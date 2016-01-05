-- |
-- Module      : Language.SequentCore.PrePrep
-- Description : CorePrep-like transformation
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- A simple global transfomation that binds every argument to every function in
-- a let-binding (or case binding if needed). CorePrep puts the final Core code
-- in this form, so decisions that depend on what the prepped code will look like
-- can use this module to perform the transform ahead of time.
--
-- In particular, CorePrep does some minor floating (similar to what the
-- simplifier does) on the let-bindings it creates, so things like free-variable
-- analysis may be sensitive to CorePrep's meddling.
--
-- Using PrePrep only makes sense for passes running at the end of the
-- Core-to-Core pipeline, since it may interfere with rule-matching and other
-- work. (There's a reason the code isn't in this form until CorePrep!) The simplifier
-- *should* undo most of this, in the sense that running PrePrep and then the
-- simplifier should be the same as just running the simplifier, but this isn't
-- guaranteed. (TODO Find out for sure.)

{-# LANGUAGE CPP #-}

module Language.SequentCore.PrePrep ( prePrepProgram ) where

import Language.SequentCore.Lint
import Language.SequentCore.OccurAnal
import Language.SequentCore.Pretty
import Language.SequentCore.Syntax
import Language.SequentCore.Syntax.Util ( uniquifyProgram )

import BasicTypes
import Coercion
import CoreSyn    ( tickishScoped )
import Demand
import FastString
import Id
import Maybes
import OrdList
import Outputable
import Pair
import Type
import UniqSupply
import Util

import Control.Applicative ((<$>))
import Control.Monad

#define ASSERT(e)      if debugIsOn && not (e) then (assertPanic __FILE__ __LINE__) else
#define ASSERT2(e,msg) if debugIsOn && not (e) then (assertPprPanic __FILE__ __LINE__ (msg)) else
#define WARN( e, msg ) (warnPprTrace (e) __FILE__ __LINE__ (msg)) $

{-
Invariants
~~~~~~~~~~
Here is the syntax of the Sequent Core produced by prePrepProgram:

    Trivial terms
       triv ::= lit  |  var  |  /\a. triv  |  /\c. triv  | compute trivc

    Trivial commands
       trivc ::= < triv | trivf ... ret >
       
    Trivial frames
       trivf ::= $ ty | $ co | |> co
    
    Frames
       frame ::= $ triv | trivf
       
    Ends
       end ::= ret
             | case as x of pat -> body ...
    
    Commands
       body ::= let(rec) x = rhs in body     -- Boxed only
              | let(rec) join j (x...) = body in body 
              | jump j(triv...)
              | < triv | frame ... end >

    Right hand sides (only place where value lambdas can occur)
       rhs ::= /\a.rhs  |  \x.rhs  |  term
    
    Terms
       term ::= triv  |  compute body
-}

type CpeTriv      = SeqCoreTerm    -- Non-terminal 'triv'
type CpeBody      = SeqCoreCommand -- Non-terminal 'body'
type CpeRhs       = SeqCoreTerm    -- Non-terminal 'rhs'
type CpeTerm      = SeqCoreTerm    -- Non-terminal 'term'
type CpeJoin      = SeqCoreJoin
type CpeBindPair  = SeqCoreBindPair

{-
%************************************************************************
%*                                                                      *
                Top level stuff
%*                                                                      *
%************************************************************************
-}

prePrepProgram :: UniqSupply -> SeqCoreProgram -> SeqCoreProgram
prePrepProgram us binds =
    initUs_ us $ do
      floats <- cpeTopBinds $ uniquifyProgram binds
      let binds' = deFloatTop floats
      return $ assertLintProgram "cpeProgram" binds' $
                 text "--- Pre-PrePrep ---" $$ pprTopLevelBinds binds

cpeTopBinds :: [SeqCoreBind] -> UniqSM Floats
-- Note [Floating out of top level bindings]
cpeTopBinds []             = return emptyFloats
cpeTopBinds (bind : binds) = do bind'  <- cpeBind TopLevel bind
                                binds' <- cpeTopBinds binds
                                return (bind' `appendFloats` binds')

{-
Note [Floating out of top level bindings]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
NB: we do need to float out of top-level bindings
Consider        x = length [True,False]
We want to get
                s1 = False : []
                s2 = True  : s1
                x  = length s2

We return a *list* of bindings, because we may start with
        x* = f (g y)
where x is demanded, in which case we want to finish with
        a = g y
        x* = f a
And then x will actually end up case-bound

%************************************************************************
%*                                                                      *
                The main code
%*                                                                      *
%************************************************************************
-}

cpeBind :: TopLevelFlag -> SeqCoreBind
        -> UniqSM Floats
cpeBind top_lvl (NonRec pair)
  = do { let bndr        = binderOfPair pair
             dmd         = idDemandInfo bndr
             is_unlifted = isUnLiftedType (idType bndr)
       ; (floats, pair1) <- cpePair top_lvl NonRecursive
                                    dmd 
                                    is_unlifted
                                    pair
       ; let new_floats = mkFloat dmd is_unlifted pair1

       ; return (floats `appendFloats` new_floats) }

cpeBind top_lvl (Rec pairs)
  = do { stuff <- mapM (cpePair top_lvl Recursive topDmd False) pairs

       ; let (floats_s, pairs1) = unzip stuff
             (term_pairs, join_pairs) = concatFloats floats_s
             -- Note that we can always move the joins inside the terms, since
             -- terms can have no free occurrences of join ids (and there's no
             -- shadowing of terms because we uniquified the whole program)
             all_term_pairs = foldrOL add_float      (filter bindsTerm pairs1) term_pairs
             all_join_pairs = foldrOL add_join_float (filter bindsJoin pairs1) join_pairs
             termFloats | null all_term_pairs = emptyFloats
                        | otherwise = unitFloat     (FloatLet     (Rec all_term_pairs))
             joinFloats | null all_join_pairs = emptyFloats
                        | otherwise = unitJoinFloat (FloatLetJoin (Rec all_join_pairs))
       ; return (termFloats `appendFloats` joinFloats) }
  where
        -- Flatten all the floats, and the currrent
        -- group into a single giant Rec
    add_float (FloatLet bind) pairs2 = flattenBind bind ++ pairs2
    add_float b               _      = pprPanic "cpeBind" (ppr b)
    
    add_join_float (FloatLetJoin bind) pairs2 = flattenBind bind ++ pairs2 

---------------
cpePair :: TopLevelFlag -> RecFlag -> Demand -> Bool
        -> SeqCoreBindPair
        -> UniqSM (Floats, CpeBindPair)
-- Used for all bindings
cpePair top_lvl is_rec dmd is_unlifted (BindTerm bndr rhs)
  = do { (floats1, rhs1) <- cpeRhsE rhs

       -- See if we are allowed to float this stuff out of the RHS
       ; (floats2, rhs2) <- float_from_rhs floats1 rhs1

       ; return (floats2, BindTerm bndr rhs2) }
  where
    is_strict_or_unlifted = (isStrictDmd dmd) || is_unlifted

    ---------------------
    float_from_rhs floats rhs
      | isEmptyFloats floats = return (emptyFloats, rhs)
      | isTopLevel top_lvl    = float_top    floats rhs
      | otherwise             = float_nested floats rhs

    ---------------------
    float_nested floats rhs
      | wantFloatNested is_rec is_strict_or_unlifted floats rhs
                  = return (floats, rhs)
      | otherwise = dont_float floats rhs

    ---------------------
    float_top floats rhs
      | allLazyTop floats
      = return (floats, rhs)

      | otherwise
      = dont_float floats rhs

    ---------------------
    dont_float floats rhs
      -- Non-empty floats, but do not want to float from rhs
      -- So wrap the rhs in the floats
      -- But: rhs1 might have lambdas, and we can't
      --      put them inside a wrapBinds
      = do { body <- rhsToBodyTermNF rhs
           ; return (emptyFloats, wrapBindsAroundBodyTerm floats body) }

cpePair _top_lvl _is_rec _dmd _is_unlifted (BindJoin bndr rhs)
  = do { rhs' <- cpeJoin rhs
       ; return (emptyFloats, BindJoin bndr rhs') }

-- ---------------------------------------------------------------------------
--              CpeRhs: produces a result satisfying CpeRhs
-- ---------------------------------------------------------------------------

cpeRhsE :: SeqCoreTerm -> UniqSM (Floats, CpeRhs)
-- If
--      e  ===>  (bs, e')
-- then
--      e = let bs in e'        (semantically, that is!)
--
-- For example
--      f (g x)   ===>   ([v = g x], f v)

cpeRhsE term@(Type {})      = return (emptyFloats, term)
cpeRhsE term@(Coercion {})  = return (emptyFloats, term)
cpeRhsE term@(Lit {})       = return (emptyFloats, term)
cpeRhsE term@(Var {})       = return (emptyFloats, term)
cpeRhsE term@(Lam {})
   = do { let (bndrs,body) = collectBinders term
        ; body' <- cpeBodyTermNF body
        ; return (emptyFloats, mkLambdas bndrs body') }
cpeRhsE      (Compute ty comm)
   = do { (floats, comm') <- cpeComm comm
        ; let comm_with_join_floats = wrapJoinBinds floats comm'
              term_floats = dropJoinsFromFloats floats
        ; return (term_floats, Compute ty comm_with_join_floats) }

-- ---------------------------------------------------------------------------
--              CpeBody: produces a result satisfying CpeBody
-- ---------------------------------------------------------------------------

cpeCommNF :: SeqCoreCommand -> UniqSM CpeBody
cpeCommNF comm
  = do { (floats, comm') <- cpeComm comm
       ; return (wrapBinds floats comm') }

---------
cpeComm :: SeqCoreCommand -> UniqSM (Floats, CpeBody)
cpeComm (Let bind comm)
  = do { new_binds <- cpeBind NotTopLevel bind
       ; (floats, comm') <- cpeComm comm
       ; return (new_binds `appendFloats` floats, comm') }
cpeComm (Jump args j)
  = cpeJump args j
cpeComm (Eval term frames end)
  = cpeEval term frames end


-- ---------------------------------------------------------------------------
--              CpeJoin: produces a result satisfying CpeJoin
-- ---------------------------------------------------------------------------

cpeJoin :: SeqCoreJoin -> UniqSM CpeJoin
cpeJoin (Join args comm)
  = do { comm' <- cpeCommNF comm
       ; return (Join args comm') }

-- ---------------------------------------------------------------------------
--              CpeTerm: produces a result satisfying CpeTerm
-- ---------------------------------------------------------------------------

cpeBodyTermNF :: SeqCoreTerm -> UniqSM CpeTerm
cpeBodyTermNF term
  = do { (floats, term') <- cpeBodyTerm term
       ; return (wrapBindsAroundBodyTerm floats term') }

--------
cpeBodyTerm :: SeqCoreTerm -> UniqSM (Floats, CpeTerm)
cpeBodyTerm term
  = do { (floats1, rhs) <- cpeRhsE term
       ; (floats2, body) <- rhsToBodyTerm rhs
       ; return (floats1 `appendFloats` floats2, body) }

--------
rhsToBodyTermNF :: CpeRhs -> UniqSM CpeTerm
rhsToBodyTermNF rhs = do { (floats,body) <- rhsToBodyTerm rhs
                     ; return (wrapBindsAroundBodyTerm floats body) }

--------
rhsToBodyTerm :: CpeRhs -> UniqSM (Floats, CpeTerm)
rhsToBodyTerm term@(Lam {})
  | all isTyVar bndrs           -- Type lambdas are ok
  = return (emptyFloats, term)
  | otherwise                   -- Some value lambdas
  = do { fn <- newVar (termType term)
       ; let float = FloatLet (NonRec (BindTerm fn term))
       ; return (unitFloat float, Var fn) }
  where
    (bndrs,_) = collectBinders term

rhsToBodyTerm term = return (emptyFloats, term)

cpeEval :: SeqCoreTerm -> [SeqCoreFrame] -> SeqCoreEnd
        -> UniqSM (Floats, CpeBody)
cpeEval term frames end
  = do { (floats, term', demands) <- doTerm term termTy
       ; (floats', term'', frames') <- doFrames term' termTy demands floats frames
       ; end' <- doEnd end -- nothing floats from a Return or Case

       ; return (floats', Eval term'' frames' end') }

  where
    termTy = termType term
    n_val_args = count isValueAppFrame frames
    
    doTerm term@(Var v) _ty
      = return (emptyFloats, term, demands)
      where
        demands = case idStrictness v of
                    StrictSig (DmdType _ demands _)
                      | not (lengthExceeds demands n_val_args) -> demands
                      | otherwise                              -> []
              -- If depth < length demands, then we have too few args to
              -- satisfy strictness  info so we have to  ignore all the
              -- strictness info, e.g. + (error "urk")
              -- Here, we can't evaluate the arg strictly, because this
              -- partial application might be seq'd
    doTerm term ty
      = do { (floats, term') <- cpeArg dmd term ty
           ; return (floats, term', []) }
      where
        dmd | n_val_args == 0, Return <- end = topDmd
            | otherwise                      = evalDmd
                                                 -- XXX Be more precise? This is
                                                 -- just what CorePrep does
    doFrames = go []
      where
        go acc term' ty demands floats frames
          = case frames of
              [] -> return (floats, term', reverse acc)
              frame@(App (Type argTy)) : frames'
                -> go (frame : acc) term' (ty `applyTy` argTy) demands floats frames'
              frame@(App (Coercion argCo)) : frames'
                -> go (frame : acc) term' (ty `applyCo` argCo) demands floats frames'
              App arg : frames'
                -> do { let (dmd1, dmds') = case demands of
                                              (dmd1:dmds') -> (dmd1, dmds')
                                              []           -> (topDmd, [])
                            (argTy, resTy) = expectJust "cpeEval:doFrames" $
                                             splitFunTy_maybe ty
                      ; (floats', arg') <- cpeArg dmd1 arg argTy
                      ; let allFloats = floats `appendFloats` floats'
                      ; go (App arg' : acc) term' resTy dmds' allFloats frames' }
              frame@(Cast co) : frames'
                -> do { let Pair _fromTy toTy = coercionKind co
                      ; go (frame : acc) term' toTy demands floats frames' }
              frame@(Tick ti) : frames'
                 | not (tickishScoped ti)
                -> go (frame : acc) term' ty demands floats frames'
                 | otherwise
                -> -- Can't float out of a scoped tick, so need to wrap what we
                   -- have in the current floats
                   do { let comm = Eval term' (reverse acc) Return
                            term'' = Compute ty (wrapBinds floats comm)
                      ; go [frame] term'' ty demands emptyFloats frames' }
    
    doEnd Return
      = return Return
    doEnd (Case bndr alts)
      = do { alts' <- forM alts $ \(Alt con bndrs rhs)
               -> do { rhs' <- cpeCommNF rhs
                     ; return (Alt con bndrs rhs') }
           ; return (Case bndr alts') }

cpeJump :: [SeqCoreArg] -> JoinId -> UniqSM (Floats, CpeBody)
cpeJump args j
  = do { (floats, args') <- unzip <$> zipWithM doArg args demands
       ; return (foldr appendFloats emptyFloats floats, Jump args' j) }
  where
    demands = case idStrictness j of
                StrictSig (DmdType _ demands _) -> demands ++ repeat topDmd
                  
    
    doArg arg dmd = cpeArg dmd arg (termType arg)

-- ---------------------------------------------------------------------------
--      CpeArg: produces a result satisfying CpeArg
-- ---------------------------------------------------------------------------

-- This is where we arrange that a non-trivial argument is let-bound
cpeArg :: Demand 
       -> SeqCoreArg -> Type -> UniqSM (Floats, CpeTriv)
cpeArg dmd arg arg_ty
  = do { (floats1, arg1) <- cpeRhsE arg     -- arg1 can be a lambda
       ; (floats2, arg2) <- if want_float floats1 arg1
                            then return (floats1, arg1)
                            else do { body1 <- rhsToBodyTermNF arg1
                                    ; return (emptyFloats, wrapBindsAroundBodyTerm floats1 body1) }
                -- Else case: arg1 might have lambdas, and we can't
                --            put them inside a wrapBinds

       ; if isTrivialTerm arg2    -- Do not let-bind a trivial argument
         then return (floats2, arg2)
         else do
       { v <- newVar arg_ty
       ; let arg_float = mkFloat dmd is_unlifted (BindTerm v arg2)
       ; return (floats2 `appendFloats` arg_float, mkVarArg v) } }
  where
    is_unlifted = isUnLiftedType arg_ty
    is_strict   = isStrictDmd dmd
    want_float  = wantFloatNested NonRecursive (is_strict || is_unlifted)
{-

Note [Floating unlifted arguments]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider    C (let v* = expensive in v)

where the "*" indicates "will be demanded".  Usually v will have been
inlined by now, but let's suppose it hasn't (see Trac #2756).  Then we
do *not* want to get

     let v* = expensive in C v

because that has different strictness.  Hence the use of 'allLazy'.
(NB: the let v* turns into a FloatCase, in mkLocalNonRec.)

%************************************************************************
%*                                                                      *
                Floats
%*                                                                      *
%************************************************************************

Note [Pin demand info on floats]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We pin demand info on floated lets so that we can see the one-shot thunks.
-}

data FloatingBind
  = FloatLet SeqCoreBind    -- Rhs of bindings are CpeRhss
                            -- They are always of lifted type;
                            -- unlifted ones are done with FloatCase
                            -- No joins! These go in FloatingJoinBind
 | FloatCase
      Id CpeBody
      Bool              -- The bool indicates "ok-for-speculation"

newtype FloatingJoinBind
  = FloatLetJoin SeqCoreBind -- INVARIANT: Must bind join(s)

-- TODO I'm keeping the logic from CorePrep that turns all unlifted bindings
-- into cases, but it's not really necessary here. But since we need to track
-- ok-for-speculation anyway, I don't think we would gain much by allowing lets
-- to be unlifted, and if the simplifier runs after this, it'll happily turn the
-- ok-for-spec cases back into lets.

data Floats = Floats OkToSpec (OrdList FloatingBind) (OrdList FloatingJoinBind)

instance Outputable FloatingBind where
  ppr (FloatLet b) = ppr b
  ppr (FloatCase b r ok) = brackets (ppr ok) <+> ppr b <+> equals <+> ppr r

instance Outputable FloatingJoinBind where
  ppr (FloatLetJoin b) = ppr b

instance Outputable Floats where
  ppr (Floats flag fs js) = ptext (sLit "Floats") <> brackets (ppr flag) <+>
                            braces (vcat (map ppr (fromOL fs) ++ map ppr (fromOL js)))

instance Outputable OkToSpec where
  ppr OkToSpec    = ptext (sLit "OkToSpec")
  ppr IfUnboxedOk = ptext (sLit "IfUnboxedOk")
  ppr NotOkToSpec = ptext (sLit "NotOkToSpec")

-- Can we float these binds out of the rhs of a let?  We cache this decision
-- to avoid having to recompute it in a non-linear way when there are
-- deeply nested lets.
data OkToSpec
   = OkToSpec           -- Lazy bindings of lifted type
   | IfUnboxedOk        -- A mixture of lazy lifted bindings and n
                        -- ok-to-speculate unlifted bindings
   | NotOkToSpec        -- Some not-ok-to-speculate unlifted bindings

mkFloat :: Demand -> Bool -> CpeBindPair -> Floats
mkFloat dmd is_unlifted (BindTerm bndr rhs)
  | use_case  = unitFloat $ FloatCase bndr (Eval rhs [] Return) (termOkForSpeculation rhs)
  | is_hnf    = unitFloat $ FloatLet (NonRec (BindTerm bndr                       rhs))
  | otherwise = unitFloat $ FloatLet (NonRec (BindTerm (setIdDemandInfo bndr dmd) rhs))
                   -- See Note [Pin demand info on floats]
  where
    is_hnf    = termIsHNF rhs
    is_strict = isStrictDmd dmd
    use_case  = is_unlifted || is_strict && not is_hnf
                -- Don't make a case for a value binding,
                -- even if it's strict.  Otherwise we get
                --      case (\x -> e) of ...!
mkFloat dmd _is_unlifted (BindJoin bndr join)
  = unitJoinFloat $ FloatLetJoin (NonRec (BindJoin (setIdDemandInfo bndr dmd) join))

emptyFloats :: Floats
emptyFloats = Floats OkToSpec nilOL nilOL

isEmptyFloats :: Floats -> Bool
isEmptyFloats (Floats _ bs js) = isNilOL bs && isNilOL js

wrapBinds :: Floats -> CpeBody -> CpeBody
wrapBinds floats@(Floats _ binds _) body
  = foldrOL mk_bind (wrapJoinBinds floats body) binds
  where
    mk_bind (FloatCase bndr rhs _) body = Eval (Compute (idType bndr) rhs) [] $
                                               Case bndr [Alt DEFAULT [] body]
    mk_bind (FloatLet bind)        body = Let bind body

wrapJoinBinds :: Floats -> CpeBody -> CpeBody
wrapJoinBinds (Floats _ _ joins) body
  = foldrOL mk_join_bind body joins
  where
    mk_join_bind (FloatLetJoin bind) body = Let bind body

wrapBindsAroundBodyTerm :: Floats -> CpeTerm -> CpeTerm
wrapBindsAroundBodyTerm floats rhs | isEmptyFloats floats = rhs
wrapBindsAroundBodyTerm floats (Compute ty rhs) = Compute ty (wrapBinds floats rhs)
wrapBindsAroundBodyTerm floats rhs = Compute (termType rhs) $
                                       wrapBinds floats (Eval rhs [] Return)

addFloat :: Floats -> FloatingBind -> Floats
addFloat (Floats ok_to_spec floats joins) new_float
  = Floats (combine ok_to_spec (check new_float)) (floats `snocOL` new_float) joins
  where
    check (FloatLet _) = OkToSpec
    check (FloatCase _ _ ok_for_spec)
        | ok_for_spec  =  IfUnboxedOk
        | otherwise    =  NotOkToSpec
        -- The ok-for-speculation flag says that it's safe to
        -- float this Case out of a let, and thereby do it more eagerly
        -- We need the top-level flag because it's never ok to float
        -- an unboxed binding to the top level

addJoinFloat :: Floats -> FloatingJoinBind -> Floats
addJoinFloat (Floats ok_to_spec floats joins) new_join
  = Floats ok_to_spec floats (joins `snocOL` new_join)

unitFloat :: FloatingBind -> Floats
unitFloat = addFloat emptyFloats

unitJoinFloat :: FloatingJoinBind -> Floats
unitJoinFloat = addJoinFloat emptyFloats

appendFloats :: Floats -> Floats -> Floats
appendFloats (Floats spec1 floats1 joins1) (Floats spec2 floats2 joins2)
  = Floats (combine spec1 spec2) (floats1 `appOL` floats2) (joins1 `appOL` joins2)

concatFloats :: [Floats] -> (OrdList FloatingBind, OrdList FloatingJoinBind)
concatFloats = foldr (\ (Floats _ bs1 js1) (bs2, js2) -> (appOL bs1 bs2, appOL js1 js2)) (nilOL, nilOL)

combine :: OkToSpec -> OkToSpec -> OkToSpec
combine NotOkToSpec _ = NotOkToSpec
combine _ NotOkToSpec = NotOkToSpec
combine IfUnboxedOk _ = IfUnboxedOk
combine _ IfUnboxedOk = IfUnboxedOk
combine _ _           = OkToSpec

dropJoinsFromFloats :: Floats -> Floats
dropJoinsFromFloats (Floats ok_to_spec floats _joins)
  = Floats ok_to_spec floats nilOL

deFloatTop :: Floats -> [SeqCoreBind]
-- For top level only; we don't expect any FloatCases or BindJoins
deFloatTop (Floats _ floats joins)
  | not (isNilOL joins)
  = panic "cpeProgram" (vcat (map ppr (fromOL joins)))
  | otherwise
  = foldrOL get [] floats
  where
    get (FloatLet b) bs = process b : bs
    get b            _  = pprPanic "cpeProgram" (ppr b)

    -- See Note [Dead code in CorePrep]
    -- Zap demand info; it makes no sense at top level, and CoreLint complains
    -- about strict top-level binders
    process (NonRec (BindTerm x e))
      = NonRec (BindTerm (zapDemandIdInfo x) (occurAnalyseTerm_NoBinderSwap e))
    process (Rec xes)
      = Rec [ BindTerm (zapDemandIdInfo x) (occurAnalyseTerm_NoBinderSwap e)
            | BindTerm x e <- xes ]
    process b
      = pprPanic "cpeProgram" (ppr b)

---------------------------------------------------------------------------
-- N.B. Here in CorePrep is a whole mess of stuff about CAFs, but happily we
-- don't need to worry about making CafInfo correct so we don't bother.

wantFloatNested :: RecFlag -> Bool -> Floats -> CpeRhs -> Bool
wantFloatNested is_rec strict_or_unlifted floats rhs
  =  isEmptyFloats floats
  || strict_or_unlifted
  || (allLazyNested is_rec floats && termIsHNF rhs)
        -- Why the test for allLazyNested?
        --      v = f (x `divInt#` y)
        -- we don't want to float the case, even if f has arity 2,
        -- because floating the case would make it evaluated too early

allLazyTop :: Floats -> Bool
allLazyTop (Floats OkToSpec _ joins) = isNilOL joins
                                         -- not "lazy" per se but can't float to top
allLazyTop _                         = False

allLazyNested :: RecFlag -> Floats -> Bool
allLazyNested _      (Floats OkToSpec    _ _) = True
allLazyNested _      (Floats NotOkToSpec _ _) = False
allLazyNested is_rec (Floats IfUnboxedOk _ _) = isNonRec is_rec

------------------------------------------------------------------------------
-- Generating new binders
-- ---------------------------------------------------------------------------

newVar :: Type -> UniqSM Id
newVar ty
 = seqType ty `seq` do
     uniq <- getUniqueM
     return (mkSysLocal (fsLit "sat") uniq ty)

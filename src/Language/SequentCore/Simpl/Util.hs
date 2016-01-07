{-# LANGUAGE LambdaCase, ViewPatterns, CPP #-}

module Language.SequentCore.Simpl.Util (
  -- * Flags
  tracing, traceTicks,

  -- * State of argument processing
  RevList, ArgInfo(..), Target(..),
  mkArgInfo, mkJumpArgInfo, mkJoinArgInfo, addFrameToArgInfo,
  addFramesToArgInfo,
  argInfoToTerm, argInfoHasTerm, argInfoSpanArgs,
  
  -- * Summary of arguments
  ArgSummary(..),
  interestingArg, nonTriv,
  
  -- * Coercion management
  castApp, combineCo, consCastMaybe, simplCoercion, simplOutCoercion, simplOutCoercion_maybe,
  
  -- * Cases
  mkCase, prepareAlts,
  
  -- * Lambda construction
  mkLam
) where

import Language.SequentCore.Arity
import Language.SequentCore.Simpl.Env
import Language.SequentCore.Simpl.Monad
import Language.SequentCore.Syntax
import Language.SequentCore.Syntax.Util
import Language.SequentCore.Util
import Language.SequentCore.WiredIn

import Coercion
import CoreMonad   ( Tick(..) )
import CoreSyn     ( CoreRule, isConLikeUnfolding, otherCons )
import Demand
import DynFlags
import FastString
import Id
import OptCoercion
import Outputable
import Pair
import Rules
import Type hiding ( substTy )
import UniqSupply
import Util        ( count, filterOut, lengthExceeds )
import Var
import VarSet

import Control.Exception ( assert )
import Control.Monad

-----------
-- Flags --
-----------

-- TODO Use proper command-line stuff.
tracing, traceTicks :: Bool

tracing    = False
traceTicks = False

-------------
-- ArgInfo --
-------------

type RevList a = [a]

data ArgInfo
  = ArgInfo {
        ai_target :: Target,     -- The term or join point
        ai_frames :: RevList OutFrame, -- ...applied to these args/casts (which are in *reverse* order)
        ai_rules  :: [CoreRule], -- Rules for this function
        ai_encl   :: Bool,       -- Flag saying whether this function
                                 -- or an enclosing one has rules (recursively)
                                 --      True => be keener to inline in all args
        ai_strs   :: [Bool],     -- Strictness of remaining value arguments
                                 --   Usually infinite, but if it is finite it guarantees
                                 --   that the function diverges after being given
                                 --   that number of args
        ai_discs  :: [Int],      -- Discounts for remaining value arguments; non-zero => be keener to inline
                                 --   Always infinite
        ai_dup    :: DupFlag
    }

data Target = TermTarget OutTerm
            | JumpTarget OutJoinId
            | JoinTarget ScopedJoin

mkArgInfo :: SimplEnv -> OutTerm
          -> [ScopedFrame] -> ScopedEnd -> ArgInfo
mkArgInfo env term@(Var fun) fs end
  | n_val_args < idArity fun            -- Note [Unsaturated functions]
  = ArgInfo { ai_target = TermTarget term, ai_frames = []
            , ai_rules = rules, ai_encl = False
            , ai_strs  = vanilla_stricts
            , ai_discs = vanilla_discounts
            , ai_dup   = NoDup }
  | otherwise
  = ArgInfo { ai_target = TermTarget term, ai_frames = []
            , ai_rules = rules
            , ai_encl  = interestingArgContext csc rules (map unScope fs) (unScope end)
            , ai_strs  = add_type_str fun_ty (idArgStrictnesses fun n_val_args)
            , ai_discs = arg_discounts
            , ai_dup   = NoDup }
  where
    fun_ty = idType fun
    n_val_args = count (isValueAppFrame . unScope) fs
    rules = getRules (getSimplRules env) fun
    (_, csc, _) = openScopedEnd end

    vanilla_discounts, arg_discounts :: [Int]
    vanilla_discounts = repeat 0
    arg_discounts = case findDef env fun of
                        BoundToTerm { def_guidance = UnfIfGoodArgs { ug_args = discounts } }
                              -> discounts ++ vanilla_discounts
                        _     -> vanilla_discounts

    vanilla_stricts :: [Bool]
    vanilla_stricts = repeat False
    
    add_type_str :: Type -> [Bool] -> [Bool]
    -- If the function arg types are strict, record that in the 'strictness bits'
    -- No need to instantiate because unboxed types (which dominate the strict
    -- types) can't instantiate type variables.
    -- add_type_str is done repeatedly (for each call); might be better
    -- once-for-all in the function
    -- But beware primops/datacons with no strictness
    add_type_str _ [] = []
    add_type_str fun_ty strs            -- Look through foralls
        | Just (_, fun_ty') <- splitForAllTy_maybe fun_ty       -- Includes coercions
        = add_type_str fun_ty' strs
    add_type_str fun_ty (str:strs)      -- Add strict-type info
        | Just (arg_ty, fun_ty') <- splitFunTy_maybe fun_ty
        = (str || isStrictType arg_ty) : add_type_str fun_ty' strs
    add_type_str _ strs
        = strs
mkArgInfo _env term _fs _end
  -- Build "arg info" for something that's not a function.
  -- Any App frame is a type error anyway, so many of these fields don't matter.
  = ArgInfo { ai_target = TermTarget term, ai_frames = []
            , ai_rules = [], ai_encl = False
            , ai_strs = repeat False -- Could be [], but applying to a non-function
                                     -- isn't bottom, it's ill-defined!
            , ai_discs = repeat 0
            , ai_dup = NoDup }

argInfoTerm :: ArgInfo -> OutTerm
argInfoTerm (ArgInfo { ai_target = TermTarget term }) = term
argInfoTerm ai = pprPanic "argInfoTerm" (ppr ai)

argInfoToTerm :: ArgInfo -> OutTerm
argInfoToTerm ai = mkComputeEval (argInfoTerm ai) (reverse (ai_frames ai))

argInfoHasTerm :: ArgInfo -> Bool
argInfoHasTerm (ArgInfo { ai_target = TermTarget {} }) = True
argInfoHasTerm _ = False

mkJumpArgInfo :: SimplEnv -> OutJoinId -> [ScopedFrame] -> ArgInfo
mkJumpArgInfo _env j fs
  = ArgInfo { ai_target = JumpTarget j, ai_frames = []
            , ai_rules = []
            , ai_encl  = False
            , ai_strs  = add_type_str j_ty (idArgStrictnesses j n_val_args)
            , ai_discs = vanilla_discounts
            , ai_dup   = NoDup }
  where
    j_ty = idType j
    n_val_args = count (isValueAppFrame . unScope) fs
    
    vanilla_discounts :: [Int]
    vanilla_discounts = repeat 0
    
    add_type_str :: Type -> [Bool] -> [Bool]
    -- Similar to add_type_str within mkArgInfo, but this is an unboxed tuple,
    -- not a function type
    add_type_str ty strs
      | Just kontTy <- isKontTy_maybe ty
      = goOuter kontTy strs
      | otherwise
      = pprPanic "mkJumpArgInfo" (ppr ty)
      where
        goOuter :: Type -> [Bool] -> [Bool]
        goOuter _ty [] = []
        goOuter ty strs
          | Just (_, bodyTy) <- isUbxExistsTy_maybe ty
          = goOuter bodyTy strs
          | isUnboxedTupleType ty
          = let (_, args) = splitTyConApp ty
            in goTupleArgs args strs
          | otherwise
          = pprPanic "mkJumpArgInfo" (ppr j_ty)
          
        goTupleArgs :: [Type] -> [Bool] -> [Bool]
        goTupleArgs [] strs = strs
        goTupleArgs _  []   = []
        goTupleArgs [ty] strs
          | Just (_, bodyTy) <- isUbxExistsTy_maybe ty
          = goOuter bodyTy strs
        goTupleArgs (ty:tys) (str:strs)
          = (str || isStrictType ty) : goTupleArgs tys strs

mkJoinArgInfo :: SimplEnv -> ScopedJoin -> [ScopedFrame] -> ArgInfo
mkJoinArgInfo _env pk _fs
  = ArgInfo { ai_target = JoinTarget pk, ai_frames = []
            , ai_rules = []
            , ai_encl  = False
            , ai_strs  = stricts ++ repeat False
            , ai_discs = repeat 0
            , ai_dup   = NoDup }
  where
    stricts = case unScope pk of Join xs _ -> map isStrictId xs

idArgStrictnesses :: Var -> Int -> [Bool]
idArgStrictnesses fun n_val_args
  = case splitStrictSig (idStrictness fun) of
      (demands, result_info)
            | not (demands `lengthExceeds` n_val_args)
            ->      -- Enough args, use the strictness given.
                    -- For bottoming functions we used to pretend that the arg
                    -- is lazy, so that we don't treat the arg as an
                    -- interesting context.  This avoids substituting
                    -- top-level bindings for (say) strings into
                    -- calls to error.  But now we are more careful about
                    -- inlining lone variables, so its ok (see SimplUtils.analyseCont)
               if isBotRes result_info then
                    map isStrictDmd demands         -- Finite => result is bottom
               else
                    map isStrictDmd demands ++ vanilla_stricts
           | otherwise
           -> warnPprTrace (not (isJoinId fun && idArity fun == 0)) __FILE__ __LINE__
                             -- Don't warn about nullary join points, which we see as
                             -- arity 0 but translate to Core as arity 1
                           (text "More demands than arity" <+> pprBndr LetBind fun <+> ppr (idArity fun)
                            <+> ppr n_val_args <+> ppr demands )
               vanilla_stricts
  where
    vanilla_stricts = repeat False

addFrameToArgInfo :: ArgInfo -> OutFrame -> ArgInfo
addFrameToArgInfo ai f
  = case f of
      App arg | not (isTypeArg arg) ->
        let strs' | null (ai_strs ai)
                  = warnPprTrace True __FILE__ __LINE__
                      (text "Adding frame to bottoming ArgInfo" $$ ppr f $$ ppr ai)
                      []
                  | otherwise
                  = tail (ai_strs ai)
        in ai' { ai_strs  = strs'
               , ai_discs = tail (ai_discs ai) } -- ai_discs is infinite
      _ -> ai'
  where
    ai' = ai { ai_frames = f : ai_frames ai }

addFramesToArgInfo :: ArgInfo -> [OutFrame] -> ArgInfo
addFramesToArgInfo ai fs
  = foldl addFrameToArgInfo ai fs

argInfoSpanArgs :: ArgInfo -> ([OutArg], [OutFrame])
argInfoSpanArgs (ArgInfo { ai_frames = rev_fs })
  = mapWhileJust (\case { App arg -> Just arg; _ -> Nothing }) (reverse rev_fs)

----------------
-- ArgSummary --
----------------

data ArgSummary = TrivArg        -- Nothing interesting
                | NonTrivArg        -- Arg has structure
                | ValueArg        -- Arg is a con-app or PAP
                            -- ..or con-like. Note [Conlike is interesting]

interestingArg :: SeqCoreTerm -> ArgSummary
-- See Note [Interesting arguments]
interestingArg e = goT e 0
  where
    -- n is # value args to which the expression is applied
    goT (Lit {}) _              = ValueArg
    goT (Var v)  n
       | isConLikeId v     = ValueArg        -- Experimenting with 'conlike' rather that
                                             --    data constructors here
       | idArity v > n           = ValueArg  -- Catches (eg) primops with arity but no unfolding
       | n > 0                   = NonTrivArg        -- Saturated or unknown call
       | conlike_unfolding = ValueArg        -- n==0; look for an interesting unfolding
                                      -- See Note [Conlike is interesting]
       | otherwise         = TrivArg        -- n==0, no useful unfolding
       where
         conlike_unfolding = isConLikeUnfolding (idUnfolding v)

    goT (Type _)         _ = TrivArg
    goT (Coercion _)     _ = TrivArg
    goT (Lam v e)           n 
       | isTyVar v     = goT e n
       | n>0           = goT e (n-1)
       | otherwise     = ValueArg
    goT (Compute _ c) n    = goC c n
    
    goC (Let _ c)     n = case goC c n of { ValueArg -> ValueArg; _ -> NonTrivArg }
    goC (Eval v fs e) n = maybe NonTrivArg (goT v) (goK (fs, e) n)
    goC (Jump vs j)   _ = goT (Var j) (length (filter isValueArg vs))
    
    goK (_, Case {}) _ = Nothing
    goK (fs, Return) n = Just $ length (filter realArg fs) + n
    
    realArg (App (Type _))     = False
    realArg (App (Coercion _)) = False
    realArg (App _)            = True
    realArg _                  = False

nonTriv ::  ArgSummary -> Bool
nonTriv TrivArg = False
nonTriv _       = True

-- See comments on SimplUtils.interestingArgContext
interestingArgContext :: ControlScope -> [CoreRule] -> [InFrame] -> InEnd -> Bool
interestingArgContext csc rules fs end
  | not (null rules)  = True
  | Case {} <- end    = False
  | any isAppFrame fs = False
  | RuleArgCtxt <- getContext csc
                      = True
  | otherwise         = False

instance Outputable ArgSummary where
  ppr TrivArg    = ptext (sLit "TrivArg")
  ppr NonTrivArg = ptext (sLit "NonTrivArg")
  ppr ValueArg   = ptext (sLit "ValueArg")

-----------------------
-- Coercion handling --
-----------------------

simplCoercion :: SimplEnv -> DataScope -> InCoercion -> OutCoercion
simplCoercion env dsc co = optCoercion (getCvSubst env dsc) co

simplOutCoercion :: OutCoercion -> OutCoercion
simplOutCoercion co = optCoercion emptyCvSubst co

simplOutCoercion_maybe :: OutCoercion -> Maybe OutCoercion
simplOutCoercion_maybe co | fromTy `eqType` toTy = Nothing
                          | otherwise            = Just $ simplOutCoercion co
  where
    Pair fromTy toTy = coercionKind co

combineCo :: Maybe OutCoercion -> OutCoercion -> Maybe OutCoercion
combineCo co_m co'
  -- Skip reflexive coercion
  | fromTy2 `eqType` toTy2
  = co_m
  | otherwise
  = case co_m of
      Nothing -> Just co'
      Just co | let Pair fromTy1 toTy1 = coercionKind co
              , fromTy2 `eqType` toTy1
              , fromTy1 `eqType` toTy2
              -- Skip back-and-forth
              -> Nothing
              | otherwise
              -> Just (mkTransCo co co')
  where Pair fromTy2 toTy2 = coercionKind co'

-- | Given a simplified argument and a coercion for a function taking that
-- argument, return the argument with the coercion applied and the coercion for
-- the return type. Note that this creates a redex in the output, but a very
-- boring one that we'll sort out next iteration. (If there's no next iteration,
-- the cast will be erased anyway.)
--
-- Returns Nothing if the original coercion is not a function or forall type.
-- (For instance, it could be IO a, which coerces to a function type but isn't
-- one.)
castApp :: SeqCoreArg -> Coercion -> Maybe (SeqCoreArg, Coercion)
  -- Either InArg  -> InCoercion  -> Maybe (InArg,  InCoercion)
  --     or OutArg -> OutCoercion -> Maybe (OutArg, OutCoercion)
castApp _                co | let Pair fromTy _toTy = coercionKind co
                            , Nothing <- splitFunTy_maybe fromTy
                            , Nothing <- splitForAllTy_maybe fromTy
                            = Nothing
castApp arg@(Type argTy) co = Just (arg, mkInstCo co argTy)
castApp arg              co = Just (mkCast arg (mkSymCo argCo), bodyCo)
  where [argCo, bodyCo]     = decomposeCo 2 co

consCastMaybe :: Maybe InCoercion -> [InFrame] -> [InFrame]
Nothing `consCastMaybe` fs = fs
Just co `consCastMaybe` fs = Cast co : fs

-----------
-- Cases --
-----------

{-
%************************************************************************
%*                                                                      *
                prepareAlts
%*                                                                      *
%************************************************************************

(Most of the prepareAlts and mkCase sections are C&P'd from SimplUtils in GHC,
including these comments.)

prepareAlts tries these things:

1.  Eliminate alternatives that cannot match, including the
    DEFAULT alternative.

2.  If the DEFAULT alternative can match only one possible constructor,
    then make that constructor explicit.
    e.g.
        case e of x { DEFAULT -> rhs }
     ===>
        case e of x { (a,b) -> rhs }
    where the type is a single constructor type.  This gives better code
    when rhs also scrutinises x or e.

3. Returns a list of the constructors that cannot holds in the
   DEFAULT alternative (if there is one)

Here "cannot match" includes knowledge from GADTs

It's a good idea to do this stuff before simplifying the alternatives, to
avoid simplifying alternatives we know can't happen, and to come up with
the list of constructors that are handled, to put into the IdInfo of the
case binder, for use when simplifying the alternatives.

Eliminating the default alternative in (1) isn't so obvious, but it can
happen:

data Colour = Red | Green | Blue

f x = case x of
        Red -> ..
        Green -> ..
        DEFAULT -> h x

h y = case y of
        Blue -> ..
        DEFAULT -> [ case y of ... ]

If we inline h into f, the default case of the inlined h can't happen.
If we don't notice this, we may end up filtering out *all* the cases
of the inner case y, which give us nowhere to go!
-}

prepareAlts :: OutTerm -> OutId -> [InAlt] -> SimplM ([AltCon], [InAlt])
-- The returned alternatives can be empty, none are possible
prepareAlts scrut case_bndr' alts
           -- Case binder is needed just for its type. Note that as an
           --   OutId, it has maximum information; this is important.
           --   Test simpl013 is an example
  = do { us <- getUniquesM
       ; let (imposs_deflt_cons, refined_deflt, alts') 
                = filterAlts us (varType case_bndr') imposs_cons alts
       ; when refined_deflt $ tick (FillInCaseDefault case_bndr')
 
       ; alts'' <- combineIdenticalAlts case_bndr' alts'
       ; return (imposs_deflt_cons, alts'') }
  where
    imposs_cons = case scrut of
                    Var v -> otherCons (idUnfolding v)
                    _     -> []

{-
Note [Combine identical alternatives]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 If several alternatives are identical, merge them into
 a single DEFAULT alternative.  I've occasionally seen this
 making a big difference:

     case e of               =====>     case e of
       C _ -> f x                         D v -> ....v....
       D v -> ....v....                   DEFAULT -> f x
       DEFAULT -> f x

The point is that we merge common RHSs, at least for the DEFAULT case.
[One could do something more elaborate but I've never seen it needed.]
To avoid an expensive test, we just merge branches equal to the *first*
alternative; this picks up the common cases
     a) all branches equal
     b) some branches equal to the DEFAULT (which occurs first)

The case where Combine Identical Alternatives transformation showed up
was like this (base/Foreign/C/Err/Error.lhs):

        x | p `is` 1 -> e1
          | p `is` 2 -> e2
        ...etc...

where @is@ was something like

        p `is` n = p /= (-1) && p == n

This gave rise to a horrible sequence of cases

        case p of
          (-1) -> $j p
          1    -> e1
          DEFAULT -> $j p

and similarly in cascade for all the join points!

NB: it's important that all this is done in [InAlt], *before* we work
on the alternatives themselves, because Simpify.simplAlt may zap the
occurrence info on the binders in the alternatives, which in turn
defeats combineIdenticalAlts (see Trac #7360).
-}

combineIdenticalAlts :: OutId -> [InAlt] -> SimplM [InAlt]
-- See Note [Combine identical alternatives]
combineIdenticalAlts case_bndr (Alt _con1 bndrs1 rhs1 : con_alts)
  | all isDeadBinder bndrs1                     -- Remember the default
  , length filtered_alts < length con_alts      -- alternative comes first
  = do  { tick (AltMerge case_bndr)
        ; return (Alt DEFAULT [] rhs1 : filtered_alts) }
  where
    filtered_alts = filterOut identical_to_alt1 con_alts
    identical_to_alt1 (Alt _con bndrs rhs) = all isDeadBinder bndrs && rhs `cheapEqCommand` rhs1

combineIdenticalAlts _ alts = return alts

{-
%************************************************************************
%*                                                                      *
                mkCase
%*                                                                      *
%************************************************************************

mkCase tries these things

1.  Merge Nested Cases

       case e of b {             ==>   case e of b {
         p1 -> rhs1                      p1 -> rhs1
         ...                             ...
         pm -> rhsm                      pm -> rhsm
         _  -> case b of b' {            pn -> let b'=b in rhsn
                     pn -> rhsn          ...
                     ...                 po -> let b'=b in rhso
                     po -> rhso          _  -> let b'=b in rhsd
                     _  -> rhsd
       }

    which merges two cases in one case when -- the default alternative of
    the outer case scrutises the same variable as the outer case. This
    transformation is called Case Merging.  It avoids that the same
    variable is scrutinised multiple times.

2.  Eliminate Identity Case

        case e of               ===> e
                True  -> True;
                False -> False

    and similar friends.
-}


mkCase, mkCase1, mkCase2
   :: DynFlags
   -> OutId -> [OutAlt]               -- Alternatives in standard (increasing) order
   -> SimplM OutKont

--------------------------------------------------
--      1. Merge Nested Cases
--------------------------------------------------

mkCase dflags outer_bndr (Alt DEFAULT _ deflt_rhs : outer_alts)
  | gopt Opt_CaseMerge dflags
  , Eval (Var inner_scrut_var) [] (Case inner_bndr inner_alts) <- deflt_rhs
  , inner_scrut_var == outer_bndr
  = do  { tick (CaseMerge outer_bndr)

        ; let wrap_alt (Alt con args rhs) = assert( outer_bndr `notElem` args ) $
                                            Alt con args (wrap_rhs rhs)
                -- Simplifier's no-shadowing invariant should ensure
                -- that outer_bndr is not shadowed by the inner patterns
              wrap_rhs rhs = Let (NonRec (BindTerm inner_bndr (Var outer_bndr))) rhs
                -- The let is OK even for unboxed binders,

              wrapped_alts | isDeadBinder inner_bndr = inner_alts
                           | otherwise               = map wrap_alt inner_alts

              merged_alts = mergeAlts outer_alts wrapped_alts
                -- NB: mergeAlts gives priority to the left
                --      case x of
                --        A -> e1
                --        DEFAULT -> case x of
                --                      A -> e2
                --                      B -> e3
                -- When we merge, we must ensure that e1 takes
                -- precedence over e2 as the value for A!

        ; mkCase1 dflags outer_bndr merged_alts
        }
        -- Warning: don't call mkCase recursively!
        -- Firstly, there's no point, because inner alts have already had
        -- mkCase applied to them, so they won't have a case in their default
        -- Secondly, if you do, you get an infinite loop, because the bindCaseBndr
        -- in munge_rhs may put a case into the DEFAULT branch!

mkCase dflags bndr alts = mkCase1 dflags bndr alts

--------------------------------------------------
--      2. Eliminate Identity Case
--------------------------------------------------

mkCase1 _dflags case_bndr alts@(Alt _ _ rhs1 : _)      -- Identity case
  | all identity_alt alts
  = do { tick (CaseIdentity case_bndr)
       ; return (re_cast rhs1) }
  where
    identity_alt (Alt con args rhs) = check_eq rhs con args

    check_eq (Eval term fs Return) con args = check_eq_cut term fs con args
    check_eq _                     _   _    = False
    
    check_eq_cut term fs con args | Just fs' <- match term con = all okCast fs'
                                  | otherwise                  = False
      where
        match (Lit lit) (LitAlt lit')      = guard (lit == lit') >>
                                             Just fs
        match (Var v)   _ | v == case_bndr = Just fs
        match (Var v)   (DataAlt dc)       = guard (rhs' `cheapEqCommand` consComm) >>
                                             Just fs'
          where
            consComm = mkConstructionCommand dc arg_tys (map mkVarArg args)
            (appFrames, fs') = span isAppFrame fs
            rhs' = Eval (Var v) appFrames Return
        match _         _                  = Nothing
        
        okCast (Cast co) = not (any (`elemVarSet` tyCoVarsOfCo co) args)
        okCast _         = False

    arg_tys = tyConAppArgs (idType case_bndr)

        -- Note [RHS casts]
        -- ~~~~~~~~~~~~~~~~
        -- We've seen this:
        --      case e of x { _ -> < x | cast c; ret > }
        -- And we definitely want to eliminate this case, to give
        --      < e | cast c; ret >
        -- So we throw away the cast from the RHS, and reconstruct
        -- it at the other end.  All the RHS casts must be the same
        -- if (all identity_alt alts) holds.
        --
        -- Don't worry about nested casts, because the simplifier combines them

    re_cast (Eval _ fs Return) = (dropWhile isAppFrame fs, Return)
    re_cast other              = pprPanic "mkCase1" (ppr other)

mkCase1 dflags bndr alts = mkCase2 dflags bndr alts

--------------------------------------------------
--      Catch-all
--------------------------------------------------
mkCase2 _dflags bndr alts
  = return ([], Case bndr alts)

{-
Note [Dead binders]
~~~~~~~~~~~~~~~~~~~~
Note that dead-ness is maintained by the simplifier, so that it is
accurate after simplification as well as before.


Note [Cascading case merge]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Case merging should cascade in one sweep, because it
happens bottom-up

      case e of a {
        DEFAULT -> case a of b
                      DEFAULT -> case b of c {
                                     DEFAULT -> e
                                     A -> ea
                      B -> eb
        C -> ec
==>
      case e of a {
        DEFAULT -> case a of b
                      DEFAULT -> let c = b in e
                      A -> let c = b in ea
                      B -> eb
        C -> ec
==>
      case e of a {
        DEFAULT -> let b = a in let c = b in e
        A -> let b = a in let c = b in ea
        B -> let b = a in eb
        C -> ec


However here's a tricky case that we still don't catch, and I don't
see how to catch it in one pass:

  case x of c1 { I# a1 ->
  case a1 of c2 ->
    0 -> ...
    DEFAULT -> case x of c3 { I# a2 ->
               case a2 of ...

After occurrence analysis (and its binder-swap) we get this

  case x of c1 { I# a1 ->
  let x = c1 in         -- Binder-swap addition
  case a1 of c2 ->
    0 -> ...
    DEFAULT -> case x of c3 { I# a2 ->
               case a2 of ...

When we simplify the inner case x, we'll see that
x=c1=I# a1.  So we'll bind a2 to a1, and get

  case x of c1 { I# a1 ->
  case a1 of c2 ->
    0 -> ...
    DEFAULT -> case a1 of ...

This is corect, but we can't do a case merge in this sweep
because c2 /= a1.  Reason: the binding c1=I# a1 went inwards
without getting changed to c1=I# c2.

I don't think this is worth fixing, even if I knew how. It'll
all come out in the next pass anyway.
-}

-------------------------
-- Lambda construction --
-------------------------

-- (from SimplUtils)
mkLam :: Bool -> [OutBndr] -> OutTerm -> SimplM OutTerm
-- mkLam tries two things
--      a) eta reduction, if that gives a trivial expression
--      b) eta expansion [only if there are some value lambdas]

mkLam _inRhsCtxt [] body
  = return body
mkLam inRhsCtxt bndrs body
  = do  { dflags <- getDynFlags
        ; mkLam' dflags bndrs body }
  where
    mkLam' :: DynFlags -> [OutBndr] -> OutTerm -> SimplM OutTerm
    mkLam' dflags bndrs (splitCastTerm -> (body, Just co))
      | not (any bad bndrs)
        -- Note [Casts and lambdas]
      = do { lam <- mkLam' dflags bndrs body
           ; return (mkCast lam (mkPiCos Representational bndrs co)) }
      where
        co_vars  = tyCoVarsOfCo co
        bad bndr = isCoVar bndr && bndr `elemVarSet` co_vars

    mkLam' dflags bndrs body@(Lam {})
      = mkLam' dflags (bndrs ++ bndrs1) body1
      where
        (bndrs1, body1) = collectBinders body

    mkLam' dflags bndrs body
      | gopt Opt_DoEtaReduction dflags
      , Just etad_lam <- tryEtaReduce bndrs body
      = do { tick (EtaReduction (head bndrs))
           ; return etad_lam }

      | not inRhsCtxt   -- See Note [Eta-expanding lambdas]
      , gopt Opt_DoLambdaEtaExpansion dflags
      , any isId bndrs
      , let body_arity = termEtaExpandArity dflags body
      , body_arity > 0
      = do { tick (EtaExpansion (head bndrs))
           ; return (mkLambdas bndrs (etaExpand body_arity body)) }

      | otherwise
      = return (mkLambdas bndrs body)

---------------
-- Instances --
---------------

instance Outputable ArgInfo where
  ppr (ArgInfo { ai_target = target
               , ai_frames = fs
               , ai_strs = strs
               , ai_dup = dup })
    = hang (text "ArgInfo") 8 $ vcat [ targetLabel <+> ppr target
                                     , text "Prev. frames:" <+> pprWithCommas ppr fs
                                     , ppWhen (dup == OkToDup) $ text "Okay to duplicate"
                                     , strictDoc ]
    where
      targetLabel = case target of TermTarget {}  -> text "Term:"
                                   JumpTarget {}  -> text "Join id:"
                                   JoinTarget {}  -> text "Inlining join:"
      strictDoc = case strs of []        -> text "Expression is bottom"
                               True  : _ -> text "Next argument strict"
                               False : _ -> text "Next argument lazy"

instance Outputable Target where
  ppr (TermTarget term) = ppr term
  ppr (JumpTarget j)    = ppr j
  ppr (JoinTarget join) = ppr join

{-
%
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section{SetLevels}

                ***************************
                        Overview
                ***************************

1. We attach binding levels to Core bindings, in preparation for floating
   outwards (@FloatOut@).

2. We also let-ify many expressions (notably case scrutinees), so they
   will have a fighting chance of being floated sensible.

3. We clone the binders of any floatable let-binding, so that when it is
   floated out it will be unique.  (This used to be done by the simplifier
   but the latter now only ensures that there's no shadowing; indeed, even 
   that may not be true.)

   NOTE: this can't be done using the uniqAway idea, because the variable
         must be unique in the whole program, not just its current scope,
         because two variables in different scopes may float out to the
         same top level place

   NOTE: Very tiresomely, we must apply this substitution to
         the rules stored inside a variable too.

   We do *not* clone top-level bindings, because some of them must not change,
   but we *do* clone bindings that are heading for the top level

4. In the expression
        case x of wild { p -> ...wild... }
   we substitute x for wild in the RHS of the case alternatives:
        case x of wild { p -> ...x... }
   This means that a sub-expression involving x is not "trapped" inside the RHS.
   And it's not inconvenient because we already have a substitution.

  Note that this is EXACTLY BACKWARDS from the what the simplifier does.
  The simplifier tries to get rid of occurrences of x, in favour of wild,
  in the hope that there will only be one remaining occurrence of x, namely
  the scrutinee of the case, and we can inline it.  

-}
{-# LANGUAGE CPP, ViewPatterns, BangPatterns #-}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://ghc.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module Language.SequentCore.FloatOut.SetLevels (
        setLevels, 

        Level(..), tOP_LEVEL,
        Levelled, LevelledBndr,
        FloatSpec(..), floatSpecLevel,

        incMinorLvl, ltMajLvl, ltLvl, isTopLvl
    ) where

import Language.SequentCore.ANF
import Language.SequentCore.FloatOut.Flags as FloatFlags
import Language.SequentCore.FloatOut.Summary
import Language.SequentCore.FVs
import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import CoreSyn          ( Unfolding,
                          isStableSource, isStableUnfolding,
                          neverUnfoldGuidance )
import qualified CoreSyn as Core
import CoreUnfold       ( mkInlinableUnfolding )
import CoreMonad        ( FloatOutSwitches(..) )
import CoreArity        ( exprBotStrictness_maybe )
import Coercion         ( coercionKind, isCoVar )
import CoreSubst        ( Subst, emptySubst, substBndrs, substRecBndrs,
                          extendIdSubst, extendSubstWithVar, cloneBndrs,
                          cloneRecIdBndrs, substTy, substCo, substVarSet )
import MkCore           ( sortQuantVars )

import SMRep            ( WordOff )
import StgCmmArgRep     ( ArgRep(P), argRepSizeW, toArgRep )
import StgCmmLayout     ( mkVirtHeapOffsets )
import StgCmmClosure    ( idPrimRep, addIdReps )

import Id
import IdInfo
import MkId             ( voidArgId, voidPrimId )
import Var
import VarSet
import VarEnv
import Literal          ( literalType, litIsTrivial )
import Demand           ( StrictSig, isBottomingSig )
import Name             ( getOccName, mkSystemVarName )
import OccName          ( occNameString )
import Type             ( isUnLiftedType, Type, mkPiTypes, tyVarsOfType )
import BasicTypes       ( Arity, RecFlag(..),
                          inlinePragmaActivation, isNeverActive, isRec )
import UniqSupply
import Util
import Maybes
import Outputable
import FastString
import Pair
import DynFlags
import StaticFlags

import Control.Applicative ( (<$>), (<*>) )
import Control.Monad       ( zipWithM )
import Data.List           ( mapAccumL )

#define ASSERT(e)      if debugIsOn && not (e) then (assertPanic __FILE__ __LINE__) else
#define ASSERT2(e,msg) if debugIsOn && not (e) then (assertPprPanic __FILE__ __LINE__ (msg)) else
#define WARN( e, msg ) (warnPprTrace (e) __FILE__ __LINE__ (msg)) $
#define MASSERT(e)     ASSERT(e) return ()

{-
%************************************************************************
%*                                                                      *
\subsection{Level numbers}
%*                                                                      *
%************************************************************************
-}

type Levelled expr = Tagged expr FloatSpec
type LevelledBndr = TaggedBndr FloatSpec

type MajorLevel = Int
data Level = Level MajorLevel  -- Major level: number of enclosing value lambdas
                   Int  -- Minor level: number of big-lambda and/or case 
                        -- expressions between here and the nearest 
                        -- enclosing value lambda

data FloatSpec 
  = FloatMe Level       -- Float to just inside the binding 
                        --    tagged with this level
  | StayPut Level       -- Stay where it is; binding is
                        --     tagged with tihs level

floatSpecLevel :: FloatSpec -> Level
floatSpecLevel (FloatMe l) = l
floatSpecLevel (StayPut l) = l

{-
The {\em level number} on a (type-)lambda-bound variable is the
nesting depth of the (type-)lambda which binds it.  The outermost lambda
has level 1, so (Level 0 0) means that the variable is bound outside any lambda.

On an expression, it's the maximum level number of its free
(type-)variables.  On a let(rec)-bound variable, it's the level of its
RHS.  On a case-bound variable, it's the number of enclosing lambdas.

Top-level variables: level~0.  Those bound on the RHS of a top-level
definition but ``before'' a lambda; e.g., the \tr{x} in (levels shown
as ``subscripts'')...
\begin{verbatim}
a_0 = let  b_? = ...  in
           x_1 = ... b ... in ...
\end{verbatim}

The main function @lvlTerm@ carries a ``context level'' (@ctxt_lvl@).
That's meant to be the level number of the enclosing binder in the
final (floated) program.  If the level number of a sub-expression is
less than that of the context, then it might be worth let-binding the
sub-expression so that it will indeed float.  

If you can float to level @Level 0 0@ worth doing so because then your
allocation becomes static instead of dynamic.  We always start with
context @Level 0 0@.  


Note [FloatOut inside INLINE]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
@InlineCtxt@ very similar to @Level 0 0@, but is used for one purpose:
to say "don't float anything out of here".  That's exactly what we
want for the body of an INLINE, where we don't want to float anything
out at all.  See notes with lvlMFE below.

But, check this out:

-- At one time I tried the effect of not float anything out of an InlineMe,
-- but it sometimes works badly.  For example, consider PrelArr.done.  It
-- has the form         __inline (\d. e)
-- where e doesn't mention d.  If we float this to 
--      __inline (let x = e in \d. x)
-- things are bad.  The inliner doesn't even inline it because it doesn't look
-- like a head-normal form.  So it seems a lesser evil to let things float.
-- In SetLevels we do set the context to (Level 0 0) when we get to an InlineMe
-- which discourages floating out.

So the conclusion is: don't do any floating at all inside an InlineMe.
(In the above example, don't float the {x=e} out of the \d.)

One particular case is that of workers: we don't want to float the
call to the worker outside the wrapper, otherwise the worker might get
inlined into the floated expression, and an importing module won't see
the worker at all.
-}

instance Outputable FloatSpec where
  ppr (FloatMe l) = char 'F' <> ppr l
  ppr (StayPut l) = ppr l

tOP_LEVEL :: Level
tOP_LEVEL   = Level 0 0

incMajorLvl :: Level -> Level
incMajorLvl (Level major _) = Level (major + 1) 0

incMinorLvl :: Level -> Level
incMinorLvl (Level major minor) = Level major (minor+1)

maxLvl :: Level -> Level -> Level
maxLvl l1@(Level maj1 min1) l2@(Level maj2 min2)
  | (maj1 > maj2) || (maj1 == maj2 && min1 > min2) = l1
  | otherwise                                      = l2

ltLvl :: Level -> Level -> Bool
ltLvl (Level maj1 min1) (Level maj2 min2)
  = (maj1 < maj2) || (maj1 == maj2 && min1 < min2)

ltMajLvl :: Level -> Level -> Bool
    -- Tells if one level belongs to a difft *lambda* level to another
ltMajLvl (Level maj1 _) (Level maj2 _) = maj1 < maj2

isTopLvl :: Level -> Bool
isTopLvl (Level 0 0) = True
isTopLvl _           = False

instance Outputable Level where
  ppr (Level maj min) = hcat [ char '<', int maj, char ',', int min, char '>' ]

instance Eq Level where
  (Level maj1 min1) == (Level maj2 min2) = maj1 == maj2 && min1 == min2


{-
%************************************************************************
%*                                                                      *
\subsection{Main level-setting code}
%*                                                                      *
%************************************************************************
-}

setLevels :: DynFlags
          -> FloatFlags
          -> FloatOutSwitches
          -> Maybe FinalPassSwitches
          -> SeqCoreProgram
          -> UniqSupply
          -> [Levelled Bind]
setLevels dflags fflags float_lams fps binds us
  = initLvl us2 (do_them init_env summarized_binds)
  where
    init_env = initialEnv dflags fflags float_lams fps

    prepped_binds | is_final_pass = prepareForFinalPass dflags fflags us1 binds
                  | otherwise     = binds

    is_final_pass = isJust fps
    
    summarized_binds = summarizeProgram prepped_binds

    (us1, us2) = splitUniqSupply us

    do_them :: LevelEnv -> [SummBind] -> LvlM [Levelled Bind]
    do_them _ [] = return []
    do_them env (b:bs)
      = do { (lvld_bind, env') <- lvlTopBind env b
           ; lvld_binds <- do_them env' bs
           ; return (lvld_bind : lvld_binds) }

lvlTopBind :: LevelEnv -> SummBind -> LvlM (Levelled Bind, LevelEnv)
lvlTopBind env (_, AnnNonRec (_, AnnBindTerm bndr rhs))
  = do { rhs' <- lvlTerm env rhs
       ; let (env', [bndr']) = substAndLvlBndrs NonRecursive env tOP_LEVEL [bndr]
       ; return (NonRec (BindTerm bndr' rhs'), env') }

lvlTopBind env (_, AnnRec pairs)
  | all (bindsTerm . deAnnotateBindPair) pairs
  = do let (bndrs,rhss) = unzip [(bndr, rhs) | (_, AnnBindTerm bndr rhs) <- pairs]
           (env', bndrs') = substAndLvlBndrs Recursive env tOP_LEVEL bndrs
       rhss' <- mapM (lvlTerm env') rhss
       return (Rec (zipWith BindTerm bndrs' rhss'), env')

lvlTopBind _ bind
  = pprPanic "lvlTopBind" (text "Top binding includes join point:" $$
                           ppr (deAnnotateBind bind))

-- Prepare for late lambda-lift pass. See Note [LLL prep]
prepareForFinalPass :: DynFlags -> FloatFlags -> UniqSupply
                    -> SeqCoreProgram
                    -> SeqCoreProgram
prepareForFinalPass dflags fflags us binds
  = binds_final
  where
    binds1 | fgopt FloatFlags.Opt_LLF_Stabilize fflags
           = stabilizeExposedUnfoldings dflags binds
           | otherwise = binds
    
    binds_final = anfProgram us binds1
    
stabilizeExposedUnfoldings :: DynFlags -> SeqCoreProgram -> SeqCoreProgram
stabilizeExposedUnfoldings dflags binds
  = map stabBind binds
  where
    stabBind (NonRec pair) = NonRec (stabPair pair)
    stabBind (Rec pairs)   = Rec (map stabPair pairs)
    
    stabPair pair
      | isTyVar bndr = pair
      | willExposeUnfolding expose_all bndr
      , isUnstableUnfolding (realIdUnfolding bndr)
      = pair `setPairBinder` bndr'
      | otherwise = pair
      where
        bndr     = binderOfPair pair
        bndr'    = bndr `setIdUnfolding` mkInlinableUnfolding dflags rhs_expr
        rhs_expr = case pair of
                     BindTerm _ term -> termToCoreExpr term
                     BindJoin {}     -> pprPanic "stabilizeExposedUnfoldings"
                                          (text "Join at top level:" <+> ppr bndr)
    
    expose_all = gopt Opt_ExposeAllUnfoldings dflags  

isUnstableUnfolding :: Unfolding -> Bool
isUnstableUnfolding (Core.CoreUnfolding { Core.uf_src = src }) = not (isStableSource src)
isUnstableUnfolding _                                          = False

-- A trimmed copy of TidyPgm.addExternal
willExposeUnfolding :: Bool -> Id -> Bool
willExposeUnfolding expose_all id = show_unfold
  where
    idinfo         = idInfo id
    show_unfold    = show_unfolding (unfoldingInfo idinfo)
    never_active   = isNeverActive (inlinePragmaActivation (inlinePragInfo idinfo))
    loop_breaker   = isStrongLoopBreaker (occInfo idinfo)
    bottoming_fn   = isBottomingSig (strictnessInfo idinfo)

        -- Stuff to do with the Id's unfolding
        -- We leave the unfolding there even if there is a worker
        -- In GHCi the unfolding is used by importers

    show_unfolding (Core.CoreUnfolding { Core.uf_src = src, Core.uf_guidance = guidance })
       =  expose_all         -- 'expose_all' says to expose all
                             -- unfoldings willy-nilly

       || isStableSource src     -- Always expose things whose
                                 -- source is an inline rule

       || not (bottoming_fn      -- No need to inline bottom functions
           || never_active       -- Or ones that say not to
           || loop_breaker       -- Or that are loop breakers
           || neverUnfoldGuidance guidance)
    show_unfolding (Core.DFunUnfolding {}) = True
    show_unfolding _                       = False

{-
Note [LLL prep]
~~~~~~~~~~~~~~~

The late lambda-lift pass is "late" for two reasons:

1. Compared to other Core-to-Core passes, late lambda-lifting is *low-level*: It
   is sensitive to fine details such as what variables end up stored in which
   closures and which function calls will be fast calls to known code. Thus it
   is crucial that we see the Core code as it will appear just before
   translation to STG - in other words, as CorePrep will transform it.

2. Late lambda-lifting is also *radical*: The operations that LLL performs
   interact very badly with GHC's other optimizations, especially rewrite rules.
   Putting LLL last keeps us from stepping on other passes' toes.

For these same reasons, we want to do a bit of preprocessing before we begin:

1. We run the code through an ANF transform that performs a subset of the same
   changes that CorePrep will make, namely those that will affect LLL decisions.

2. Putting LLL last in the pipeline keeps it from mucking with *this* module's
   optimizations, but of course many unfoldings get exposed to other modules as
   well. Thus, before we begin, we stabilize any unfoldings that may get exposed
   so that they're "frozen" in their pre-LLL state.

%************************************************************************
%*                                                                      *
\subsection{Setting expression levels}
%*                                                                      *
%************************************************************************
-}

lvlTerm :: LevelEnv             -- Context
        -> SummTerm             -- Input expression
        -> LvlM (Levelled Term) -- Result expression

{-
The @ctxt_lvl@ is, roughly, the level of the innermost enclosing
binder.  Here's an example

        v = \x -> ...\y -> let r = case (..x..) of
                                        ..x..
                           in ..

When looking at the rhs of @r@, @ctxt_lvl@ will be 1 because that's
the level of @r@, even though it's inside a level-2 @\y@.  It's
important that @ctxt_lvl@ is 1 and not 2 in @r@'s rhs, because we
don't want @lvlTerm@ to turn the scrutinee of the @case@ into an MFE
--- because it isn't a *maximal* free expression.

If there were another lambda in @r@'s rhs, it would get level-2 as well.
-}

lvlTerm env (_, AnnType ty)     = return (Type (substTy (le_subst env) ty))
lvlTerm env (_, AnnCoercion co) = return (Coercion (substCo (le_subst env) co))
lvlTerm env (_, AnnVar v)       = return (lookupVar env v)
lvlTerm _   (_, AnnLit lit)     = return (Lit lit)

-- We don't split adjacent lambdas.  That is, given
--      \x y -> (x+1,y)
-- we don't float to give
--      \x -> let v = x+y in \y -> (v,y)
-- Why not?  Because partial applications are fairly rare, and splitting
-- lambdas makes them more expensive.

lvlTerm env expr@(_, AnnLam {})
  = do { new_body <- lvlMFE True new_env body
       ; return (mkLambdas new_bndrs new_body) }
  where
    (bndrs, body)        = collectAnnBinders expr
    (env1, bndrs1)       = substBndrsSL NonRecursive env bndrs
    (new_env, new_bndrs) = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1
        -- At one time we called a special verion of collectBinders,
        -- which ignored coercions, because we don't want to split
        -- a lambda like this (\x -> coerce t (\s -> ...))
        -- This used to happen quite a bit in state-transformer programs,
        -- but not nearly so much now non-recursive newtypes are transparent.
        -- [See SetLevels rev 1.50 for a version with this approach.]

lvlTerm env (_, AnnCompute ty comm)
  = Compute ty' <$> lvlComm env ty' comm
  where
    ty' = substTy (le_subst env) ty

lvlComm :: LevelEnv
        -> Type -- Return type, substituted
        -> SummCommand
        -> LvlM (Levelled Command)
lvlComm env ty (_, AnnLet bind body)
  = do { (bind', new_env) <- lvlBind env ty bind
       ; body' <- lvlComm new_env ty body
       ; return (Let bind' body') }

lvlComm env ty (_, AnnEval term frames end)
  = do
    (term', frames') <- case term of
      -- float out partial applications.  This is very beneficial
      -- in some cases (-7% runtime -4% alloc over nofib -O2).
      -- In order to float a PAP, there must be a function at the
      -- head of the application, and the application must be
      -- over-saturated with respect to the function's arity.
      (fvs_term, AnnVar f) | floatPAPs env &&
                             arity > 0 && arity < n_val_args ->
        do
        let fvs_largs = unionSumms (map getSummary largs)
            fvs_pap   = fvs_term `unionSumm` fvs_largs
            ty_pap    = foldl frameType
                              (termType (deAnnotateTerm term))
                              (map deAnnotateFrame lapps)
            pap       = (fvs_pap `unionSumm` summFromFVs (tyVarsOfType ty_pap),
                          AnnCompute ty_pap $
                            (fvs_pap, AnnEval term lapps (emptySumm, AnnReturn)))
        pap'         <- lvlMFE False env pap
        otherFrames' <- mapM (lvlFrame env) otherFrames
        return (pap', otherFrames')
        where
          (lapps, otherFrames) = takeApps arity frames
          largs = map (\(_, AnnApp arg) -> arg) lapps
          n_val_args = count (isValueArg . deAnnotateTerm) largs
          arity = idArity f
          
          takeApps = go []
            where
              go acc 0 fs = done acc fs
              go acc n (f@(_, AnnApp (_, AnnType _)) : fs) = go (f : acc) n     fs
              go acc n (f@(_, AnnApp _             ) : fs) = go (f : acc) (n-1) fs
              go acc _ fs = done acc fs
              
              done acc fs = (reverse acc, fs)
          
      _ ->
        (,) <$> lvlTerm env term <*> mapM (lvlFrame env) frames
    end' <- case end of
      (_, AnnReturn)         -> return Return
      (_, AnnCase bndr alts) -> lvlCase env summ term' frames' bndr ty alts
        where
          summ = getSummary term `unionSumm` unionSumms (map getSummary frames)
    return $ Eval term' frames' end'

lvlComm env _ (_, AnnJump args j)
  | decontifying env j
  = do
    args' <- if null args then return [Var voidPrimId]
                          else mapM (lvlMFE False env) args
    return $ Eval (lookupVar env j) (map App args') Return
  | otherwise
  = do
    args' <- mapM (lvlMFE False env) args
    case lookupVar env j of
      Var j' -> return $ Jump args' j' 
      other  -> pprPanic "lvlComm" (text "Abstracted join??" <+> ppr other) 

lvlFrame :: LevelEnv
         -> SummFrame
         -> LvlM (Levelled Frame)
lvlFrame env (_, AnnApp arg) = App <$> lvlMFE False env arg
                                 -- TODO Use strictness of argument?
                                 -- Is there a reason that GHC doesn't?
lvlFrame env (_, AnnCast co) = return $ Cast (substCo (le_subst env) co)
lvlFrame _   (_, AnnTick ti) = return $ Tick ti

lvlJoin :: LevelEnv -> Type -> SummJoin -> LvlM (Levelled Join)
lvlJoin env retTy (_, AnnJoin bndrs body)
  = do { new_body <- lvlMFEComm True new_env retTy body
       ; return (Join new_bndrs new_body) }
  where
    (env1, bndrs1)       = substBndrsSL NonRecursive env bndrs
    (new_env, new_bndrs) = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1

lvlRhs :: LevelEnv -> Type -> LevelledBndr -> SummBindPair
       -> LvlM (Levelled BindPair)
lvlRhs env _retTy new_bndr (_, AnnBindTerm _bndr term)
  = do { new_term <- lvlTerm env term
       ; return (BindTerm new_bndr new_term) }
lvlRhs env retTy new_bndr (_, AnnBindJoin _bndr join)
  = do { new_join <- lvlJoin env retTy join
       ; return (BindJoin new_bndr new_join) }

decontifyBindPair :: LevelEnv -> Type -> SummBindPair -> (LevelEnv, SummBindPair)
decontifyBindPair env _ pair@(_, AnnBindTerm {}) = (env, pair)
decontifyBindPair env retTy (summ, AnnBindJoin bndr join)
  = (env', (summ, AnnBindTerm bndr' term))
    where
      (env', bndr') = decontifyBndr env retTy bndr
      term = case join of
               (joinSumm, AnnJoin bndrs comm) ->
                 foldr lam (joinSumm, AnnCompute retTy comm) bndrs'
                 where
                   bndrs' | null bndrs = [TB voidArgId NoSummary]
                          | otherwise  = bndrs

                   lam x body = (joinSumm, AnnLam x body)

decontifyBindPairs :: LevelEnv -> Type -> [SummBindPair] -> (LevelEnv, [SummBindPair])
decontifyBindPairs env ty = mapAccumL (flip decontifyBindPair ty) env

-------------------------------------------
lvlCase :: LevelEnv             -- Level of in-scope names/tyvars
        -> Summary              -- Summary of input scrutinee
        -> Levelled Term        -- Processed scrutinee (term part)
        -> [Levelled Frame]     -- Processed scrutinee (frame part)
        -> SummBndr             -- Case binder2
        -> Type                 -- Return type
        -> [SummAlt]            -- Input alternatives
        -> LvlM (Levelled End)  -- Result expression
lvlCase env scrut_fvs scrut_term scrut_frames case_bndr ty alts
  | [(_, AnnAlt con@(DataAlt {}) bs body)] <- alts
  , termOkForSpeculation scrut'   -- See Note [Check the output scrutinee for okForSpec]
  , not (isTopLvl dest_lvl)       -- Can't have top-level cases
  =     -- See Note [Floating cases]
        -- Always float the case if possible
        -- Unlike lets we don't insist that it escapes a value lambda
    do { (rhs_env, (case_bndr':bs')) <- cloneVars NonRecursive env dest_lvl (case_bndr:bs)
                   -- We don't need to use extendCaseBndrLvlEnv here
                   -- because we are floating the case outwards so
                   -- no need to do the binder-swap thing
       ; body' <- lvlMFEComm True rhs_env ty body
       ; let alt' = Alt con [TB b (StayPut dest_lvl) | b <- bs'] body'
       ; return (Case (TB case_bndr' (FloatMe dest_lvl)) [alt']) }

  | otherwise     -- Stays put
  = do { let (alts_env1, [case_bndr']) = substAndLvlBndrs NonRecursive env incd_lvl [case_bndr]
             alts_env = extendCaseBndrEnv alts_env1 case_bndr scrut'
       ; alts' <- mapM (lvl_alt alts_env) alts
       ; return (Case case_bndr' alts') }
  where
      scrut' = mkComputeEval scrut_term scrut_frames
      incd_lvl = incMinorLvl (le_ctxt_lvl env)
      dest_lvl = maxFvLevel (const True) env scrut_fvs
              -- Don't abstact over type variables, hence const True

      lvl_alt alts_env (_, AnnAlt con bs rhs)
        = do { rhs' <- lvlMFEComm True new_env ty rhs
             ; return $ Alt con bs' rhs' }
        where
          (new_env, bs') = substAndLvlBndrs NonRecursive alts_env incd_lvl bs

{-
Note [Floating cases]
~~~~~~~~~~~~~~~~~~~~~
Consider this:
  data T a = MkT !a
  f :: T Int -> blah
  f x vs = case x of { MkT y -> 
             let f vs = ...(case y of I# w -> e)...f..
             in f vs
Here we can float the (case y ...) out , because y is sure
to be evaluated, to give
  f x vs = case x of { MkT y -> 
           caes y of I# w ->
             let f vs = ...(e)...f..
             in f vs

That saves unboxing it every time round the loop.  It's important in
some DPH stuff where we really want to avoid that repeated unboxing in
the inner loop.

Things to note
 * We can't float a case to top level
 * It's worth doing this float even if we don't float
   the case outside a value lambda.  Example
     case x of { 
       MkT y -> (case y of I# w2 -> ..., case y of I# w2 -> ...)
   If we floated the cases out we could eliminate one of them.
 * We only do this with a single-alternative case

Note [Check the output scrutinee for okForSpec]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider this:
  case x of y { 
    A -> ....(case y of alts)....
  }
Because of the binder-swap, the inner case will get substituted to
(case x of ..).  So when testing whether the scrutinee is
okForSpecuation we must be careful to test the *result* scrutinee ('x'
in this case), not the *input* one 'y'.  The latter *is* ok for
speculation here, but the former is not -- and indeed we can't float
the inner case out, at least not unless x is also evaluated at its
binding site.

That's why we apply exprOkForSpeculation to scrut' and not to scrut.
-}

lvlMFE ::  Bool                 -- True <=> strict context [body of case or let]
        -> LevelEnv             -- Level of in-scope names/tyvars
        -> SummTerm             -- input expression
        -> LvlM (Levelled Term) -- Result expression
-- lvlMFE is just like lvlTerm, except that it might let-bind
-- the expression, so that it can itself be floated.

lvlMFE _ env (_, AnnType ty)
  = return (Type (substTy (le_subst env) ty))

lvlMFE _ env (_, AnnCoercion co)
  = return (Coercion (substCo (le_subst env) co))

lvlMFE _ env (_, AnnVar id)
  = return (lookupVar env id)

lvlMFE strict_ctxt env (fvs, AnnLit lit)
  = ASSERT(isEmptyVarEnv (sm_varsUsed fvs))
    lvlMFE strict_ctxt env (summ, AnnCompute (literalType lit)
                                    (summ, AnnEval (summ, AnnLit lit) []
                                                   (summ, AnnReturn)))
  where
    summ = emptySumm

lvlMFE strict_ctxt env term@(_, AnnLam {})
  = lvlMFE strict_ctxt env (summ, AnnCompute ty
                                    (summ, AnnEval term []
                                                  (emptySumm, AnnReturn)))
                              -- N.B.: Since we compute the type from the term,
                              -- there can't be any variables free in the type
                              -- but not the term, so we reuse fvs as is
  where
    summ = getSummary term
    ty   = termType (deAnnotateTerm term)

lvlMFE strict_ctxt env (_, AnnCompute ty comm)
  = mkCompute ty <$> lvlMFEComm strict_ctxt env ty comm

lvlMFEComm :: Bool                    -- True <=> strict context [body of case or let]
           -> LevelEnv                -- Level of in-scope names/tyvars
           -> Type                    -- Return type
           -> SummCommand             -- input expression
           -> LvlM (Levelled Command) -- Result expression
lvlMFEComm strict_ctxt env ty ann_comm
  | isUnLiftedType ty
        -- Can't let-bind it; see Note [Unlifted MFEs]
        -- This includes coercions, which we don't want to float anyway
        -- NB: no need to substitute cos isUnLiftedType doesn't change
  || isFinalPass env
  || never_float ann_comm
  || notWorthFloating ann_comm abs_vars
  || not float_me
  =     -- Don't float it out
    lvlComm env ty ann_comm

  | otherwise   -- Float it out!
  = do { let (ann_comm', extraFrames) = trimForFloating env ann_comm
       ; let ty' | (co : _) <- [co | Cast co <- extraFrames]
                 , let (Pair fromTy _toTy) = coercionKind co
                 = fromTy -- We trimmed off a cast, so adjust the type
                 | otherwise
                 = ty
       ; rhs <- lvlFloatRhsComm abs_vars dest_lvl env ty' ann_comm'
       ; var <- newLvlVar rhs is_bot
       ; return (Let (NonRec (BindTerm (TB var (FloatMe dest_lvl)) rhs))
                     (Eval (Var var)
                           (map (App . mkVarArg) abs_vars ++ extraFrames)
                           Return)) }
  where
    comm     = deAnnotateCommand ann_comm
    is_bot   = commandIsBottom comm      -- Note [Bottoming floats]
    dest_lvl = destLevel env summ is_bot
    summ     = getSummary ann_comm
    fvs      = fvsFromSumm summ `unionVarSet` tyVarsOfType ty
                 -- ty may not be the final type of the binding if we trim off
                 -- coercions (see ty' above). But if there are coercions to
                 -- trim off, the command must specify its own return type, so
                 -- the free vars of ty and ty' are in summ to begin with. In
                 -- short, we can get away with using ty to calculate the tyvars
                 -- to abstract.
    abs_vars = abstractVars dest_lvl env fvs
    
        -- Eliminate a few kinds of commands from consideration
    never_float (_, AnnEval _ _ (_, AnnCase {})) | strict_ctxt
                                                 = True -- Don't share cases from strict contexts
    never_float (_, AnnJump _ j)                 | is_still_join j
                                                 = True -- Note [Don't float jumps]
    never_float (summ, _)                        | has_join summ
                                                 = True -- Contains a jump
    never_float _                                = False
    
    has_join summ = any is_still_join (varSetElems (fvsFromSumm summ))
    is_still_join j = isJoinId j && not (j `elemVarSet` le_decont env)
                         -- It's a join point and we're not decontifying it

        -- A decision to float entails let-binding this thing, and we only do 
        -- that if we'll escape a value lambda, or will go to the top level.
    float_me = dest_lvl `ltMajLvl` (le_ctxt_lvl env)    -- Escapes a value lambda
                -- OLD CODE: not (exprIsCheap expr) || isTopLvl dest_lvl
                --           see Note [Escaping a value lambda]

            || (isTopLvl dest_lvl       -- Only float if we are going to the top level
                && floatConsts env      --   and the floatConsts flag is on
                && not strict_ctxt)     -- Don't float from a strict context    
          -- We are keen to float something to the top level, even if it does not
          -- escape a lambda, because then it needs no allocation.  But it's controlled
          -- by a flag, because doing this too early loses opportunities for RULES
          -- which (needless to say) are important in some nofib programs
          -- (gcd is an example).
          --
          -- Beware:
          --    concat = /\ a -> foldr ..a.. (++) []
          -- was getting turned into
          --    lvl    = /\ a -> foldr ..a.. (++) []
          --    concat = /\ a -> lvl a
          -- which is pretty stupid.  Hence the strict_ctxt test
          -- 
          -- Also a strict contxt includes uboxed values, and they
          -- can't be bound at top level

trimForFloating :: LevelEnv
                -> SummCommand
                -> (SummCommand, [Levelled Frame])
-- No point in floating out an expression wrapped in a coercion or note
-- If we do we'll transform  lvl = e |> co 
--                       to  lvl' = e; lvl = lvl' |> co
-- and then inline lvl.  Better just to float out the payload.
trimForFloating env (fvs, AnnEval term frames end@(_, AnnReturn))
  = ((fvs, AnnEval term frames' end), extraFrames)
  where
    (frames', extraFrames) = go (reverse frames) []
    go ((_, AnnTick ti) : fs) acc = go fs (Tick ti : acc)
    go ((_, AnnCast co) : fs) acc = go fs (Cast (substCo (le_subst env) co) : acc)
    go fs                     acc = (reverse fs, acc)
trimForFloating _ comm = (comm, [])
-- XXX The trimForFloating function is a bit awkward; it's meant to replace the
-- AnnTick and AnnCast cases of lvlMFE in GHC. A refactor might clarify things.

{-
lvlMFE strict_ctxt env (_, AnnTick e@t)
  = do { e' <- lvlMFE strict_ctxt env e
       ; return (Tick t e') }

lvlMFE strict_ctxt env (_, AnnCast e@(_, co))
  = do  { e' <- lvlMFE strict_ctxt env e
        ; return (Cast e' (substCo (le_subst env) co)) }

-}

{-
Note [Floating joins]
~~~~~~~~~~~~~~~~~~~~~

Join points can't float past the enclosing Compute unless we decontify them.
This is not great because join points are faster to call (it's essentially a
goto), but it's disastrous if the join point becomes a closure, increasing
allocation for no benefit. *But* if we're floating the join point to top level,
there's no issue with allocation and we may make something unfoldably small. So
we float but *only* all the way, in both regular floating and LLL.

Nullary join points are a different matter; if we decontify one, it'll become a
thunk *but* we may increase sharing.
-}

{-
Note [Don't float jumps]
~~~~~~~~~~~~~~~~~~~~~~~~

In order to float a jump, we'd need to abstract it as a join point. But then we
never float join points unless they can go to top level, and a jump can never go
to top level because of course it refers to the join point.

In STG terms, this suggests that it never helps to float an invocation of a
let-no-escape function. TODO Is this true?
-}

{-
Note [Unlifted MFEs]
~~~~~~~~~~~~~~~~~~~~
We don't float unlifted MFEs, which potentially loses big opportunites.
For example:
        \x -> f (h y)
where h :: Int -> Int# is expensive. We'd like to float the (h y) outside
the \x, but we don't because it's unboxed.  Possible solution: box it.

Note [Bottoming floats]
~~~~~~~~~~~~~~~~~~~~~~~
If we see
        f = \x. g (error "urk")
we'd like to float the call to error, to get
        lvl = error "urk"
        f = \x. g lvl
Furthermore, we want to float a bottoming expression even if it has free
variables:
        f = \x. g (let v = h x in error ("urk" ++ v))
Then we'd like to abstact over 'x' can float the whole arg of g:
        lvl = \x. let v = h x in error ("urk" ++ v)
        f = \x. g (lvl x)
See Maessen's paper 1999 "Bottom extraction: factoring error handling out
of functional programs" (unpublished I think).

When we do this, we set the strictness and arity of the new bottoming
Id, *immediately*, for two reasons:

  * To prevent the abstracted thing being immediately inlined back in again
    via preInlineUnconditionally.  The latter has a test for bottoming Ids
    to stop inlining them, so we'd better make sure it *is* a bottoming Id!

  * So that it's properly exposed as such in the interface file, even if
    this is all happening after strictness analysis.

Note [Bottoming floats: eta expansion] c.f Note [Bottoming floats]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Tiresomely, though, the simplifier has an invariant that the manifest
arity of the RHS should be the same as the arity; but we can't call
etaExpand during SetLevels because it works over a decorated form of
CoreExpr.  So we do the eta expansion later, in FloatOut.

Note [Case MFEs]
~~~~~~~~~~~~~~~~
We don't float a case expression as an MFE from a strict context.  Why not?
Because in doing so we share a tiny bit of computation (the switch) but
in exchange we build a thunk, which is bad.  This case reduces allocation 
by 7% in spectral/puzzle (a rather strange benchmark) and 1.2% in real/fem.
Doesn't change any other allocation at all.
-}

annotateBotStr :: Id -> Maybe (Arity, StrictSig) -> Id
-- See Note [Bottoming floats] for why we want to add
-- bottoming information right now
annotateBotStr id Nothing            = id
annotateBotStr id (Just (arity, sig)) = id `setIdArity` arity
                                           `setIdStrictness` sig

notWorthFloating :: SummCommand -> [Var] -> Bool
-- Returns True if the expression would be replaced by
-- something bigger than it is now.  For example:
--   abs_vars = tvars only:  return True if e is trivial, 
--                           but False for anything bigger
--   abs_vars = [x] (an Id): return True for trivial, or an application (f x)
--                           but False for (f x x)
--
-- One big goal is that floating should be idempotent.  Eg if
-- we replace e with (lvl79 x y) and then run FloatOut again, don't want
-- to replace (lvl79 x y) with (lvl83 x y)!
notWorthFloating (_, AnnEval term frames (_, AnnReturn)) abs_vars
  = go term frames (count isId abs_vars)
  where
    go (_, AnnVar {})  [] n = n >= 0
    go (_, AnnLit lit) [] n = ASSERT( n==0 )
                              litIsTrivial lit   -- Note [Floating literals]
    
    go e ((_, AnnCast _):fs)  n = go e fs n
    go e ((_, AnnApp arg):fs) n
       | (_, AnnType {}) <- arg = go e fs n
       | (_, AnnCoercion {}) <- arg = go e fs n
       | n==0                   = False
       | is_triv arg            = go e fs (n-1)
       | otherwise              = False
    go _ _ _                    = False

    is_triv (_, AnnLit {})                        = True  -- Treat all literal args as trivial
    is_triv (_, AnnVar {})                        = True  -- (ie not worth floating)
    is_triv (_, AnnCompute _ c)                   = is_triv_comm c
    is_triv _                                     = False
    
    is_triv_comm (_, AnnEval e fs (_, AnnReturn)) = is_triv e && all is_triv_frame fs
    is_triv_comm _                                = False
    
    is_triv_frame (_, AnnCast _)                  = True
    is_triv_frame (_, AnnApp (_, AnnType {}))     = True
    is_triv_frame (_, AnnApp (_, AnnCoercion {})) = True
    is_triv_frame _                               = False     
notWorthFloating _ _
  = False

{-
Note [Floating literals]
~~~~~~~~~~~~~~~~~~~~~~~~
It's important to float Integer literals, so that they get shared,
rather than being allocated every time round the loop.
Hence the litIsTrivial.

We'd *like* to share MachStr literal strings too, mainly so we could
CSE them, but alas can't do so directly because they are unlifted.


Note [Escaping a value lambda]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We want to float even cheap expressions out of value lambdas, 
because that saves allocation.  Consider
        f = \x.  .. (\y.e) ...
Then we'd like to avoid allocating the (\y.e) every time we call f,
(assuming e does not mention x).   

An example where this really makes a difference is simplrun009.

Another reason it's good is because it makes SpecContr fire on functions.
Consider
        f = \x. ....(f (\y.e))....
After floating we get
        lvl = \y.e
        f = \x. ....(f lvl)...
and that is much easier for SpecConstr to generate a robust specialisation for.

The OLD CODE (given where this Note is referred to) prevents floating
of the example above, so I just don't understand the old code.  I
don't understand the old comment either (which appears below).  I
measured the effect on nofib of changing OLD CODE to 'True', and got
zeros everywhere, but a 4% win for 'puzzle'.  Very small 0.5% loss for
'cse'; turns out to be because our arity analysis isn't good enough
yet (mentioned in Simon-nofib-notes).

OLD comment was:
         Even if it escapes a value lambda, we only
         float if it's not cheap (unless it'll get all the
         way to the top).  I've seen cases where we
         float dozens of tiny free expressions, which cost
         more to allocate than to evaluate.
         NB: exprIsCheap is also true of bottom expressions, which
             is good; we don't want to share them

        It's only Really Bad to float a cheap expression out of a
        strict context, because that builds a thunk that otherwise
        would never be built.  So another alternative would be to
        add 
                || (strict_ctxt && not (exprIsBottom expr))
        to the condition above. We should really try this out.


%************************************************************************
%*                                                                      *
\subsection{Bindings}
%*                                                                      *
%************************************************************************

The binding stuff works for top level too.
-}

lvlBind :: LevelEnv
        -> Type -- Current return type
        -> SummBind
        -> LvlM (Levelled Bind, LevelEnv)
lvlBind env ty bind@(_, AnnNonRec pair)
  | not (isTyVar var)    -- Don't do anything for TyVar binders
                         --   (simplifier gets rid of them pronto)
  , not (isCoVar var)    -- Difficult to fix up CoVar occurrences (see extendPolyLvlEnv)
                         -- so we will ignore this case for now
  , Just (dest_lvl, abs_vars) <- decideBindFloat env ty bind
  , not (isTopLvl dest_lvl && is_term && isUnLiftedType (idType var))
          -- We can't float an unlifted binding to top level, so we don't 
          -- float it at all.  It's a bit brutal, but unlifted bindings 
          -- aren't expensive either
  , isTopLvl dest_lvl || is_term || (is_nullary_join && fgopt Opt_FloatNullaryJoins (le_fflags env))
          -- Never float a non-nullary join point except to top level
          -- Note [Floating joins]
  = do_float dest_lvl abs_vars
  | otherwise
  = no_float
  where
    bndr = binderOfAnnPair pair
    is_term = bindsTerm (deAnnotateBindPair pair)
    is_nullary_join | (_, AnnBindJoin _ (_, AnnJoin [] _)) <- pair = True
                    | otherwise                                    = False
    TB var _ = bndr
    no_float
      = do { let bind_lvl              = incMinorLvl (le_ctxt_lvl env)
                 (new_env, [new_bndr]) = substAndLvlBndrs NonRecursive env bind_lvl [bndr]
           ; new_pair <- lvlRhs env ty new_bndr pair
           ; return (NonRec new_pair, new_env) }

    do_float dest_lvl abs_vars
      | null abs_vars
      = do {  -- No type abstraction; clone existing binder
             let (env1, pair1) = decontifyBindPair env ty pair
                 bndr1 = binderOfAnnPair pair1
           ; (new_env, [cloned_bndr]) <- cloneVars NonRecursive env1 dest_lvl [bndr1]
           ; let new_bndr = TB cloned_bndr (FloatMe dest_lvl)
           ; new_pair <- lvlRhs (setCtxtLvl new_env dest_lvl) ty new_bndr pair1
           ; return (NonRec new_pair, new_env) }

      | otherwise
      = do {  -- Yes, type abstraction; create a new binder, extend substitution, etc
             MASSERT(all (not . isJoinId) abs_vars)
           ; let (env1, pair1) = decontifyBindPair env ty pair
                 bndr1 = binderOfAnnPair pair1
           ; (new_env, [fresh_bndr]) <- newPolyBndrs dest_lvl env1 abs_vars [bndr1]
           ; let new_bndr = TB fresh_bndr (FloatMe dest_lvl)
           ; new_pair <- lvlFloatRhs abs_vars dest_lvl env ty new_bndr pair1
           ; return (NonRec new_pair, new_env) }

lvlBind env ty bind@(_, AnnRec pairs)
  | Just (dest_lvl, abs_vars) <- decideBindFloat env ty bind
  , isTopLvl dest_lvl || not (any binds_unfloatable_join pairs)
          -- Never float a non-nullary join point except to top level
          -- Note [Floating joins]
  = do_float dest_lvl abs_vars
  | otherwise
  = no_float
  where
    bndrs = map binderOfAnnPair pairs
    binds_unfloatable_join (_, AnnBindJoin _ (_, AnnJoin xs _))
      = not (fgopt Opt_FloatNullaryJoins (le_fflags env) && null xs)
    binds_unfloatable_join _
      = False

    no_float
      = do { let bind_lvl = incMinorLvl (le_ctxt_lvl env)
                 (new_env, new_bndrs) = substAndLvlBndrs Recursive env bind_lvl bndrs
           ; new_pairs <- zipWithM (lvlRhs new_env ty) new_bndrs pairs
           ; return (Rec new_pairs, new_env) }

    do_float dest_lvl abs_vars
      | null abs_vars
      = do { let (env1, pairs1) = decontifyBindPairs env ty pairs
                 bndrs1 = map binderOfAnnPair pairs1
           ; (new_env, cloned_bndrs) <- cloneVars Recursive env1 dest_lvl bndrs1
           ; let new_bndrs = [TB b (FloatMe dest_lvl) | b <- cloned_bndrs]
           ; new_pairs <- zipWithM (lvlRhs (setCtxtLvl new_env dest_lvl) ty) new_bndrs pairs1
           ; return (Rec new_pairs, new_env) }

      | otherwise  -- Non-null abs_vars
      = do { MASSERT(all (not . isJoinId) abs_vars)
           ; let (env1, pairs1) = decontifyBindPairs env ty pairs
                 bndrs1 = map binderOfAnnPair pairs1
           ; (new_env, fresh_bndrs) <- newPolyBndrs dest_lvl env1 abs_vars bndrs1
           ; let new_bndrs = [TB b (FloatMe dest_lvl) | b <- fresh_bndrs]
           ; new_pairs <- zipWithM (lvlFloatRhs abs_vars dest_lvl new_env ty) new_bndrs pairs1
           ; return (Rec new_pairs, new_env) }

decideBindFloat :: LevelEnv -> Type -> SummBind
                -> Maybe (Level, [Var]) -- Nothing <=> do not float
                                        -- Just (lvl, vars) <=>
                                        --   float to lvl, abstracting vars
decideBindFloat env retTy bind
  | Just fps <- le_finalPass env
  = late_float fps
  | otherwise
  = early_float
  where
    early_float | profitable = Just (dest_lvl, abs_vars)
                | otherwise  = Nothing
      where
        profitable = (dest_lvl `ltMajLvl` le_ctxt_lvl env) -- Escapes a value lambda
                  || isTopLvl dest_lvl -- Going all the way to the top level

        dest_lvl = destLevel env bind_summ is_bot
        abs_vars = abstractVars dest_lvl env fvs

    late_float fps | all_funs -- only lift functions
                   , Nothing <- why_not = Just (tOP_LEVEL, abs_vars)
                   | otherwise          = Nothing
      where
        abs_vars    = abstractVars tOP_LEVEL env fvs
        abs_ids_set = expandFloatedIds env fvs
        abs_ids     = varSetElems abs_ids_set

        why_not = decideLateLambdaFloat env fps is_rec all_one_shot abs_ids_set
                                        time_info space_info ids extra_sdoc

        time_info  = wouldIncreaseRuntime    env abs_ids (sm_varsUsed bind_summ)
        space_info = wouldIncreaseAllocation env abs_ids_set pairs scope_summ

        pairs = flattenAnnBind bind
        ids = identifiers $ map binderOfAnnPair pairs
        is_rec = case bind of (_, AnnRec {})    -> Recursive
                              (_, AnnNonRec {}) -> NonRecursive
        all_one_shot = all is_one_shot_binding pairs
        all_funs     = all is_function_binding pairs
        scope_summ = case bsumm of BindSummary summ -> summ
                                   NoSummary        -> emptySumm
          where (TB _ bsumm) = head (bindersOfAnnBind bind)

        -- for -ddump-late-float with -dppr-debug
        extra_sdoc = text "scope_summ:" <+> ppr scope_summ
                  $$ text "le_env env:" <+> ppr (le_env env)
                  $$ text "abs_vars:"   <+> ppr abs_vars

    bind_summ = getSummary bind
    fvs_summ = fvsFromSumm bind_summ
    fvs | any (bindsJoin . deAnnotateBindPair) (flattenAnnBind bind)
        = fvs_summ `unionVarSet` tyVarsOfType retTy
            -- Will need to abstract over free vars in return type
        | otherwise
        = fvs_summ
    is_bot | (_, AnnNonRec (_, AnnBindTerm _ term)) <- bind = termIsBottom (deAnnotateTerm term)
           | (_, AnnNonRec (_, AnnBindJoin _ (_, AnnJoin _ comm))) <- bind
                                                            = commandIsBottom (deAnnotateCommand comm)
           | otherwise                                      = False
    is_one_shot_binding (_, AnnBindTerm _ term)
      = case collectAnnBinders term of
          (bndrs, _) -> all isOneShotBndr (identifiers bndrs)
    is_one_shot_binding (_, AnnBindJoin _ join)
      = case join of
          (_, AnnJoin bndrs _) -> all isOneShotBndr (identifiers bndrs)
    is_function_binding (_, AnnBindTerm _ term)
      = isFunction term
    is_function_binding (_, AnnBindJoin _ _)
      = True

decideLateLambdaFloat :: LevelEnv -> FinalPassSwitches
                      -> RecFlag
                      -> Bool   -- ^ One-shot lambda?
                      -> IdSet  -- ^ Ids being abstracted over
                      -> IdSet  -- ^ Ids of functions made slow by abstraction
                      -> [(Bool, WordOff, WordOff, WordOff)] -- ^ Bad space info
                      -> [Id]  -- ^ Ids of binding under consideration
                      -> SDoc  -- ^ Debug info for -ddump-late-float
                      -> Maybe VarSet -- Nothing <=> float to tOP_LEVEL
                                      -- Just xs <=> don't float, blaming xs
decideLateLambdaFloat env fps is_rec all_one_shot abs_ids_set
                      slowdowns space_info ids extra_sdoc
  | fps_trace fps, pprTrace msg msg_sdoc False = {- trace clause -} undefined
  | floating = Nothing
  | is_bad_space = Just emptyVarSet
  | otherwise    = Just slowdowns
  where
    floating = not $ is_bad_time || is_bad_space

    msg = '\n' :
          (if floating then "late-float" else "late-no-float") ++
          (if isRec is_rec then "(rec " ++ show (length ids) ++ ")" else "") ++
          (if floating && is_bad_space then "(SAT)" else "") -- FIXME Dead code

    is_bad_time = not (isEmptyVarSet slowdowns)

    is_bad_space | fps_oneShot fps && all_one_shot = False
                 | otherwise                       = any bad_space_info space_info

    bad_space_info (creates_PAPs, clo_size, cg, cgil)
      | not (fps_createPAPs fps)
      , creates_PAPs
      = True

      -- If the closure is NOT under a lambda, then we get a discount
      -- for no longer allocating these bindings' closures, since
      -- these bindings would be allocated at least as many times as
      -- the closure.

      | Just limit <- fps_cloGrowth fps
      , cg - clo_size > limit * wORDS_PTR
      = True

      -- If the closure is under a lambda, we do NOT discount for not
      -- allocating these bindings' closures, since the closure could
      -- be allocated many more times than these bindings are.

      | Just limit <- fps_cloGrowthInLam fps
      , cgil > limit * wORDS_PTR
      = True

      | otherwise = False

    msg_sdoc = vcat (zipWith space ids space_info) where
      abs_ids = varSetElems abs_ids_set
      space v (badPAP, closureSize, cg, cgil) = vcat
       [ ppr v
       , text "size:" <+> ppr closureSize
       , text "abs_ids:" <+> ppr (length abs_ids) <+> ppr abs_ids
       , text "createsPAPs:" <+> ppr badPAP
       , text "closureGrowth:" <+> ppr cg
       , text "CG in lam:"   <+> ppr cgil
       , text "fast-calls:" <+> ppr (varSetElems slowdowns)
       , ppWhen opt_PprStyle_Debug extra_sdoc
       ]

    wORDS_PTR = StgCmmArgRep.argRepSizeW (le_dflags env) StgCmmArgRep.P

-- if a free id was floated, then its abs_ids are now free ids
expandFloatedIds :: LevelEnv -> {- In -} VarSet -> {- Out -} IdSet
expandFloatedIds env = foldVarSet snoc emptyVarSet where
  snoc id acc
    | isId id
    , not (isCoVar id)
    = case lookupVarEnv (le_env env) id of
        Nothing -> extendVarSet acc id -- TODO is this case possible?
        Just (new_id, filter isId -> abs_ids)
          | not (null abs_ids) -> -- it's a lambda-lifted function
                                  extendVarSetList acc abs_ids
          | otherwise          -> extendVarSet     acc new_id
    | otherwise
    = acc

-- see Note [Preserving Fast Entries]
wouldIncreaseRuntime ::
  LevelEnv ->
  [Id] ->      -- the abstracted value ids
  VarUses ->   -- FIIs for the bindings' RHS
  VarSet       -- the forgotten ids
wouldIncreaseRuntime env abs_ids binding_group_vus
  = ASSERT(all isId abs_ids)
    mkVarSet (filter bad_id abs_ids)
  where
    bad_id abs_id
      | isJoinId abs_id
      = True               -- *Cannot* abstract over join id (and wouldn't want to)
      | idArity abs_id > 0 -- NB (arity > 0) iff "is known function"
                           -- FIXME This is not true under CallArity! Should
                           -- remember which binders are let-bound to functions
      = case lookupVarEnv binding_group_vus abs_id of
          Just (_, VU _unapplied under exact over)
                   -> no_under && under ||
                      no_exact && exact ||
                      no_over  && over
          Nothing -> False
      | otherwise
      = False

    fps = le_finalPass env `orElse` pprPanic "wouldIncreaseRuntime" empty
    no_under = not (fps_absUnsatVar   fps)
    no_exact = not (fps_absSatVar     fps)
    no_over  = not (fps_absOversatVar fps)

wouldIncreaseAllocation ::
  LevelEnv ->
  IdSet ->      -- the abstracted value ids
  [SummBindPair] -> -- the bindings in the binding group with each's summary
  Summary ->        -- the entire scope of the binding group
  [] -- for each binder:
    ( Bool -- would create PAPs
    , WordOff  -- size of this closure group
    , WordOff  -- estimated increase for closures that are NOT
               -- allocated under a lambda
    , WordOff  -- estimated increase for closures that ARE allocated
               -- under a lambda
    )
wouldIncreaseAllocation env abs_ids_set pairs
                        (Summary { sm_varsUsed = vus, sm_skeleton = scope_sk })
  = ASSERT(all isId (varSetElems abs_ids_set))
    flip map bndrs $ \(TB bndr _) -> case lookupVarEnv vus bndr of
    Nothing -> (False, closuresSize, 0, 0) -- it's a dead variable. Huh.
    Just (_, vu) -> (violatesPAPs, closuresSize, closureGrowth, closureGrowthInLambda)
      where
        violatesPAPs = vu_unapplied vu

        (closureGrowth, closureGrowthInLambda)
          = costToLift (expandFloatedIds env) sizer bndr abs_ids_set scope_sk
    where
      bndrs = map binderOfAnnPair pairs

      dflags = le_dflags env

      -- It's not enough to calculate "total size of abs_ids" because
      -- each binding in a letrec may have incomparable sets of free
      -- ids. abs_ids is merely the union of those sets.
      --
      -- So we instead calculate and then add up the size of each
      -- binding's closure. GHC does not currently share closure
      -- environments, and we either lift the entire recursive binding
      -- group or none of it.
      closuresSize = sum $ flip map pairs $ \(summ, _) ->
        let (words, _, _) =
              StgCmmLayout.mkVirtHeapOffsets dflags isUpdateable $
              StgCmmClosure.addIdReps $
              filter (`elemVarSet` abs_ids_set) $
              varEnvElts $ expandFloatedIds env $ -- NB In versus Out ids
              fvsFromSumm summ
              where isUpdateable = False -- functions are not updateable
        in words + sTD_HDR_SIZE dflags -- ignoring profiling overhead
           -- safely ignoring the silt's satTypes; should always be []
           -- because this is a *function* closure we're considering

      sizer :: Id -> WordOff
      sizer = argRep_sizer . toArgRep . StgCmmClosure.idPrimRep

      argRep_sizer :: ArgRep -> WordOff
      argRep_sizer = StgCmmArgRep.argRepSizeW dflags

type NewId    = Id
type OldIdSet = IdSet
type NewIdSet = IdSet
costToLift :: (OldIdSet -> NewIdSet) -> (Id -> WordOff) ->
  NewId -> NewIdSet -> -- the function binder and its free ids
  Skeleton -> -- abstraction of the scope of the function
  (WordOff, WordOff) -- ( closure growth , closure growth in lambda )
costToLift expander sizer f abs_ids = go where
  go sk = case sk of
    NilSk -> (0,0)
    CloSk _ (expander -> fids) rhs -> -- NB In versus Out ids
      let (!cg1,!cgil1) = go rhs
          cg | f `elemVarSet` fids =
               let newbies = abs_ids `minusVarSet` fids
               in foldVarSet (\id size -> sizer id + size) (0 - sizer f) newbies
             | otherwise           = 0
            -- (max 0) the growths from the RHS, since the closure
            -- might not be entered
            --
            -- in contrast, the effect on the closure's allocation
            -- itself is certain
      in (cg + max 0 cg1, max 0 cgil1)
    BothSk sk1 sk2 -> let (!cg1,!cgil1) = go sk1
                          (!cg2,!cgil2) = go sk2
                       -- they are under different lambdas (if any),
                       -- so we max instead of sum, since their
                       -- multiplicities could differ
                      in (cg1 + cg2   ,   cgil1 `max` cgil2)
    LamSk oneshot sk -> case go sk of
      (cg, cgil) -> if oneshot
                    then (   max 0 $ cg + cgil   ,   0) -- zero entries or one
                    else (0   ,   cg `max` cgil   ) -- perhaps several entries
    AltSk sk1 sk2 -> let (!cg1,!cgil1) = go sk1
                         (!cg2,!cgil2) = go sk2
                     in (   cg1 `max` cg2   ,   cgil1 `max` cgil2   )

----------------------------------------------------
-- Three help functions for the type-abstraction case

lvlFloatRhsComm :: [OutVar] -> Level -> LevelEnv -> Type -> SummCommand
                -> UniqSM (Levelled Term)
lvlFloatRhsComm abs_vars dest_lvl env ty rhs
  = do { rhs' <- lvlComm rhs_env ty rhs
       ; return (mkLambdas abs_vars_w_lvls $ mkCompute ty rhs') }
  where
    (rhs_env, abs_vars_w_lvls) = lvlLamBndrs env dest_lvl abs_vars

lvlFloatRhsTerm :: [OutVar] -> Level -> LevelEnv -> SummTerm
                -> UniqSM (Levelled Term)
lvlFloatRhsTerm abs_vars dest_lvl env rhs
  = do { rhs' <- lvlTerm rhs_env rhs
       ; return (mkLambdas abs_vars_w_lvls rhs') }
   where
     (rhs_env, abs_vars_w_lvls) = lvlLamBndrs env dest_lvl abs_vars

lvlFloatRhsJoin :: [OutVar] -> Level -> LevelEnv -> Type -> SummJoin
                -> UniqSM (Levelled Join)
lvlFloatRhsJoin abs_vars dest_lvl env retTy join
  = do { Join bndrs' comm' <- lvlJoin rhs_env retTy join
       ; return (Join (abs_vars_w_lvls ++ bndrs') comm') }
   where
     (rhs_env, abs_vars_w_lvls) = lvlLamBndrs env dest_lvl abs_vars

lvlFloatRhs :: [OutVar] -> Level -> LevelEnv -> Type
            -> LevelledBndr -> SummBindPair
            -> UniqSM (Levelled BindPair)
lvlFloatRhs abs_vars dest_lvl env retTy bndr' pair
  = case pair of
      (_, AnnBindTerm _bndr term)
        -> do { term' <- lvlFloatRhsTerm abs_vars dest_lvl env term
              ; return (BindTerm bndr' term') }
      (_, AnnBindJoin _bndr join)
        -- Here we DO NOT assume that bndr' and _bndr are join ids! If we're
        -- decontifying, we do the binder before the RHS (awkwardly enough)
        -> do { join' <- lvlFloatRhsJoin abs_vars dest_lvl env retTy join
              ; return (BindJoin bndr' join') }

{-

%************************************************************************
%*                                                                      *
\subsection{Deciding floatability}
%*                                                                      *
%************************************************************************
-}

substAndLvlBndrs :: RecFlag -> LevelEnv -> Level -> [SummBndr] -> (LevelEnv, [LevelledBndr])
substAndLvlBndrs is_rec env lvl bndrs
  = lvlBndrs subst_env lvl subst_bndrs
  where
    (subst_env, subst_bndrs) = substBndrsSL is_rec env bndrs

substBndrsSL :: RecFlag -> LevelEnv -> [SummBndr] -> (LevelEnv, [OutVar])
-- So named only to avoid the name clash with CoreSubst.substBndrs
substBndrsSL is_rec env@(LE { le_subst = subst, le_env = id_env }) (identifiers -> bndrs)
  = ( env { le_subst    = subst'
          , le_env      = foldl add_id  id_env (bndrs `zip` bndrs') }
    , bndrs')
  where
    (subst', bndrs') = case is_rec of
                         NonRecursive -> substBndrs    subst bndrs
                         Recursive    -> substRecBndrs subst bndrs

lvlLamBndrs :: LevelEnv -> Level -> [OutVar] -> (LevelEnv, [LevelledBndr])
-- Compute the levels for the binders of a lambda group
lvlLamBndrs env lvl bndrs
  = lvlBndrs env new_lvl bndrs
  where
    new_lvl | any is_major bndrs = incMajorLvl lvl
            | otherwise          = incMinorLvl lvl

    is_major bndr = isId bndr && not (isProbablyOneShotLambda bndr)
       -- The "probably" part says "don't float things out of a
       -- probable one-shot lambda"


lvlBndrs :: LevelEnv -> Level -> [SeqCoreBndr] -> (LevelEnv, [LevelledBndr])
-- The binders returned are exactly the same as the ones passed,
-- apart from applying the substitution, but they are now paired
-- with a (StayPut level)
--
-- The returned envt has ctxt_lvl updated to the new_lvl
--
-- All the new binders get the same level, because
-- any floating binding is either going to float past
-- all or none.  We never separate binders.
lvlBndrs env@(LE { le_lvl_env = lvl_env }) new_lvl bndrs
  = ( env { le_ctxt_lvl = new_lvl
          , le_lvl_env  = foldl add_lvl lvl_env bndrs }
    , lvld_bndrs)
  where
    lvld_bndrs    = [TB bndr (StayPut new_lvl) | bndr <- bndrs]
    add_lvl env v = extendVarEnv env v new_lvl

  -- Destination level is the max Id level of the expression
  -- (We'll abstract the type variables, if any.)
destLevel :: LevelEnv -> Summary
          -> Bool   -- True <=> is bottom
          -> Level
destLevel env summ is_bot
  | is_bot = tOP_LEVEL  -- Send bottoming bindings to the top
                        -- regardless; see Note [Bottoming floats]
  | otherwise = maxFvLevel isId env summ  -- Max over Ids only; the tyvars
                                          -- will be abstracted

isFunction :: SummTerm -> Bool
-- The idea here is that we want to float *functions* to
-- the top level.  This saves no work, but 
--      (a) it can make the host function body a lot smaller, 
--              and hence inlinable.  
--      (b) it can also save allocation when the function is recursive:
--          h = \x -> letrec f = \y -> ...f...y...x...
--                    in f x
--     becomes
--          f = \x y -> ...(f x)...y...x...
--          h = \x -> f x x
--     No allocation for f now.
-- We may only want to do this if there are sufficiently few free 
-- variables.  We certainly only want to do it for values, and not for
-- constructors.  So the simple thing is just to look for lambdas
isFunction (_, AnnLam (TB b _) e) | isId b    = True
                                  | otherwise = isFunction e
isFunction _                                  = False

{-
%************************************************************************
%*                                                                      *
\subsection{Free-To-Level Monad}
%*                                                                      *
%************************************************************************
-}

type OutVar = Var   -- Post cloning
type OutId  = Id    -- Post cloning

data LevelEnv
  = LE { le_switches  :: FloatOutSwitches
       , le_finalPass :: Maybe FinalPassSwitches
       , le_ctxt_lvl  :: Level           -- The current level
       , le_lvl_env   :: VarEnv Level    -- Domain is *post-cloned* TyVars and Ids
       , le_subst     :: Subst           -- Domain is pre-cloned TyVars and Ids
                                         -- The Id -> CoreExpr in the Subst is ignored
                                         -- (since we want to substitute in LevelledExpr
                                         -- instead) but we do use the Co/TyVar substs
       , le_env      :: IdEnv (OutVar,[OutVar])        -- Domain is pre-cloned Ids
           -- (v,vs) represents the application "v vs0 vs1 vs2" ...
           -- Except in the late float, the vs are all types.

        -- see Note [The Reason SetLevels Does Substitution]
       , le_decont    :: IdSet           -- Domain is pre-cloned JoinIds
                                         -- These are being floated to top level
                                         -- and hence decontified
       , le_dflags    :: DynFlags
       , le_fflags    :: FloatFlags
    }
        -- We clone let- and case-bound variables so that they are still
        -- distinct when floated out; hence the le_subst/le_env.
        -- (see point 3 of the module overview comment).
        -- We also use these envs when making a variable polymorphic
        -- because we want to float it out past a big lambda.
        --
        -- The le_subst and le_env always implement the same mapping,
        -- but the le_subst maps to CoreExpr whereas the le_env maps
        -- to a (possibly nullary) type application.  There is never
        -- any real difference between the two ranges, but sadly the
        -- types differ.  The le_subst is used when substituting in a
        -- variable's IdInfo; the le_env when we find a Var.
        --
        -- In addition the le_env representation caches the free
        -- tyvars range, just so we don't have to call freeVars on the
        -- type application repeatedly.
        --
        -- The domain of the both envs is *pre-cloned* Ids, though
        --
        -- The domain of the le_lvl_env is the *post-cloned* Ids

initialEnv :: DynFlags -> FloatFlags
           -> FloatOutSwitches -> Maybe FinalPassSwitches
           -> LevelEnv
initialEnv dflags fflags float_lams fps
  = LE { le_switches = float_lams
       , le_finalPass = fps
       , le_ctxt_lvl = tOP_LEVEL
       , le_lvl_env = emptyVarEnv
       , le_subst = emptySubst
       , le_env = emptyVarEnv
       , le_decont = emptyVarSet
       , le_dflags = dflags
       , le_fflags = fflags }

isFinalPass :: LevelEnv -> Bool
isFinalPass env = isJust (le_finalPass env)

floatConsts :: LevelEnv -> Bool
floatConsts le = floatOutConstants (le_switches le)

floatPAPs :: LevelEnv -> Bool
floatPAPs le = floatOutPartialApplications (le_switches le)

setCtxtLvl :: LevelEnv -> Level -> LevelEnv
setCtxtLvl env lvl = env { le_ctxt_lvl = lvl }

-- extendCaseBndrLvlEnv adds the mapping case-bndr->scrut-var if it can
-- (see point 4 of the module overview comment)
extendCaseBndrEnv :: LevelEnv
                  -> SummBndr       -- Pre-cloned case binder
                  -> Levelled Term  -- Post-cloned scrutinee
                  -> LevelEnv
extendCaseBndrEnv le@(LE { le_subst = subst, le_env = id_env })
                  (TB case_bndr _) (Var scrut_var)
  = le { le_subst   = extendSubstWithVar subst case_bndr scrut_var
       , le_env     = add_id id_env (case_bndr, scrut_var) }
extendCaseBndrEnv env _ _ = env

maxFvLevel :: (Var -> Bool) -> LevelEnv -> Summary -> Level
maxFvLevel max_me (LE { le_lvl_env = lvl_env, le_env = id_env }) (fvsFromSumm -> var_set)
  = foldVarSet max_in tOP_LEVEL var_set
  where
    max_in in_var lvl 
       = foldr max_out lvl (case lookupVarEnv id_env in_var of
                                Just (v, abs_vars) -> v:abs_vars
                                Nothing            -> [in_var])

    max_out out_var lvl 
        | max_me out_var = case lookupVarEnv lvl_env out_var of
                                Just lvl' -> maxLvl lvl' lvl
                                Nothing   -> lvl 
        | otherwise = lvl       -- Ignore some vars depending on max_me

lookupVar :: LevelEnv -> Id -> Levelled Term
lookupVar le v = case lookupVarEnv (le_env le) v of
                    Just (v', vs') -> mkVarAppTerm (Var v') vs'
                    _              -> Var v

decontifying :: LevelEnv -> JoinId -> Bool
decontifying le j = j `elemVarSet` le_decont le

abstractVars :: Level -> LevelEnv -> VarSet -> [OutVar]
        -- Find the variables in fvs, free vars of the target expresion,
        -- whose level is greater than the destination level
        -- These are the ones we are going to abstract out
abstractVars dest_lvl (LE { le_subst = subst, le_lvl_env = lvl_env }) in_fvs
  = map zap $ uniq $ sortQuantVars
    [out_var | out_fv  <- varSetElems (substVarSet subst in_fvs)
             , out_var <- varSetElems (close out_fv)
             , abstract_me out_var ]
        -- NB: it's important to call abstract_me only on the OutIds the
        -- come from substVarSet (not on fv, which is an InId)
  where
    uniq :: [Var] -> [Var]
        -- Remove adjacent duplicates; the sort will have brought them together
    uniq (v1:v2:vs) | v1 == v2  = uniq (v2:vs)
                    | otherwise = v1 : uniq (v2:vs)
    uniq vs = vs

    abstract_me v = case lookupVarEnv lvl_env v of
                        Just lvl -> dest_lvl `ltLvl` lvl
                        Nothing  -> False

        -- We are going to lambda-abstract, so nuke any IdInfo,
        -- and add the tyvars of the Id (if necessary)
    zap v | isId v = WARN( isStableUnfolding (idUnfolding v) ||
                           not (isEmptySpecInfo (idSpecialisation v)),
                           text "absVarsOf: discarding info on" <+> ppr v )
                     setIdInfo v vanillaIdInfo
          | otherwise = v

    close :: Var -> VarSet  -- Close over variables free in the type
                            -- Result includes the input variable itself
    close v = foldVarSet (unionVarSet . close)
                         (unitVarSet v)
                         (varTypeTyVars v)



type LvlM result = UniqSM result

initLvl :: UniqSupply -> UniqSM a -> a
initLvl = initUs_


newPolyBndrs :: Level -> LevelEnv -> [OutVar] -> [SummBndr] -> UniqSM (LevelEnv, [OutId])
-- The envt is extended to bind the new bndrs to dest_lvl, but
-- the ctxt_lvl is unaffected
newPolyBndrs dest_lvl
             env@(LE { le_lvl_env = lvl_env, le_subst = subst, le_env = id_env })
             abs_vars (identifiers -> bndrs)
 = ASSERT( all (not . isCoVar) bndrs )   -- What would we add to the CoSubst in this case. No easy answer.
   do { uniqs <- getUniquesM
      ; let new_bndrs = zipWith mk_poly_bndr bndrs uniqs
            bndr_prs  = bndrs `zip` new_bndrs
            env' = env { le_lvl_env = foldl add_lvl   lvl_env new_bndrs
                       , le_subst   = foldl add_subst subst   bndr_prs
                       , le_env     = foldl add_id    id_env  bndr_prs }
      ; return (env', new_bndrs) }
  where
    add_lvl   env v' = extendVarEnv env v' dest_lvl
    add_subst env (v, v') = extendIdSubst env v (Core.mkVarApps (Core.Var v') abs_vars)
                              -- Will be used in IdInfo
    add_id    env (v, v') = extendVarEnv env v (v', abs_vars)

    mk_poly_bndr bndr uniq = transferPolyIdInfo bndr abs_vars $         -- Note [transferPolyIdInfo] in Id.lhs
                             mkSysLocal (mkFastString str) uniq poly_ty
                           where
                             str     = prefix ++ occNameString (getOccName bndr)
                             prefix  = if isFinalPass env then "llf_" else "poly_"
                             poly_ty = mkPiTypes abs_vars (substTy subst (idType bndr))

newLvlVar :: Levelled Term        -- The RHS of the new binding
          -> Bool                -- Whether it is bottom
          -> LvlM Id
newLvlVar lvld_rhs is_bot
  = do { uniq <- getUniqueM
       ; return (add_bot_info (mkLocalId (mk_name uniq) rhs_ty)) }
  where
    add_bot_info var  -- We could call annotateBotStr always, but the is_bot
                      -- flag just tells us when we don't need to do so
       | is_bot    = annotateBotStr var (exprBotStrictness_maybe core_rhs)
       | otherwise = var
    core_rhs = termToCoreExpr (deTag lvld_rhs)
    rhs_ty = termType lvld_rhs
    mk_name uniq = mkSystemVarName uniq (mkFastString "lvl")

cloneVars :: RecFlag -> LevelEnv -> Level -> [SummBndr] -> LvlM (LevelEnv, [Var])
-- Works for Ids, TyVars and CoVars
-- The dest_lvl is attributed to the binders in the new env,
-- but cloneVars doesn't affect the ctxt_lvl of the incoming env
cloneVars is_rec
          env@(LE { le_subst = subst, le_lvl_env = lvl_env, le_env = id_env })
          dest_lvl (identifiers -> vs)
  = do { us <- getUniqueSupplyM
       ; let (subst', vs1) = case is_rec of
                               NonRecursive -> cloneBndrs      subst us vs
                               Recursive    -> cloneRecIdBndrs subst us vs
             vs2  = map zap_demand_info vs1  -- See Note [Zapping the demand info]
             prs  = vs `zip` vs2
             env' = env { le_lvl_env = foldl add_lvl lvl_env vs2
                        , le_subst   = subst'
                        , le_env     = foldl add_id id_env prs }

       ; return (env', vs2) }
  where
     add_lvl env v_cloned = extendVarEnv env v_cloned dest_lvl

decontifyBndr :: LevelEnv -> Type -> SummBndr -> (LevelEnv, SummBndr)
decontifyBndr le retTy (TB bndr summ)
  | isJoinId bndr
  = (le', TB bndr' summ)
  | otherwise
  = (le, TB bndr summ)
  where
    le'   = le { le_decont = extendVarSet (le_decont le) bndr' }
    bndr' = joinIdToCore retTy bndr

add_id :: IdEnv (OutVar, [OutVar]) -> (Var, Var) -> IdEnv (OutVar, [OutVar])
add_id id_env (v, v1)
  | isTyVar v = delVarEnv    id_env v
  | isCoVar v = delVarEnv    id_env v
  | otherwise = extendVarEnv id_env v (v1, [])

zap_demand_info :: Var -> Var
zap_demand_info v
  | isId v    = zapDemandIdInfo v
  | otherwise = v

{-
Note [Preserving Fast Entries] (wrt Note [Late Lambda Floating])
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The policy: avoid changing fast entry invocations of free variables
(known call) into slow entry invocations of the new parameter
representing that free variable (unknown call).

  ... let f x = ... in
      let g x = ... (f ...) ... in  -- GOOD: call to f is fast entry
      ... g a ...

  => -- NB f wasn't floated

  poly_g f x = ... (f ...) ... -- BAD: call to f is slow entry

  ... let f x = ... in
      ... poly_g f a ...

The mechanism: when considering a let-bound lambda, we disallow the
float if any of the variables being abstracted over are applied in the
RHS. The flags -f(no)-late-abstract-undersat-var and
-f(no)-late-abstract-sat-var determine the details of this check.

It is intended that only applications of locally-bound free variables
*whose bindings are not themselves floated* can prevent a float. This
comes for free. The free variable information is not updated during
the setLevels pass. On the other hand, the set of abstracted variables
is calculated using the current LevelEnv. Thus: while a floated
function's original Id may be in the FII, it won't be in the
abs_vars.

Note [Zapping the demand info]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
VERY IMPORTANT: we must zap the demand info if the thing is going to
float out, becuause it may be less demanded than at its original
binding site.  Eg
   f :: Int -> Int
   f x = let v = 3*4 in v+x
Here v is strict; but if we float v to top level, it isn't any more.

Note [The Reason SetLevels Does Substitution]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If a binding is going to be floated, setLevels carries a substitution
in order to eagerly replace that binding's occurrences with a
reference to the floated binding. Why doesn't it instead create a
simple binding right next to it and rely on the wise and weary
simplifier to handle the inlining? It's an issue with nested bindings.

  outer a = let x = ... a ... in
            let y = ... x ... in
            ... x ... y ...

Currently, when setLevels processes the x binding, the substitution
leads to the following intermediate step. (I am showing the result of
the substitution as if it were already applied.)

  x' a = ...

  out a = let y = ... x' a ... in
          ... x' a ... y ...

If we were to instead rely on the simplifier, we'd do something like this

  x' a = ...

  out a = let x = x' a in
          let y = ... x ... in
          ... x ... y ...

The problem here is that the subsequent step in which setLevels
analyzes the y binding would still treat x as y's only free
variable. With the eager substitution, on the other hand, x' is not
treated as a free variable since it's a global and a *is* recognized
as a free variable. That's the behavior we currently intend.
-}

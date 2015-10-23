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
{-# LANGUAGE CPP, ViewPatterns #-}
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
import Language.SequentCore.FloatOut.Flags
import Language.SequentCore.FloatOut.Summary
import Language.SequentCore.FVs
import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import CoreSyn          ( Unfolding(..),
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
import Id
import IdInfo
import Var
import VarSet
import VarEnv
import Literal          ( literalType, litIsTrivial )
import Demand           ( StrictSig, isBottomingSig )
import Name             ( getOccName, mkSystemVarName )
import OccName          ( occNameString )
import Type             ( isUnLiftedType, Type, mkPiTypes, tyVarsOfType )
import BasicTypes       ( Arity, RecFlag(..),
                          inlinePragmaActivation, isNeverActive )
import UniqSupply
import Util
import Outputable
import FastString
import Pair
import DynFlags

import Control.Applicative ( (<$>), (<*>) )
import Data.Maybe          ( isJust )

#define ASSERT(e)      if debugIsOn && not (e) then (assertPanic __FILE__ __LINE__) else
#define ASSERT2(e,msg) if debugIsOn && not (e) then (assertPprPanic __FILE__ __LINE__ (msg)) else
#define WARN( e, msg ) (warnPprTrace (e) __FILE__ __LINE__ (msg)) $

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
  = initLvl us (do_them init_env summarized_binds)
  where
    init_env = initialEnv dflags fflags float_lams fps

    prepped_binds | is_final_pass = prepareForFinalPass dflags fflags us binds
                  | otherwise     = binds

    is_final_pass = isJust fps
    
    summarized_binds = summarizeProgram prepped_binds

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
    binds1 | fgopt Opt_LLF_Stabilize fflags
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
isUnstableUnfolding (CoreUnfolding { uf_src = src }) = not (isStableSource src)
isUnstableUnfolding _                                = False

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

    show_unfolding (CoreUnfolding { uf_src = src, uf_guidance = guidance })
       =  expose_all         -- 'expose_all' says to expose all
                             -- unfoldings willy-nilly

       || isStableSource src     -- Always expose things whose
                                 -- source is an inline rule

       || not (bottoming_fn      -- No need to inline bottom functions
           || never_active       -- Or ones that say not to
           || loop_breaker       -- Or that are loop breakers
           || neverUnfoldGuidance guidance)
    show_unfolding (DFunUnfolding {}) = True
    show_unfolding _                  = False

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
        otherFrames' <- mapM (lvlMFEFrame env) otherFrames
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
  = do
    args' <- mapM (lvlTerm env) args
    case lookupVar env j of
      Var j' -> return $ Jump args' j' 
      other  -> pprPanic "lvlComm" (text "Abstracted join??" <+> ppr other) 

lvlFrame :: LevelEnv
         -> SummFrame
         -> LvlM (Levelled Frame)
lvlFrame env (_, AnnApp arg) = App <$> lvlMFE False env arg
lvlFrame env (_, AnnCast co) = return $ Cast (substCo (le_subst env) co)
lvlFrame _   (_, AnnTick ti) = return $ Tick ti

lvlJoin :: LevelEnv -> Type -> SummJoin -> LvlM (Levelled Join)
lvlJoin env retTy (_, AnnJoin bndrs body)
  = do { new_body <- lvlMFEComm True new_env retTy body
       ; return (Join new_bndrs new_body) }
  where
    (env1, bndrs1)       = substBndrsSL NonRecursive env bndrs
    (new_env, new_bndrs) = lvlLamBndrs env1 (le_ctxt_lvl env) bndrs1
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

lvlMFEFrame :: LevelEnv
            -> SummFrame
            -> LvlM (Levelled Frame)
lvlMFEFrame env (_, AnnApp arg) = App <$> lvlMFE False env arg
                                    -- TODO Use strictness of argument?
                                    -- Is there a reason that GHC doesn't?
lvlMFEFrame env (_, AnnCast co) = return $ Cast (substCo (le_subst env) co)
lvlMFEFrame _   (_, AnnTick ti) = return $ Tick ti

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
    dest_lvl = destLevel env summ (isFunctionComm ann_comm) is_bot
    summ     = getSummary ann_comm
    abs_vars = abstractVars dest_lvl env summ
    
        -- Eliminate a few kinds of commands from consideration
    never_float (_, AnnEval _ _ (_, AnnCase {})) = True -- Don't share cases
    never_float (_, AnnJump {})                  = True -- Note [Don't float jumps]
    never_float _                                = False
    
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
trimForFloating _ comm@(_, AnnLet {}) = (comm, [])
trimForFloating env (fvs, AnnEval term frames end@(_, AnnReturn))
  = ((fvs, AnnEval term frames' end), extraFrames)
  where
    (frames', extraFrames) = go (reverse frames) []
    go ((_, AnnTick ti) : fs) acc = go fs (Tick ti : acc)
    go ((_, AnnCast co) : fs) acc = go fs (Cast (substCo (le_subst env) co) : acc)
    go fs                     acc = (reverse fs, acc)
trimForFloating _ comm = pprPanic "trimForFloating" (ppr (deAnnotateCommand comm))
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
Note [Don't float jumps]
~~~~~~~~~~~~~~~~~~~~~~~~

In order to float a jump, we'd need to abstract it as a join point. But then we
never float join points because it never helps. So we don't float jumps.

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
lvlBind env ty (_, AnnNonRec (_, AnnBindJoin bndr join))
  = -- Don't float join points
    do { join' <- lvlJoin env ty join
       ; let  bind_lvl        = le_ctxt_lvl env -- Joins don't participate in 
                                                -- floating, so don't inc level
              (env', [bndr']) = substAndLvlBndrs NonRecursive env bind_lvl [bndr]
       ; return (NonRec (BindJoin bndr' join'), env') }

lvlBind env ty (_, AnnRec pairs@((_, AnnBindJoin {}) : _))
  = -- Don't float join points
    do { let  bind_lvl       = le_ctxt_lvl env -- Joins don't participate in 
                                               -- floating, so don't inc level
              (env', bndrs') = substAndLvlBndrs NonRecursive env bind_lvl bndrs
       ; joins' <- mapM (lvlJoin env' ty) joins
       ; return (Rec (zipWith BindJoin bndrs' joins'), env') }
  where
    (bndrs, joins) = ASSERT(all (bindsJoin . deAnnotateBindPair) pairs)
                     unzip [(bndr, join) | (_, AnnBindJoin bndr join) <- pairs]

lvlBind env _ty (_, AnnNonRec (_, AnnBindTerm bndr@(TB var _) rhs@(rhs_summ,_)))
  | isTyVar var     -- Don't do anything for TyVar binders
                    --   (simplifier gets rid of them pronto)
  || isCoVar var    -- Difficult to fix up CoVar occurrences (see extendPolyLvlEnv)
                    -- so we will ignore this case for now
  || not (profitableFloat env dest_lvl)
  || (isTopLvl dest_lvl && isUnLiftedType (idType var))
          -- We can't float an unlifted binding to top level, so we don't 
          -- float it at all.  It's a bit brutal, but unlifted bindings 
          -- aren't expensive either
  = -- No float
    do { rhs' <- lvlTerm env rhs
       ; let  bind_lvl        = incMinorLvl (le_ctxt_lvl env)
              (env', [bndr']) = substAndLvlBndrs NonRecursive env bind_lvl [bndr]
       ; return (NonRec (BindTerm bndr' rhs'), env') }

  -- Otherwise we are going to float
  | null abs_vars
  = do {  -- No type abstraction; clone existing binder
         rhs' <- lvlTerm (setCtxtLvl env dest_lvl) rhs
       ; (env', [bndr']) <- cloneVars NonRecursive env dest_lvl [bndr]
       ; return (NonRec (BindTerm (TB bndr' (FloatMe dest_lvl)) rhs'), env') }

  | otherwise
  = do {  -- Yes, type abstraction; create a new binder, extend substitution, etc
         rhs' <- lvlFloatRhsTerm abs_vars dest_lvl env rhs
       ; (env', [bndr']) <- newPolyBndrs dest_lvl env abs_vars [bndr]
       ; return (NonRec (BindTerm (TB bndr' (FloatMe dest_lvl)) rhs'), env') }

  where
    bind_summ  = rhs_summ `unionSumm` summFromFVs (idFreeVars var)
    abs_vars   = abstractVars dest_lvl env bind_summ
    dest_lvl   = destLevel env bind_summ (isFunction rhs) is_bot
    is_bot     = termIsBottom (deAnnotateTerm rhs)

lvlBind env _ty (bind_summ, AnnRec pairs)
  | not (profitableFloat env dest_lvl)
  = do { let bind_lvl = incMinorLvl (le_ctxt_lvl env)
             (env', bndrs') = substAndLvlBndrs Recursive env bind_lvl bndrs
       ; rhss' <- mapM (lvlTerm env') rhss
       ; return (Rec (zipWith BindTerm bndrs' rhss'), env') }

  | null abs_vars
  = do { (new_env, new_bndrs) <- cloneVars Recursive env dest_lvl bndrs
       ; new_rhss <- mapM (lvlTerm (setCtxtLvl new_env dest_lvl)) rhss
       ; let tagged_bndrs = [TB b (FloatMe dest_lvl) | b <- new_bndrs]
       ; return ( Rec (zipWith BindTerm tagged_bndrs new_rhss)
                , new_env) }

-- ToDo: when enabling the floatLambda stuff,
--       I think we want to stop doing this
  | [(_, AnnBindTerm bndr rhs)] <- pairs
  , count isId abs_vars > 1
  = do  -- Special case for self recursion where there are
        -- several variables carried around: build a local loop:
        --      poly_f = \abs_vars. \lam_vars . letrec f = \lam_vars. rhs in f lam_vars
        -- This just makes the closures a bit smaller.  If we don't do
        -- this, allocation rises significantly on some programs
        --
        -- We could elaborate it for the case where there are several
        -- mutually functions, but it's quite a bit more complicated
        --
        -- This all seems a bit ad hoc -- sigh
    let (rhs_env, abs_vars_w_lvls) = lvlLamBndrs env dest_lvl abs_vars
        rhs_lvl = le_ctxt_lvl rhs_env

    (rhs_env', [new_bndr]) <- cloneVars Recursive rhs_env rhs_lvl [bndr]
    let
        (lam_bndrs, rhs_body)   = collectAnnBinders rhs
        (body_env1, lam_bndrs1) = substBndrsSL NonRecursive rhs_env' lam_bndrs
        (body_env2, lam_bndrs2) = lvlLamBndrs body_env1 rhs_lvl lam_bndrs1
    new_rhs_body <- lvlTerm body_env2 rhs_body
    (poly_env, [poly_bndr]) <- newPolyBndrs dest_lvl env abs_vars [bndr]
    let new_body = mkAppTerm (Var new_bndr) (map mkVarArg lam_bndrs1)
    return (Rec [BindTerm (TB poly_bndr (FloatMe dest_lvl))
                  (mkLambdas abs_vars_w_lvls $
                   mkLambdas lam_bndrs2 $
                   (`addLetsToTerm` new_body) $
                   [Rec [BindTerm ( TB new_bndr (StayPut rhs_lvl) )
                                 ( mkLambdas lam_bndrs2 new_rhs_body )]])]
           , poly_env)

  | otherwise  -- Non-null abs_vars
  = do { (new_env, new_bndrs) <- newPolyBndrs dest_lvl env abs_vars bndrs
       ; new_rhss <- mapM (lvlFloatRhsTerm abs_vars dest_lvl new_env) rhss
       ; return ( Rec (zipWith BindTerm [TB b (FloatMe dest_lvl) | b <- new_bndrs]
                                        new_rhss)
                , new_env) }

  where
    (bndrs,rhss) = ASSERT(all (bindsTerm . deAnnotateBindPair) pairs)
                   unzip [ (bndr, rhs) | (_, AnnBindTerm bndr rhs) <- pairs ]

    dest_lvl = destLevel env bind_summ (all isFunction rhss) False
    abs_vars = abstractVars dest_lvl env bind_summ

profitableFloat :: LevelEnv -> Level -> Bool
profitableFloat env dest_lvl
  =  (dest_lvl `ltMajLvl` le_ctxt_lvl env)  -- Escapes a value lambda
  || isTopLvl dest_lvl                      -- Going all the way to top level

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
          -> Bool   -- True <=> is function
          -> Bool   -- True <=> is bottom
          -> Level
destLevel env summ is_function is_bot
  | is_bot = tOP_LEVEL  -- Send bottoming bindings to the top
                        -- regardless; see Note [Bottoming floats]
  | Just n_args <- floatLams env
  , n_args > 0  -- n=0 case handled uniformly by the 'otherwise' case
  , is_function
  , countFreeIds summ <= n_args
  = tOP_LEVEL   -- Send functions to top level; see
                -- the comments with isFunction

  | otherwise = maxFvLevel isId env summ  -- Max over Ids only; the tyvars
                                          -- will be abstracted

isFunctionComm :: SummCommand -> Bool
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
isFunctionComm (_, AnnEval term [] (_, AnnReturn))
  = isFunction term
isFunctionComm _
  = False

isFunction :: SummTerm -> Bool
isFunction (_, AnnLam (TB b _) e) | isId b    = True
                                  | otherwise = isFunction e
isFunction _                                  = False

countFreeIds :: Summary -> Int
countFreeIds = foldVarSet add 0 . fvsFromSumm
  where
    add :: Var -> Int -> Int
    add v n | isId v    = n+1
            | otherwise = n 

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
  = LE { le_switches :: FloatOutSwitches
       , le_fps      :: Maybe FinalPassSwitches
       , le_ctxt_lvl :: Level           -- The current level
       , le_lvl_env  :: VarEnv Level    -- Domain is *post-cloned* TyVars and Ids
       , le_subst    :: Subst           -- Domain is pre-cloned TyVars and Ids
                                        -- The Id -> CoreExpr in the Subst is ignored
                                        -- (since we want to substitute in LevelledExpr
                                        -- instead) but we do use the Co/TyVar substs
       , le_env      :: IdEnv ([OutVar], Levelled Term) -- Domain is pre-cloned Ids
           -- (v,vs) represents the application "v vs0 vs1 vs2" ...
           -- Except in the late float, the vs are all types.

        -- see Note [The Reason SetLevels Does Substitution]

       , le_dflags   :: DynFlags
       , le_fflags   :: FloatFlags
    }
        -- We clone let- and case-bound variables so that they are still
        -- distinct when floated out; hence the le_subst/le_env.
        -- (see point 3 of the module overview comment).
        -- We also use these envs when making a variable polymorphic
        -- because we want to float it out past a big lambda.
        --
        -- The le_subst and le_env always implement the same mapping, but the
        -- le_subst maps to CoreExpr and the le_env to LevelledExpr
        -- Since the range is always a variable or type application,
        -- there is never any difference between the two, but sadly
        -- the types differ.  The le_subst is used when substituting in
        -- a variable's IdInfo; the le_env when we find a Var.
        --
        -- In addition the le_env records a list of tyvars free in the
        -- type application, just so we don't have to call freeVars on
        -- the type application repeatedly.
        --
        -- The domain of the both envs is *pre-cloned* Ids, though
        --
        -- The domain of the le_lvl_env is the *post-cloned* Ids

initialEnv :: DynFlags -> FloatFlags
           -> FloatOutSwitches -> Maybe FinalPassSwitches
           -> LevelEnv
initialEnv dflags fflags float_lams fps
  = LE { le_switches = float_lams
       , le_fps = fps
       , le_ctxt_lvl = tOP_LEVEL
       , le_lvl_env = emptyVarEnv
       , le_subst = emptySubst
       , le_env = emptyVarEnv
       , le_dflags = dflags
       , le_fflags = fflags }

floatLams :: LevelEnv -> Maybe Int
floatLams le = floatOutLambdas (le_switches le)

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
                                Just (abs_vars, _) -> abs_vars
                                Nothing            -> [in_var])

    max_out out_var lvl 
        | max_me out_var = case lookupVarEnv lvl_env out_var of
                                Just lvl' -> maxLvl lvl' lvl
                                Nothing   -> lvl 
        | otherwise = lvl       -- Ignore some vars depending on max_me

lookupVar :: LevelEnv -> Id -> Levelled Term
lookupVar le v = case lookupVarEnv (le_env le) v of
                    Just (_, expr) -> expr
                    _              -> Var v

abstractVars :: Level -> LevelEnv -> Summary -> [OutVar]
        -- Find the variables in fvs, free vars of the target expresion,
        -- whose level is greater than the destination level
        -- These are the ones we are going to abstract out
abstractVars dest_lvl (LE { le_subst = subst, le_lvl_env = lvl_env }) (fvsFromSumm -> in_fvs)
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
    add_id    env (v, v') = extendVarEnv env v ((v':abs_vars), mkVarAppTerm (Var v') abs_vars)

    mk_poly_bndr bndr uniq = transferPolyIdInfo bndr abs_vars $         -- Note [transferPolyIdInfo] in Id.lhs
                             mkSysLocal (mkFastString str) uniq poly_ty
                           where
                             str     = "poly_" ++ occNameString (getOccName bndr)
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

add_id :: IdEnv ([Var], Levelled Term) -> (Var, Var) -> IdEnv ([Var], Levelled Term)
add_id id_env (v, v1)
  | isTyVar v = delVarEnv    id_env v
  | otherwise = extendVarEnv id_env v ([v1], ASSERT(not (isCoVar v1)) Var v1)

zap_demand_info :: Var -> Var
zap_demand_info v
  | isId v    = zapDemandIdInfo v
  | otherwise = v

{-
Note [Zapping the demand info]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
VERY IMPORTANT: we must zap the demand info if the thing is going to
float out, becuause it may be less demanded than at its original
binding site.  Eg
   f :: Int -> Int
   f x = let v = 3*4 in v+x
Here v is strict; but if we float v to top level, it isn't any more.
-}

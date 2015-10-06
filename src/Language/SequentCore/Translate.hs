{-# LANGUAGE ParallelListComp, TupleSections, MultiWayIf, ViewPatterns,
             LambdaCase, BangPatterns, CPP #-}

-- | 
-- Module      : Language.SequentCore.Translate
-- Description : Core \<-\> Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Translation between Sequent Core and native GHC Core.

module Language.SequentCore.Translate (
  -- $txn
  fromCoreModule, termFromCoreExpr, joinFromCoreExprByKontType,
  bindsToCore,
  commandToCoreExpr, termToCoreExpr, joinToCoreExpr, joinIdToCore,
  CoreContext, kontToCoreExpr,
  onCoreExpr, onSequentCoreTerm
) where

import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import BasicTypes ( Arity, RecFlag(..), TopLevelFlag(..), TupleSort(..)
                  , isNonRec, isNotTopLevel )
import CoreSubst
import CoreUnfold
import qualified CoreSyn as Core
import qualified CoreUtils as Core
import qualified CoreFVs as Core
import FastString
import Id
import IdInfo
import Maybes
import qualified MkCore as Core
import MkId
import Outputable  hiding ( (<>) )
import Type        hiding ( substTy )
import TysPrim
import TysWiredIn
import UniqFM     ( intersectUFM_C )
import Unique
import Util       ( count )
import VarEnv
import VarSet

import Control.Applicative
import Control.Exception ( assert )
import Control.Monad
import Control.Monad.Fix
import Data.List
import Data.Monoid

-- $txn
-- The translations to and from Sequent Core are /not/ guaranteed to be perfect
-- inverses. However, any differences between @e@ and @commandToCoreExpr
-- (fromCoreExpr e)@ should be operationally insignificant, such as a @let@
-- floating out from a function being applied. A more precise characterization
-- of the indended invariants of these functions would entail some sort of
-- /bisimulation/, but it should suffice to know that the translations are
-- "faithful enough."

------------------------------------------------
-- Public interface for Core --> Sequent Core --
------------------------------------------------

-- | Translates a list of Core bindings into Sequent Core.
fromCoreModule :: [Core.CoreBind] -> [SeqCoreBind]
fromCoreModule = fromCoreBinds . escAnalProgram

-- | Translates a single Core expression as a Sequent Core term.
termFromCoreExpr :: Core.CoreExpr -> SeqCoreTerm
termFromCoreExpr expr
  = fromCoreExprAsTerm env markedExpr
  where
    markedExpr = runEscM (escAnalExpr expr)
    env = initFromCoreEnvForExpr expr

-- | Translates a single Core expression as a Sequent Core parameterized
-- continuation, given the continuation type it should translate to. Used in
-- translating unfoldings on JoinIds, since we have the Sequent Core type
-- already in that case.
joinFromCoreExprByKontType :: Type -> Core.CoreExpr -> SeqCoreJoin
joinFromCoreExprByKontType ty expr
  = fromCoreExprAsJoin env ([], Return) (argDescsForKontTy ty) markedExpr
  where
    markedExpr = runEscM (escAnalExpr expr)
    env = initFromCoreEnvForExpr expr

---------------------------------------
-- Phase 1: Escape-analyse Core code --
---------------------------------------

{-
Note [Escape analysis]
~~~~~~~~~~~~~~~~~~~~~~

The purpose of the escape analysis is to work out which let-bound functions we
can translate as parameterized continuations rather than as functions. To do
this, we gather information on all the identifier's occurrences, namely:

  Does every occurrence of f appear in a non-escaping context?

To be in a non-escaping context, the occurrence of f must be a tail call in the
context that declared it - that is, not inside a lambda, an argument, a cast
(see Note [Calls inside casts]), etc.

We perform the escape analysis by passing a Var -> Bool mapping bottom-up. Any
candidate for contification (that is, any let-bound variable) that appears in an
expression will appear in the returned mapping. If f appears only in
non-escaping contexts (that is, does not escape), it maps to True; if it appears
at least once in an escaping context, it maps to False. When combining mappings,
say when analysing the branches of a case, we union them together, performing an
AND on any two variables that appear in both mappings. Then, whenever the
traversal returns from an escaping context, such as a lambda or an argument
position, we take the whole mapping and set every value to False, since every
variable that appears in such a context escapes.

(In practice, we save some time by keeping two sets rather than one mapping--one
records all variables seen, and the other records the subset of those that
escape. Rather than set every value to False, then, we just set the escapee set
equal to the occurrence set.)

The result of the escape analysis is an annotated version of the code where each
binder is marked according to whether it should be contified and, if so, what
its total arity is (that is, arity counting both type and value binders).

Note [Calls inside casts]
~~~~~~~~~~~~~~~~~~~~~~~~~

If we try to contify a function that's invoked inside a cast, the resulting
program will be ill-typed. From the perspective of (Dual) System FC's
operational semantics, this is unsurprising because a cast is an operation and
a tail call is definitionally the final operation a function performs. However,
the cast is a fiction; all casts (and types) are erased on translation to STG.
Hence CoreToStg's escape analysis is able to contify (or let-no-escape) more
functions than ours. It's unclear what the workaround might be, though it's also
unclear how often this is a problem in practice.
-}

-- Bottom-up data --

data EscapeAnalysis
  = EA { ea_nonEsc  :: IdEnv CallInfo
       , ea_allVars :: IdSet }

data CallInfo
  = CI { ci_arity   :: TotalArity  -- Counts *all* arguments, including types
       , ci_args    :: Call        -- Invariant: Length is ci_arity
       , ci_scope   :: ScopeType } -- Recursive call?

type TotalArity = Arity -- Counts *all* arguments, including types
type Call = [Core.CoreExpr]
data Occs = Esc | NonEsc CallInfo
data ScopeType = Inside | Outside -- In recursive RHS or not?

emptyEscapeAnalysis :: EscapeAnalysis
emptyEscapeAnalysis = EA { ea_nonEsc  = emptyVarEnv
                         , ea_allVars = emptyVarSet }

unitCall :: Id -> Call -> ScopeType -> EscapeAnalysis
unitCall x call scope = EA { ea_nonEsc  = unitVarEnv x (CI { ci_arity = length call
                                                           , ci_args  = call
                                                           , ci_scope = scope })
                           , ea_allVars = unitVarSet x }

markAllAsEscaping :: EscapeAnalysis -> EscapeAnalysis
markAllAsEscaping ea = ea { ea_nonEsc = emptyVarEnv }

-- XXX This implementation is probably slower than is possible using something
-- like Data.IntMap.mergeWithKey.
intersectWithMaybeVarEnv :: (elt1 -> elt2 -> Maybe elt3)
                         -> VarEnv elt1 -> VarEnv elt2 -> VarEnv elt3
intersectWithMaybeVarEnv f env1 env2
  = mapVarEnv fromJust $ filterVarEnv isJust $ intersectUFM_C f env1 env2

combineEscapeAnalyses :: EscapeAnalysis -> EscapeAnalysis -> EscapeAnalysis
combineEscapeAnalyses ea1 ea2
  | isEmptyVarEnv (ea_allVars ea1) = ea2
  | isEmptyVarEnv (ea_allVars ea2) = ea1
  | otherwise = EA { ea_allVars = ea_allVars ea1 `unionVarSet` ea_allVars ea2
                   , ea_nonEsc  = onlyIn1 `plusVarEnv` onlyIn2
                                          `plusVarEnv` nonEscBoth }
  where
    -- There are three ways a variable makes it into the non-escaping set for
    -- the combined analysis:
    --   1. It appears in the left non-escaping set and not at all on the right
    --   2. It appears in the right non-escaping set and not at all on the left
    --   3. It appears in both non-escaping sets with the same arity
    
    onlyIn1 = ea_nonEsc ea1 `minusVarEnv` ea_allVars ea2
    onlyIn2 = ea_nonEsc ea2 `minusVarEnv` ea_allVars ea1
    nonEscBoth = intersectWithMaybeVarEnv combine (ea_nonEsc ea1) (ea_nonEsc ea2)
    
    -- Only need to keep one call made to each function
    -- Prefer non-recursive calls (see Note [Determining fixed type values])
    combine ci1 ci2 | ci_arity ci1 /= ci_arity ci2 = Nothing
                    | Inside <- ci_scope ci1       = Just ci2
                    | otherwise                    = Just ci1

forgetVars :: EscapeAnalysis -> [Id] -> EscapeAnalysis
forgetVars (EA { ea_nonEsc = nonEsc, ea_allVars = allVars }) xs
  = EA { ea_nonEsc  = nonEsc  `delVarEnvList` xs
       , ea_allVars = allVars `delVarSetList` xs }

occurrences :: EscapeAnalysis -> Id -> Maybe Occs
occurrences ea x
  | Just ci <- lookupVarEnv (ea_nonEsc ea) x = Just (NonEsc ci)
  | x `elemVarEnv` ea_allVars ea             = Just Esc
  | otherwise                                = Nothing

-- If none of the variables escape, return the list of variables that occur
-- along with their apparent arities and call lists
allOccurrences :: EscapeAnalysis -> [Id] -> Maybe [(Id, Maybe CallInfo)]
allOccurrences _  []       = Just []
allOccurrences ea (x : xs) = case occurrences ea x of
                               Just (NonEsc ci) -> ((x, Just ci) :) <$>
                                                   allOccurrences ea xs
                               Just Esc         -> Nothing
                               Nothing          -> ((x, Nothing) :) <$>
                                                   allOccurrences ea xs

instance Monoid EscapeAnalysis where
  mempty = emptyEscapeAnalysis
  mappend = combineEscapeAnalyses

-- Top-down data --

type CandidateEnv = IdEnv ScopeType

emptyCandidateEnv :: CandidateEnv
emptyCandidateEnv = emptyVarEnv

addCandidate :: CandidateEnv -> Id -> ScopeType -> CandidateEnv
addCandidate = extendVarEnv

addCandidates :: CandidateEnv -> [Id] -> ScopeType -> CandidateEnv
addCandidates env ids sc = extendVarEnvList env [ (id, sc) | id <- ids ]

candidateScope :: CandidateEnv -> Id -> Maybe ScopeType
candidateScope = lookupVarEnv

-- Monad --

-- | The monad underlying the escape analysis.
newtype EscM a = EscM { unEscM :: CandidateEnv -> (EscapeAnalysis, a) }

instance Monad EscM where
  return x = EscM $ \_   -> (emptyEscapeAnalysis, x)
  m >>= k  = EscM $ \env -> let (escs1, x) = unEscM m env
                                (escs2, y) = unEscM (k x) env
                                escs       = escs1 <> escs2
                            in (escs, y)

instance Functor EscM where fmap = liftM
instance Applicative EscM where { pure = return; (<*>) = ap }

instance MonadFix EscM where
  mfix f = EscM $ \env -> let pair@(_, ans) = unEscM (f ans) env
                          in pair

runEscM :: EscM a -> a
runEscM m = snd $ unEscM m emptyCandidateEnv

-- Monad operations --

getCandidates :: EscM CandidateEnv
getCandidates = EscM $ \env -> (emptyEscapeAnalysis, env)

alteringEnv :: (CandidateEnv -> CandidateEnv) -> EscM a -> EscM a
alteringEnv f m = EscM $ \env -> unEscM m (f env)

withEnv :: CandidateEnv -> EscM a -> EscM a
withEnv env m = EscM $ \_ -> unEscM m env

withoutCandidate :: Id -> EscM a -> EscM a
withoutCandidate x = alteringEnv (`delVarEnv` x)

withoutCandidates :: [Id] -> EscM a -> EscM a
withoutCandidates xs = alteringEnv (`delVarEnvList` xs)

reportCall :: Id -> Call -> ScopeType -> EscM ()
reportCall x call scope = --pprTrace "reportCall" (ppr x <+> ppr call <+> ppr scope)
                          writeAnalysis (unitCall x call scope)

captureAnalysis, readAnalysis :: EscM a -> EscM (EscapeAnalysis, a)
captureAnalysis m = EscM $ \env -> let (escs, ans) = unEscM m env
                                   in (emptyEscapeAnalysis, (escs, ans))
readAnalysis m    = EscM $ \env -> let (escs, ans) = unEscM m env
                                   in (escs, (escs, ans))

writeAnalysis :: EscapeAnalysis -> EscM ()
writeAnalysis escs = EscM $ \_ -> (escs, ())

filterAnalysis :: (EscapeAnalysis -> EscapeAnalysis) -> EscM a -> EscM a
filterAnalysis f m = EscM $ \env -> let (escs, ans) = unEscM m env
                                    in (f escs, ans)

-- Result: Marked binders --

{-
Note [Fixing type arguments]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Suppose we are contifying the polymorphic function:

    k :: forall a b. Bool -> a -> b -> [b]

Since we're contifying it, it is always tail-called from a particular context,
and that context expects a result of type [T] for some particular T. Thus we
cannot allow b to vary in the contified version of k: It must *always* return
[T] (and its final argument must be a T). Hence we must eliminate the type
parameter b and substitute T for b in the type and body of k. Supposing T is Int,
the contified k looks like

    k :: Cont# (exists a. (Bool, a, Int))

(type simplified for clarity). Note that since a doesn't appear in the original
function's return type, it is free to vary, and we construct the existential as
usual. This is important for case analyses on existential types, which produce
polymorphic join points.

Note [Determining fixed type values]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The above discussion glossed over a detail: How did we determine T to be the
constant value of b? It is true that k must always be invoked with the same
value of b *but* recursive calls will pass on the constant value, so looking
at them is unhelpful.

For instance:

    let rec { replicate :: forall a. Int -> a -> [a] -> [a]
              replicate @a n x xs =
                case n <= 0 of True  -> xs
                               False -> rep @a (n-1) (x:xs) }
    in case q of True  -> rep @Char 4 'a' []
                 False -> rep @Char 3 'b' []

The rep function is always tail-called with Char as the type argument, but in
the recursive call this is not apparent from syntax alone: The recursive call
passes a, not Char. Thus we need to differentiate between recursive calls and
"outside" calls and we need to look at an outside call to determine a. If there
are no outside calls, we would need either abstract interpretation or
unification to find the correct type, so we punt and give up on contifying.

(One is tempted to detect when a recursive call passes a tyvar that's equal to
the corresponding binder. This could solve the above case - we would know not
to use a because a is itself the binder. However, this does not cover mutual
recursion or other cases where a is passed indirectly just as the actual type
is.)
-}

data KontOrFunc = MakeKont [ArgDesc] | MakeFunc
data ArgDesc    = FixedType Type | FixedVoidArg | TyArg TyVar | ValArg Type
data MarkedVar  = Marked Var KontOrFunc

unmark :: MarkedVar -> Var
unmark (Marked var _) = var

instance HasId MarkedVar where identifier = unmark

-- | Decide whether a variable should be contified, returning the marked
-- variable and a flag (True if contifying).
markVar :: Id -> CallInfo -> (MarkedVar, Bool)
markVar x ci
  = case mkArgDescs x (idType x) ci of
      Just descs -> (Marked x (MakeKont descs), True)
      Nothing    -> (Marked x MakeFunc,         False)

-- | Decide whether a group of mutually recursive variables should be contified,
-- returning the marked variables and a flag. Either all of the variables will
-- be contified (in which case the flag is True) or none of them will.
markVars :: [Id] -> [CallInfo] -> ([MarkedVar], Bool)
markVars xs cis
  = case zipWithM (\x ci -> mkArgDescs x (idType x) ci) xs cis of
      Just descss -> ([ Marked x (MakeKont descs) | x <- xs | descs <- descss ], True)
      Nothing     -> ([ Marked x MakeFunc         | x <- xs ]                  , False)

-- | Return a constant value for each argument that needs one, given the type
-- and total arity of a function to be contified and a call made to it. Any
-- type parameters binding variables appearing in the return type must be made
-- constant, since the contified function will return to a fixed continuation in
-- which those parameters are not bound. (See Note [Determining fixed type
-- values].)
-- 
-- Returns Nothing if a type parameter needs to be fixed but the scope of the
-- given call is Inside, meaning only recursive calls were made to the function.
-- In this case, we give up on contification. (TODO: A more sophisticated
-- analysis could still find the correct type to use.)
--
-- We also don't contify if the id has rules; this is uncommon, but it does
-- happen (often due to SpecConstr), and we don't want to stop rules from firing.
--
-- It's possible the total arity is greater than the number of arrows and foralls
-- in the type, but only if the return type of the function is a type variable
-- bound in an outer scope. This is fine, because the extra arguments cannot
-- change the actual return type, so we don't need to fix (mask out) the extra
-- arguments. TODO Be more sure about this.
mkArgDescs :: Var -> Type -> CallInfo -> Maybe [ArgDesc]
mkArgDescs x _ _
  | idHasRules x = Nothing -- unlikely but possible, and contification
                           -- would likely get in the way of rule firings
mkArgDescs x ty (CI { ci_arity = arity, ci_args = call, ci_scope = scope })
  = go ty call
  where
    (_tyVars, retTy) = splitPiTyN ty arity
    freeInRetTy     = tyVarsOfType retTy
    
    go ty (Core.Type tyArg : call)
      | tyVar `elemVarSet` freeInRetTy
      = case scope of
          Outside ->
            -- Start over with new return type
            (FixedType tyArg :) <$> mkArgDescs x (substTyWith [tyVar] [tyArg] bodyTy) 
                                               (CI { ci_arity = length call
                                                   , ci_args  = call
                                                   , ci_scope = scope })
          Inside -> Nothing
      | otherwise
      = (TyArg tyVar :) <$> go bodyTy call
      where
        (tyVar, bodyTy) = splitForAllTy_maybe ty `orElse`
                            pprPanic "mkArgDescs" (ppr ty <+> ppr tyArg)
    go ty (arg : call)
      | argTy `eqType` voidPrimTy
      = (FixedVoidArg :) <$> go retTy call
      | otherwise
      = (ValArg argTy :) <$> go retTy call
      where
        (argTy, retTy) = splitFunTy_maybe ty `orElse`
                           pprPanic "mkArgDescs" (ppr ty <+> ppr arg)
                           
    go _ [] = Just []

argDescsForKontTy :: Type -> [ArgDesc]
argDescsForKontTy kontTy
  | Just ty <- isKontTy_maybe kontTy
  = go ty []
  | otherwise
  = pprPanic "argDescsForKontTy" (ppr kontTy)
  where
    go ty acc | Just (tyVar, retTy) <- isUbxExistsTy_maybe ty
              = go retTy (TyArg tyVar : acc)
              | isUnboxedTupleType ty
              , Just (_, tyArgs) <- splitTyConApp_maybe ty
              = goTuple tyArgs acc
              | otherwise
              = pprPanic "argDescsForKontTy" (ppr kontTy)
    
    goTuple [] acc       = done (FixedVoidArg : acc)
    goTuple [ty] acc     | Just (tyVar, retTy) <- isUbxExistsTy_maybe ty
                         = go retTy (TyArg tyVar : acc)
                         | otherwise
                         = done (ValArg ty : acc)
    goTuple (ty:tys) acc = goTuple tys (ValArg ty : acc)
    
    done acc = reverse acc
    
splitPiTyN :: Type -> TotalArity -> ([Maybe TyVar], Type)
splitPiTyN ty n
  | Just (tyVar, ty') <- splitForAllTy_maybe ty
  = let (args, retTy) = splitPiTyN ty' (n-1)
    in (Just tyVar : args, retTy)
  | Just (_, ty') <- splitFunTy_maybe ty
  = let (args, retTy) = splitPiTyN ty' (n-1)
    in (Nothing : args, retTy)
  | otherwise
  = ([], ty)

-- Escape analysis --

escAnalProgram :: Core.CoreProgram -> [Core.Bind MarkedVar]
escAnalProgram binds = runEscM (go binds)
  where
    go :: [Core.CoreBind] -> EscM [Core.Bind MarkedVar]
    go (bind:binds)
      = do
        (_escs, bind', binds') <- mfix $ \ ~(rec_escs_body, _, _) -> do
          (env', bind') <- escAnalBind TopLevel bind rec_escs_body
          (escs_body, binds') <- readAnalysis $ withEnv env' $ go binds
          return (escs_body, bind', binds')
        return (bind':binds')
    go [] = return []

escAnalBind :: TopLevelFlag -> Core.CoreBind -> EscapeAnalysis
            -> EscM (CandidateEnv, Core.Bind MarkedVar)
escAnalBind lvl (Core.NonRec bndr rhs) escs_body
  = do
    (escs_rhs, (rhs', lamCount)) <-
      captureAnalysis $ escAnalId bndr >> escAnalRhs rhs
      -- escAnalId looks at rules and unfoldings, which act as alternate RHSes
    let (marked, kontifying, unsat)
          | isNotTopLevel lvl
          , Just (NonEsc ci) <- occurrences escs_body bndr
          = let (marked, kontifying) = markVar bndr ci
            in (marked, kontifying, ci_arity ci < lamCount)
          | otherwise
          = (Marked bndr MakeFunc, False, False)
        escs_rhs' | not kontifying || unsat = markAllAsEscaping escs_rhs
                  | otherwise               = escs_rhs
    writeAnalysis escs_rhs'
    
    env <- getCandidates
    return (addCandidate env bndr Outside, Core.NonRec marked rhs')

escAnalBind lvl (Core.Rec pairs) escs_body
  = do
    env <- getCandidates
    let bndrs = map fst pairs
        env_rhs = addCandidates env bndrs Inside
    (unzip -> (escs_rhss, unzip -> (rhss', lamCounts)))
      <- withEnv env_rhs $ forM pairs $ \(bndr, rhs) ->
           captureAnalysis $ escAnalId bndr >> escAnalRhs rhs
    let escs = mconcat escs_rhss <> escs_body
        (pairs', kontifying, unsats)
          | isNotTopLevel lvl
          , Just occsList <- allOccurrences escs bndrs
          = let (bndrs_live, cis, rhss'_live, lamCounts_live)
                  = unzip4 [ (bndr, ci, rhs', lamCount)
                           | ((bndr, Just ci), rhs', lamCount) <-
                               zip3 occsList rhss' lamCounts ]
                (bndrs_marked, kontifying) = markVars bndrs_live cis
                isUnsat ci lamCount = ci_arity ci < lamCount
            in ( zip bndrs_marked rhss'_live, kontifying
               , zipWith isUnsat cis lamCounts_live )
          | otherwise
          = ([ (Marked bndr MakeFunc, rhs') | (bndr, rhs') <- zip bndrs rhss' ], False, repeat False)
        
        escs_rhss' | not kontifying = map markAllAsEscaping escs_rhss
                   | otherwise      = [ if unsat then markAllAsEscaping escs else escs
                                      | escs <- escs_rhss
                                      | unsat <- unsats ]

    writeAnalysis (mconcat escs_rhss' `forgetVars` bndrs)
    let env_body = addCandidates env bndrs Outside
    return (env_body, Core.Rec pairs')

-- | Analyse an expression, but don't let its top-level lambdas cause calls to
-- escape. Returns the number of lambdas ignored; if the function is partially
-- invoked, the calls escape after all.
escAnalRhs :: Core.CoreExpr -> EscM (Core.Expr MarkedVar, Int)
escAnalRhs expr
  = do
    let (bndrs, body) = Core.collectBinders expr
    body' <- withoutCandidates bndrs $ escAnalExpr body
    return $ ( Core.mkLams [ Marked bndr MakeFunc | bndr <- bndrs ] body'
             , length bndrs )

escAnalExpr :: Core.CoreExpr -> EscM (Core.Expr MarkedVar)
escAnalExpr (Core.Var x)
  = escAnalApp x []
escAnalExpr (Core.Lit lit)
  = return $ Core.Lit lit
escAnalExpr expr@(Core.App {})
  = let (func, args) = Core.collectArgs expr
    in case func of
      Core.Var fid -> escAnalApp fid args
      _ -> filterAnalysis markAllAsEscaping $ do
             func' <- escAnalExpr func
             args' <- mapM escAnalExpr args
             return $ Core.mkApps func' args'
escAnalExpr expr@(Core.Lam {})
  = do
    let (tyBndrs, valBndrs, body) = Core.collectTyAndValBinders expr
    -- Remove value binders from the environment in case of shadowing - we
    -- won't report them as free vars
    body' <- withoutCandidates valBndrs $
             -- Lambdas ruin contification, so the free vars escape
             filterAnalysis markAllAsEscaping $
             escAnalExpr body
    let bndrs' = [ Marked bndr MakeFunc | bndr <- tyBndrs ++ valBndrs ]
    return $ Core.mkLams bndrs' body'
escAnalExpr (Core.Let bind body)
  = do
    (_escs, bind', body') <- mfix $ \ ~(rec_escs_body, _, _) -> do
      (env', bind') <- escAnalBind NotTopLevel bind rec_escs_body
      (escs_body, body') <- readAnalysis $ withEnv env' $ escAnalExpr body
      return (escs_body, bind', body')
    return $ Core.Let bind' body'
escAnalExpr (Core.Case scrut bndr ty alts)
  = do
    scrut' <- filterAnalysis markAllAsEscaping $ escAnalExpr scrut
    alts' <- withoutCandidate bndr $ forM alts $ \(con, bndrs, rhs) -> do
      rhs' <- withoutCandidates bndrs $ escAnalExpr rhs
      return (con, map (`Marked` MakeFunc) bndrs, rhs')
    return $ Core.Case scrut' (Marked bndr MakeFunc) ty alts'
escAnalExpr (Core.Cast expr co)
  -- A call under a cast isn't a tail call, so pretend the free vars escape
  = (`Core.Cast` co) <$> filterAnalysis markAllAsEscaping (escAnalExpr expr)
escAnalExpr (Core.Tick ti expr)
  = Core.Tick ti <$> escAnalExpr expr
escAnalExpr (Core.Type ty)
  = return $ Core.Type ty
escAnalExpr (Core.Coercion co)
  = return $ Core.Coercion co

escAnalApp :: Id -> [Core.CoreExpr] -> EscM (Core.Expr MarkedVar)
escAnalApp fid args
  = do
    env <- getCandidates
    let candidacy = candidateScope env fid
    whenIsJust candidacy $ \scope -> reportCall fid args scope
    args' <- filterAnalysis markAllAsEscaping $ mapM escAnalExpr args
    return $ Core.mkApps (Core.Var fid) args'

-- Analyse unfolding and rules
escAnalId :: Id -> EscM ()
escAnalId x
  | isId x
  = do
    mapM_ escAnalRule (idCoreRules x)
    escAnalUnfolding (idUnfolding x)
  | otherwise
  = return ()

escAnalRule :: Core.CoreRule -> EscM ()
escAnalRule (Core.Rule { Core.ru_bndrs = bndrs, Core.ru_rhs = rhs })
  = void $ withoutCandidates bndrs $ escAnalExpr rhs
escAnalRule _
  = return ()

escAnalUnfolding :: Core.Unfolding -> EscM ()
escAnalUnfolding (Core.CoreUnfolding { Core.uf_tmpl = rhs  }) = void $ escAnalExpr rhs
escAnalUnfolding (Core.DFunUnfolding { Core.df_args = args }) = mapM_ escAnalExpr args
escAnalUnfolding _                                            = return ()

----------------------------------------
-- Phase 2: Translate to Sequent Core --
----------------------------------------

-- Continuation calling conventions --

-- | The protocol for invoking a given let-bound continuation. Currently all
-- such continuations must be invoked using a jump, so @ByJump@ is the only
-- constructor, but we must still keep track of which arguments are fixed and
-- should be omitted when converting a function call.
newtype KontCallConv = ByJump [ArgDesc]

-- Auxiliary datatype for idToKontId
data KontType = KTExists TyVar KontType | KTTuple [KontType] | KTType Type

-- | Convert an id to the id of a parameterized continuation, changing its type
-- according to the given calling convention.
idToJoinId :: Id -> KontCallConv -> JoinId
idToJoinId p conv@(ByJump descs)
  = p `setIdType` kontTypeToType (go (idType p) descs)
      `setIdInfo` (idInfo p `setArityInfo` valArgCount)
      `tweakUnfolding` conv
  where
    valArgCount = count (\case { ValArg {} -> True; _ -> False }) descs
    
    go _  [] = KTTuple []
    go ty (FixedType tyArg : descs')
      | Just (tyVar, ty') <- splitForAllTy_maybe ty
      = go (substTyWith [tyVar] [tyArg] ty') descs'
    go ty (FixedVoidArg : descs')
      | Just (argTy, retTy) <- splitFunTy_maybe ty
      = assert (argTy `eqType` voidPrimTy) $
        go retTy descs'
    go ty (TyArg tyVar : descs')
      | Just (tyVar', ty') <- splitForAllTy_maybe ty
      = assert (tyVar == tyVar') $
        KTExists tyVar (go ty' descs')
    go ty (ValArg argTy : descs')
      | Just (argTy', retTy) <- splitFunTy_maybe ty
      = assert (argTy `eqType` argTy') $
        argTy `consKT` go retTy descs'
    go _ _
      = pprPanic "idToJoinId" (pprBndr LetBind p $$ ppr descs)

    kontTypeToType :: KontType -> Type
    kontTypeToType = mkKontTy . go
      where 
        go (KTExists bndr kty) = mkUbxExistsTy bndr (go kty)
        go (KTTuple ktys)      = mkTupleTy UnboxedTuple (map go ktys)
        go (KTType ty)         = ty

    consKT :: Type -> KontType -> KontType
    ty `consKT` kty@KTExists {} = KTTuple [KTType ty, kty]
    ty `consKT` (KTTuple ktys)  = KTTuple (KTType ty : ktys)
    ty `consKT` (KTType ty2)    = KTTuple [KTType ty, KTType ty2]

-- | Remove from a list the elements corresponding to fixed arguments according
-- to the given calling convention.
removeFixedArgs :: [a] -> KontCallConv -> [a]
removeFixedArgs args (ByJump descs)
  = [ arg | (arg, desc) <- zip args descs, keep desc ]
  where
    keep (FixedType _) = False
    keep FixedVoidArg  = False
    keep _             = True

-- | Alter an id's unfolding according to the given calling convention.
tweakUnfolding :: Id -> KontCallConv -> Id
tweakUnfolding id (ByJump descs)
  = case unf of
      Core.CoreUnfolding {} ->
        let expr = Core.uf_tmpl unf
            env = initFromCoreEnvForExpr expr
            (env', bndrs, body) = etaExpandForJoinBody env descs expr
            bndrs' | noValArgs = bndrs ++ [voidPrimId]
                   | otherwise = bndrs
            expr' = substExpr (text "tweakUnfolding") (fce_subst env') (Core.mkLams bndrs' body)
            arity' = valArgCount `min` 1
        in id `setIdUnfolding`
             mkCoreUnfolding (Core.uf_src unf) (Core.uf_is_top unf) (simpleOptExpr expr')
                             arity' (fixGuid (Core.uf_guidance unf))
      _ -> id
  where
    unf = realIdUnfolding id
    
    isValArgDesc (ValArg {}) = True
    isValArgDesc _           = False
    
    valArgCount = count isValArgDesc descs
    noValArgs = valArgCount == 0
    
    fixGuid guid@(Core.UnfIfGoodArgs { Core.ug_args = args })
      | noValArgs
      = guid { Core.ug_args = [0] } -- We keep a single Void# lambda in the unfolding
      | otherwise
      = guid { Core.ug_args = fixArgs args descs }
    fixGuid guid = guid
    
    fixArgs [] [] = []
    fixArgs [] (ValArg _ : _)
      = warnPprTrace True __FILE__ __LINE__
          (text "Out of value discounts" $$
           text "Unfolding:" <+> ppr unf $$
           text "Arg descs:" <+> ppr descs)
        []
    fixArgs args []
      = warnPprTrace True __FILE__ __LINE__
          (text "Leftover arg discounts:" <+> ppr args $$
           text "Unfolding:" <+> ppr unf $$
           text "Arg descs:" <+> ppr descs)
        []
    fixArgs (arg:args) (ValArg _ : descs)
      = arg : fixArgs args descs
    fixArgs (_:args) (FixedVoidArg : descs)
      = fixArgs args descs
    fixArgs args (_ : descs) -- Type argument (fixed or variable)
      = fixArgs args descs

-- Environment for Core -> Sequent Core translation --

data FromCoreEnv
  = FCE { fce_subst :: Subst
        , fce_boundKonts :: IdEnv KontCallConv }

initFromCoreEnv :: FromCoreEnv
initFromCoreEnv = FCE { fce_subst = emptySubst
                      , fce_boundKonts = emptyVarEnv }

initFromCoreEnvForExpr :: Core.CoreExpr -> FromCoreEnv
initFromCoreEnvForExpr expr = initFromCoreEnv { fce_subst = freeVarSet }
  where
    freeVarSet = mkSubst (mkInScopeSet (Core.exprFreeVars expr))
                   emptyVarEnv emptyVarEnv emptyVarEnv

bindAsJoin :: FromCoreEnv -> JoinId -> KontCallConv -> FromCoreEnv
bindAsJoin env p conv
  = env { fce_boundKonts = extendVarEnv (fce_boundKonts env) p conv }

bindAsJoins :: FromCoreEnv -> [(JoinId, KontCallConv)] -> FromCoreEnv
bindAsJoins env ps = foldr (\(p, conv) env' -> bindAsJoin env' p conv) env ps

kontCallConv :: FromCoreEnv -> Var -> Maybe KontCallConv
kontCallConv env var = lookupVarEnv (fce_boundKonts env) var

fromCoreExpr :: FromCoreEnv -> Core.Expr MarkedVar -> SeqCoreKont
                            -> SeqCoreCommand
fromCoreExpr env expr (fs, end) = go [] env expr fs end
  where
    go :: [SeqCoreBind] -> FromCoreEnv -> Core.Expr MarkedVar
       -> [SeqCoreFrame] -> SeqCoreEnd -> SeqCoreCommand
    go binds env expr fs end = case expr of
      Core.Var x         -> goApp x []
      Core.Lit l         -> done $ Lit l
      Core.App {}         | (Core.Var x, args) <- Core.collectArgs expr
                         -> goApp x args
      Core.App e1 e2     ->
        let e2' = fromCoreExprAsTerm env e2
        in go binds env e1 (App e2' : fs) end
      Core.Lam x e       -> done $ fromCoreLams env x e
      Core.Let bs e      ->
        let (env', bs')   = fromCoreBind env (Just (fs, end)) bs
        in go (bs' : binds) env' e fs end
      Core.Case e (Marked x _) _ as
        -- If the continuation is just a return, copy it into the branches
        | null fs, Return {} <- end -> go binds env e [] end'
        -- Otherwise be more careful. In the simplifier, we get clever and
        -- split the continuation into a duplicable part and a non-duplicable
        -- part (see splitDupableKont); for now just share the whole thing.
        | otherwise -> 
        let join_arg  = mkKontArgId (idType x')
            join_rhs  = Join [join_arg] (Eval (Var join_arg) [] end')
            join_ty   = mkKontTy (mkTupleTy UnboxedTuple [idType x'])
            join_bndr = mkInlinableJoinBinder join_ty
            join_bind = NonRec (BindJoin join_bndr join_rhs)
        in go (join_bind : binds) env e [] (Case join_arg [Alt DEFAULT [] (Jump [Var join_arg] join_bndr)])
        where
          (subst_rhs, x') = substBndr subst x
          env_rhs = env { fce_subst = subst_rhs }
          end'    = Case x' $ map (fromCoreAlt env_rhs (fs, end)) as
      Core.Coercion co   -> done $ Coercion (substCo subst co)
      Core.Cast e co     -> go binds env e (Cast (substCo subst co) : fs) end
      Core.Tick ti e     -> go binds env e (Tick (substTickish subst ti) : fs) end
      Core.Type t        -> done $ Type (substTy subst t)
      where
        subst = fce_subst env
        done term = addLets (reverse binds) $ Eval term fs end
        
        goApp x args = case conv_maybe of
          Just conv@(ByJump descs)
            -> assert (length args == length descs) $
               doneJump (removeFixedArgs args' conv) p
          Nothing
            -> doneEval (Var x') (map App args' ++ fs) end
          where
            x' = substIdOcc subst x
            args' = map (\e -> fromCoreExprAsTerm env e) args
            conv_maybe = kontCallConv env x'
            p = let Just conv = conv_maybe in idToJoinId x' conv
            
            doneEval v fs e = addLets (reverse binds) $ Eval v fs e
            doneJump vs j = foldr Let (Jump vs j) (reverse binds)

fromCoreLams :: FromCoreEnv -> MarkedVar -> Core.Expr MarkedVar
                            -> SeqCoreTerm
fromCoreLams env (Marked x _) expr
  = mkLambdas xs' body'
  where
    (xs, body) = Core.collectBinders expr
    bodyComm = fromCoreExpr env' body ([], Return)
    body' = mkCompute ty bodyComm
    (subst', xs') = substBndrs (fce_subst env) (x : map unmark xs)
    env' = env { fce_subst = subst' }
    ty  = substTy subst' (Core.exprType (unmarkExpr body))

fromCoreExprAsTerm :: FromCoreEnv -> Core.Expr MarkedVar -> SeqCoreTerm
fromCoreExprAsTerm env expr
  = mkCompute ty body
  where
    body = fromCoreExpr env expr ([], Return)
    subst = fce_subst env
    ty = substTy subst (Core.exprType (unmarkExpr expr))

fromCoreExprAsJoin :: FromCoreEnv -> SeqCoreKont -> [ArgDesc]
                   -> Core.Expr MarkedVar
                   -> SeqCoreJoin
fromCoreExprAsJoin env kont descs expr
  = --pprTrace "fromCoreExprAsJoin" (ppr descs $$ ppr bndrs $$ ppr bndrs_final)
    Join bndrs comm
  where
    -- Eta-expand the body *before* translating to Sequent Core so that the
    -- parameterized continuation has all the arguments it should get
    (env', bndrs, etaBody) = etaExpandForJoinBody env descs expr
    comm = fromCoreExpr env' etaBody kont

etaExpandForJoinBody :: HasId b
                     => FromCoreEnv -> [ArgDesc] -> Core.Expr b
                     -> (FromCoreEnv, [Var], Core.Expr b)
etaExpandForJoinBody env descs expr
  = (env', bndrs_final, etaBody)
  where
    subst = fce_subst env

    -- Calculate outer binders (existing ones from expr, minus fixed args)
    (bndrs, body) = collectNBinders (length descs) expr
    bndrs_unmarked = identifiers bndrs
    (subst', bndr_maybes) = mapAccumL doBndr subst (zip bndrs_unmarked descs)
    bndrs' = catMaybes bndr_maybes

    -- Calculate eta-expanding binders and arguments
    extraArgs = drop (length bndrs) descs -- will need to eta-expand with these
    (subst'', unzip -> (etaBndr_maybes, etaArgs))
      = mapAccumL mkEtaBndr subst' (zip [1..] extraArgs)
    etaBndrs = catMaybes etaBndr_maybes
    
    env' = env { fce_subst = subst'' }
    bndrs_final = bndrs' ++ etaBndrs
    etaBody | null extraArgs = body
            | otherwise      = Core.mkApps body etaArgs
    
    -- Process a binder, possibly dropping it, and return a new subst
    doBndr :: Subst -> (Var, ArgDesc) -> (Subst, Maybe Var)
    doBndr subst (bndr, FixedType ty)
      = (CoreSubst.extendTvSubst subst bndr (substTy subst ty), Nothing)
    doBndr subst (bndr, FixedVoidArg)
      -- Usually, a binder for a Void# is dead, but in case it's not, take the
      -- argument to be void#. Note that, under the let/app invariant, any
      -- argument of unlifted type must be ok-for-speculation, and any
      -- ok-for-speculation expression of Void# is equal to void# (it can't be
      -- _|_ or have side effects or possible errors and still be OFS; it could
      -- still be case x +# y of z -> void#, but then we can eliminate the case).
      -- So this is always correct.
      = (extendSubstWithVar subst bndr voidPrimId, Nothing)
    doBndr subst (bndr, TyArg tyVar)
      = (subst'', Just bndr')
      where
        (subst', bndr') = substBndr subst bndr
        -- Further ArgInfos may refer to tyVar, so we need to substitute to get
        -- the right types for generated arguments (when eta-expanding).
        subst'' = CoreSubst.extendTvSubst subst' tyVar (mkTyVarTy bndr')
    doBndr subst (bndr, ValArg _)
      = (subst', Just bndr')
      where
        (subst', bndr') = substBndr subst bndr

    -- From an ArgDesc, generate an argument to apply and (possibly) a parameter
    -- to the eta-expanded function
    mkEtaBndr :: Subst -> (Int, ArgDesc) -> (Subst, (Maybe Var, Core.Expr b))
    mkEtaBndr subst (_, FixedType ty)
      = (subst, (Nothing, Core.Type (substTy subst ty)))
    mkEtaBndr subst (_, FixedVoidArg)
      = (subst, (Nothing, Core.Var voidPrimId))
    mkEtaBndr subst (_, TyArg tyVar)
      = (subst', (Just tv', Core.Type (mkTyVarTy tv')))
      where
        (subst', tv') = substBndr subst tyVar
    mkEtaBndr subst (n, ValArg ty)
      = (subst', (Just x, Core.Var x))
      where
        (subst', x) = freshEtaId n subst ty
        
    collectNBinders :: TotalArity -> Core.Expr b -> ([b], Core.Expr b)
    collectNBinders = go []
      where
        go acc 0 e              = (reverse acc, e)
        go acc n (Core.Lam x e) = go (x:acc) (n-1) e
        go acc _ e              = (reverse acc, e)

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: FromCoreEnv -> SeqCoreKont -> Core.Alt MarkedVar
            -> SeqCoreAlt
fromCoreAlt env kont (ac, bs, e)
  = let (subst', bs') = substBndrs (fce_subst env) (map unmark bs)
        e' = fromCoreExpr (env { fce_subst = subst' }) e kont
    in Alt ac bs' e'

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: FromCoreEnv -> Maybe SeqCoreKont -> Core.Bind MarkedVar
             -> (FromCoreEnv, SeqCoreBind)
fromCoreBind (env@FCE { fce_subst = subst }) kont_maybe bind =
  case bind of
    Core.NonRec (Marked x mark) rhs -> (env_final, NonRec pair')
      where
        (subst', x') = substBndr subst x
        env' = env { fce_subst = subst' }
        env_final | MakeKont _ <- mark = bindAsJoin env' x' conv
                  | otherwise          = env'
        (~(Just conv), pair') = fromCoreBindPair env kont_maybe x' mark rhs

    Core.Rec pairs -> (env_final, Rec pairs_final)
      where
        xs = map (unmark . fst) pairs
        (subst', xs') = assert (all isId xs) $ substRecBndrs subst xs
        env' = env { fce_subst = subst' }
        pairs' = [ fromCoreBindPair env_final kont_maybe x' mark rhs
                 | (Marked _ mark, rhs) <- pairs
                 | x' <- xs' ]
        env_final = bindAsJoins env' [ (binderOfPair pair, conv)
                                     | (Just conv, pair) <- pairs' ]
        pairs_final = map snd pairs'

fromCoreBindPair :: FromCoreEnv -> Maybe SeqCoreKont -> Var -> KontOrFunc
                 -> Core.Expr MarkedVar -> (Maybe KontCallConv, SeqCoreBindPair)
fromCoreBindPair env kont_maybe x mark rhs
  = case mark of
      MakeKont descs -> let Just kont = kont_maybe
                            join = fromCoreExprAsJoin env kont descs rhs
                        in (Just (ByJump descs),
                            BindJoin (idToJoinId x (ByJump descs)) join)
      MakeFunc       -> (Nothing, BindTerm x $ fromCoreExprAsTerm env rhs)

fromCoreBinds :: [Core.Bind MarkedVar] -> [SeqCoreBind]
fromCoreBinds = snd . mapAccumL (\env -> fromCoreBind env Nothing) initFromCoreEnv

------------------------------------------------
-- Public interface for Sequent Core --> Core --
------------------------------------------------
    
-- | Translates a command into Core.
commandToCoreExpr :: Type -> SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr retTy comm
  = case comm of
      Let bind comm'   -> Core.mkCoreLet (bindToCore (Just retTy) bind)
                                         (commandToCoreExpr retTy comm')
      Eval term fs end -> kontToCoreExpr retTy (fs, end) (termToCoreExpr term)
      Jump args j      -> Core.mkCoreApps (Core.Var (joinIdToCore retTy j))
                                          (map termToCoreExpr args ++ extraArgs)
        where
          extraArgs | all isTypeArg args = [ Core.Var voidPrimId ]
                    | otherwise          = []

-- | Translates a term into Core.
termToCoreExpr :: SeqCoreTerm -> Core.CoreExpr
termToCoreExpr val =
  case val of
    Lit l        -> Core.Lit l
    Var x        -> Core.Var x
    Lam x t      -> Core.Lam x (termToCoreExpr t)
    Type t       -> Core.Type t
    Coercion co  -> Core.Coercion co
    Compute kb c -> commandToCoreExpr kb c

-- | Translates a join point into Core.
joinToCoreExpr :: Type -> SeqCoreJoin -> Core.CoreExpr
joinToCoreExpr = joinToCoreExpr' NonRecursive

joinToCoreExpr' :: RecFlag -> Type -> SeqCoreJoin -> Core.CoreExpr
joinToCoreExpr' recFlag retTy (Join xs comm)
  = Core.mkCoreLams (maybeOneShots xs') (commandToCoreExpr retTy comm)
  where
    xs'   | null xs   = [ voidArgId ]
          | otherwise = xs
    maybeOneShots xs | isNonRec recFlag = map setOneShotLambdaIfId xs
                     | otherwise        = xs
    setOneShotLambdaIfId x | isId x = setOneShotLambda x
                           | otherwise = x

-- | Functional representation of expression contexts in Core.
type CoreContext = Core.CoreExpr -> Core.CoreExpr

-- | Translates a continuation into a function that will wrap a Core expression
-- with a fragment of context (an argument to apply to, a case expression to
-- run, etc.).
kontToCoreExpr :: Type -> SeqCoreKont -> CoreContext
kontToCoreExpr retTy (fs, end) =
  foldr (flip (.)) (endToCoreExpr retTy end) (map frameToCoreExpr fs)

frameToCoreExpr :: SeqCoreFrame -> CoreContext
frameToCoreExpr k =
  case k of
    App  {- expr -} v   -> \e -> Core.mkCoreApp e (termToCoreExpr v)
    Cast {- expr -} co  -> \e -> Core.Cast e co
    Tick ti {- expr -}  -> \e -> Core.Tick ti e

endToCoreExpr :: Type -> SeqCoreEnd -> CoreContext
endToCoreExpr retTy k =
  case k of
    Case {- expr -} b as -> \e -> Core.Case e b retTy (map (altToCore retTy) as)
    Return               -> \e -> e

-- | Convert a join id to its Core form. For instance, given a return type of 
--   String,
--     @j :: Cont# (exists# a. (# a, Int, Char #))
--   becomes
--     @j :: forall a. a -> Int -> Char -> String
joinIdToCore :: Type -> JoinId -> Id
joinIdToCore retTy j = maybeAddArity $ j `setIdType` kontTyToCoreTy argTy retTy
  where
    argTy = isKontTy_maybe (idType j) `orElse` pprPanic "joinIdToCore" (pprBndr LetBind j)
    maybeAddArity j' | idArity j' == 0 = j' `setIdInfo` (idInfo j' `setArityInfo` 1)
                     | otherwise       = j'

kontTyToCoreTy :: Type -> Type -> Type
kontTyToCoreTy ty retTy
  | Just (a, body) <- isUbxExistsTy_maybe ty
  = mkForAllTy a (kontTyToCoreTy body retTy)
  | isUnboxedTupleType ty
  = let (_, args) = splitTyConApp ty
    in if | null args -> mkFunTy voidPrimTy retTy
          | Just (a, ty') <- isUbxExistsTy_maybe (last args)
                      -> mkFunTys (init args) 
                                  (mkForAllTy a (kontTyToCoreTy ty' retTy))
          | otherwise -> mkFunTys args retTy
  | otherwise
  = pprPanic "kontArgsTyToCoreTy" (ppr ty)

-- | Translates a binding into Core.
bindToCore :: Maybe Type -> SeqCoreBind -> Core.CoreBind
bindToCore retTy_maybe bind =
  case bind of
    NonRec pair -> Core.NonRec b v
      where (b, v) = bindPairToCore retTy_maybe NonRecursive pair
    Rec pairs   -> Core.Rec (map (bindPairToCore retTy_maybe Recursive) pairs)

bindPairToCore :: Maybe Type -> RecFlag -> SeqCoreBindPair
               -> (Core.CoreBndr, Core.CoreExpr)
bindPairToCore retTy_maybe recFlag pair =
  case pair of
    BindTerm b v -> (b, termToCoreExpr v)
    BindJoin b pk -> (joinIdToCore retTy b, joinToCoreExpr' recFlag retTy pk)
      where
        retTy = retTy_maybe `orElse` panic "bindPairToCore: top-level cont"

-- | Translates a list of top-level bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore binds = map (bindToCore Nothing) binds

altToCore :: Type -> SeqCoreAlt -> Core.CoreAlt
altToCore retTy (Alt ac bs c) = (ac, bs, commandToCoreExpr retTy c)

--------------------------------------------------------------
-- Public interface for operations going in both directions --
--------------------------------------------------------------

-- | Take an operation on Sequent Core terms and perform it on Core expressions
onCoreExpr :: (SeqCoreTerm -> SeqCoreTerm) -> (Core.CoreExpr -> Core.CoreExpr)
onCoreExpr f = termToCoreExpr . f . termFromCoreExpr

-- | Take an operation on Core expressions and perform it on Sequent Core terms
onSequentCoreTerm :: (Core.CoreExpr -> Core.CoreExpr) -> (SeqCoreTerm -> SeqCoreTerm)
onSequentCoreTerm f = termFromCoreExpr . f . termToCoreExpr

----------------
-- Miscellany --
----------------

instance Outputable EscapeAnalysis where
  ppr (EA { ea_nonEsc = nonEsc, ea_allVars = allVars })
    = text "non-escaping:" <+> ppr (mapVarEnv ci_arity nonEsc) $$
      text "    escaping:" <+> ppr (allVars `minusVarEnv` nonEsc)

instance Outputable ScopeType where
  ppr Inside = text "inside scope"
  ppr Outside = text "outside scope"
  
instance Outputable Occs where
  ppr Esc = text "esc"
  ppr (NonEsc ci) = text "arity" <+> int (ci_arity ci)

instance Outputable KontOrFunc where
  ppr MakeFunc = text "func"
  ppr (MakeKont _) = text "cont"

instance Outputable MarkedVar where
  ppr (Marked var mark) = ppr var <+> brackets (ppr mark)

instance OutputableBndr MarkedVar where
  pprBndr site (Marked var MakeFunc) = pprBndr site var
  pprBndr site (Marked var mark) = pprBndr site var <+> brackets (ppr mark)
  pprPrefixOcc (Marked var _) = pprPrefixOcc var
  pprInfixOcc  (Marked var _) = pprInfixOcc  var

instance Outputable ArgDesc where
  ppr (FixedType ty) = text "fixed type:" <+> ppr ty
  ppr FixedVoidArg   = text "fixed void#"
  ppr (TyArg tyVar)  = text "type arg:" <+> pprBndr LambdaBind tyVar
  ppr (ValArg ty)    = text "arg of type" <+> ppr ty

mapCore :: (a -> b) -> Core.Expr a -> Core.Expr b
mapCore f = go
  where
    go (Core.Var x)       = Core.Var x
    go (Core.Lit l)       = Core.Lit l
    go (Core.App e1 e2)   = Core.App (go e1) (go e2)
    go (Core.Lam b e)     = Core.Lam (f b) (go e)
    go (Core.Let bind e)  = Core.Let (goBind bind) (go e)
    go (Core.Case scrut bndr ty alts)
                          = Core.Case (go scrut) (f bndr) ty
                              [ (con, map f bndrs, go rhs)
                              | (con, bndrs, rhs) <- alts ]
    go (Core.Cast e co)   = Core.Cast (go e) co
    go (Core.Tick ti e)   = Core.Tick ti (go e)
    go (Core.Type ty)     = Core.Type ty
    go (Core.Coercion co) = Core.Coercion co
    
    goBind (Core.NonRec bndr rhs) = Core.NonRec (f bndr) (go rhs)
    goBind (Core.Rec pairs)       = Core.Rec [ (f bndr, go rhs)
                                             | (bndr, rhs) <- pairs ]

unmarkExpr :: Core.Expr MarkedVar -> Core.CoreExpr
unmarkExpr = mapCore unmark

-- copied from CoreArity
freshEtaId :: Int -> Subst -> Type -> (Subst, Id)
freshEtaId n subst ty
      = (subst', eta_id')
      where
        ty'     = substTy subst ty
        eta_id' = uniqAway (substInScope subst) $
                  mkSysLocal (fsLit "eta") (mkBuiltinUnique n) ty'
        subst'  = extendInScope subst eta_id'           

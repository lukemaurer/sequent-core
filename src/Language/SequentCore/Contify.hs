{-# LANGUAGE CPP, LambdaCase, ParallelListComp, ViewPatterns #-}

-- | 
-- Module      : Language.SequentCore.Contify
-- Description : Contification pass
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Pass that turns as many functions as possible into join points.

module Language.SequentCore.Contify ( runContify, contifyInTerm ) where

import {-# SOURCE #-} Language.SequentCore.Translate

import Language.SequentCore.FVs
import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import BasicTypes ( Arity, TopLevelFlag(..), TupleSort(..)
                  , isNotTopLevel )
import CoreSubst
import CoreUnfold
import qualified CoreSyn as Core
import FastString
import Id
import IdInfo
import Maybes
import MkId
import Outputable hiding ( (<>) )
import Type hiding ( substTy )
import TysPrim
import TysWiredIn
import UniqFM     ( intersectUFM_C )
import Unique
import Util       ( count, debugIsOn )
import VarEnv
import VarSet

import Control.Applicative
import Control.Exception    ( assert )
import Control.Monad
import Control.Monad.Fix
import Data.List
import Data.Monoid

#define ASSERT(e)      if debugIsOn && not (e) then (assertPanic __FILE__ __LINE__) else
#define ASSERT2(e,msg) if debugIsOn && not (e) then (assertPprPanic __FILE__ __LINE__ (msg)) else
#define WARN( e, msg ) (warnPprTrace (e) __FILE__ __LINE__ (msg)) $
#define MASSERT(e)     ASSERT(e) return ()

runContify :: SeqCoreProgram -> SeqCoreProgram
runContify = cfyInTopLevelBinds . escAnalProgram

contifyInTerm :: SeqCoreTerm -> SeqCoreTerm
contifyInTerm term = cfyInTerm env (runEscM $ escAnalTerm term)
  where
    env = initCfyEnvForTerm term

----------------------------------
-- Phase 1: Escape-analyse code --
----------------------------------

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
type Call = [SeqCoreArg]
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

data KontOrFunc = MakeKont [ArgDesc] | Keep
data ArgDesc    = FixedType Type | FixedVoidArg | TyArg TyVar | ValArg Type
data MarkedVar  = Marked Var KontOrFunc

isValArgDesc :: ArgDesc -> Bool
isValArgDesc (ValArg {}) = True
isValArgDesc _           = False

removeFixedArgs :: [a] -> [ArgDesc] -> [a]
removeFixedArgs args descs
  = [ arg | (arg, desc) <- zip args descs, keep desc ]
  where
    keep (FixedType _) = False
    keep FixedVoidArg  = False
    keep _             = True

isKeep :: KontOrFunc -> Bool
isKeep Keep = True
isKeep _    = False

unmark :: MarkedVar -> Var
unmark (Marked var _) = var

instance HasId MarkedVar where identifier = unmark

-- | Decide whether a variable should be contified, returning the marked
-- variable and a flag (True if contifying).
markVar :: Id -> CallInfo -> (MarkedVar, Bool)
markVar x ci
  = case mkArgDescs x (idType x) ci of
      Just descs -> (Marked x (MakeKont descs), True)
      Nothing    -> (Marked x Keep,             False)

-- | Decide whether a group of mutually recursive variables should be contified,
-- returning the marked variables and a flag. Either all of the variables will
-- be contified (in which case the flag is True) or none of them will.
markVars :: [Id] -> [CallInfo] -> ([MarkedVar], Bool)
markVars xs cis
  = case zipWithM (\x ci -> mkArgDescs x (idType x) ci) xs cis of
      Just descss -> ([ Marked x (MakeKont descs) | x <- xs | descs <- descss ], True)
      Nothing     -> ([ Marked x Keep             | x <- xs ]                  , False)

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
    
    go ty (Type tyArg : call)
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

escAnalProgram :: SeqCoreProgram -> [Bind MarkedVar]
escAnalProgram binds = runEscM (go binds)
  where
    go :: [SeqCoreBind] -> EscM [Bind MarkedVar]
    go (bind:binds)
      = do
        (_escs, bind', binds') <- mfix $ \ ~(rec_escs_body, _, _) -> do
          (env', bind') <- escAnalBind TopLevel bind rec_escs_body
          (escs_body, binds') <- readAnalysis $ withEnv env' $ go binds
          return (escs_body, bind', binds')
        return (bind':binds')
    go [] = return []

escAnalBind :: TopLevelFlag -> SeqCoreBind -> EscapeAnalysis
            -> EscM (CandidateEnv, Bind MarkedVar)
escAnalBind lvl (NonRec (BindTerm bndr rhs)) escs_body
  = do
    (escs_rhs, (rhs', lamCount)) <-
      captureAnalysis $ escAnalId bndr >> escAnalRhsTerm rhs
      -- escAnalId looks at rules and unfoldings, which act as alternate RHSes
    let (marked, rhs_escapes)
          | isNotTopLevel lvl
          , Just (NonEsc ci) <- occurrences escs_body bndr
          = let (marked, kontifying) = markVar bndr ci
            in (marked, not kontifying || ci_arity ci /= lamCount)
              -- Note [Contifying inexactly-applied functions]
          | otherwise
          = (Marked bndr Keep, True)
        escs_rhs' | rhs_escapes = markAllAsEscaping escs_rhs
                  | otherwise   = escs_rhs
    writeAnalysis escs_rhs'
    
    env <- getCandidates
    return (addCandidate env bndr Outside, NonRec (BindTerm marked rhs'))

escAnalBind _ (NonRec (BindJoin bndr rhs)) _
  = do
    rhs' <- escAnalId bndr >> escAnalJoin rhs
    env <- getCandidates
    return (env, NonRec (BindJoin (Marked bndr Keep) rhs'))

escAnalBind lvl (Rec pairs) escs_body
  = do
    env <- getCandidates
    let (termPairs, joinPairs) = partitionBindPairs pairs
        termBndrs = map fst termPairs
        joinBndrs = map fst joinPairs
        bndrs     = map binderOfPair pairs
        env_rhs   = addCandidates env termBndrs Inside
    (unzip -> (escs_termRhss, unzip -> (termRhss', lamCounts)))
      <- withEnv env_rhs $ forM termPairs $ \(bndr, term) ->
           captureAnalysis $ escAnalId bndr >> escAnalRhsTerm term
    (unzip -> (escs_joinRhss, joinRhss'))
      <- withEnv env_rhs $ forM joinPairs $ \(bndr, join) ->
           captureAnalysis $ escAnalId bndr >> escAnalJoin join
    let escs = mconcat escs_termRhss <> mconcat escs_joinRhss <> escs_body
        (termPairs', kontifying, escape_flags)
          | isNotTopLevel lvl
          , Just occsList <- allOccurrences escs termBndrs
          = let (bndrs_live, cis, rhss'_live, lamCounts_live)
                  = unzip4 [ (bndr, ci, rhs', lamCount)
                           | ((bndr, Just ci), rhs', lamCount) <-
                               zip3 occsList termRhss' lamCounts ]
                (bndrs_marked, kontifying) = markVars bndrs_live cis
                escapes ci lamCount = ci_arity ci /= lamCount
            in ( zipWith BindTerm bndrs_marked rhss'_live, kontifying
               , zipWith escapes cis lamCounts_live )
          | otherwise
          = ([ BindTerm (Marked bndr Keep) rhs' | bndr <- termBndrs | rhs' <- termRhss' ], False, repeat True)
        joinPairs'
          = [ BindJoin (Marked bndr Keep) rhs' | bndr <- joinBndrs | rhs' <- joinRhss' ]
        
        escs_termRhss' | not kontifying = map markAllAsEscaping escs_termRhss
                       | otherwise      = [ if rhs_escapes then markAllAsEscaping escs else escs
                                          | escs <- escs_termRhss
                                          | rhs_escapes <- escape_flags ]

    writeAnalysis $ (mconcat escs_termRhss' <> mconcat escs_joinRhss) `forgetVars` bndrs
    let env_body = addCandidates env termBndrs Outside
    return (env_body, Rec (termPairs' ++ joinPairs'))


{-
Note [Contifying inexactly-applied functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If a function is consistently tail-called, but with the "wrong" number of
arguments, then it can still be contified but its body is an escaping context.
Consider (assuming all calls are tail calls):

    let k = \x -> ...
        h = \y z ->
              let j = \w -> ... k (w + z) ... in ... j y ...
    in ... e ...

Consider three cases for e:
  * e = h a b: Here we will contify all three functions: h is consistently
    tail-called *with two arguments*, so its body is a tail context for k;
    similarly, j is consistently tail-called with one argument, so the call to
    k is a true tail call.
  * e = h a: Since h a is a lambda, its body is an escaping context. Thus h is
    contified (as a continuation of one argument), as is j, but k is not.
  * e = h a b c: To contify h, we will first need to eta-expand it:

        h = \y z eta ->
              (let j = \w -> ... k (w + z) ... in ... j y ...) eta

    (We don't bother moving the argument inward; phase 2 will do that.) Now
    k (w + z) is clearly not a tail call, so again h and j are contified but k
    is not.

Crucially, escape analysis is a bottom-up pass, so we can in fact decide on j
and h first, thus influencing the decision for k.
-}

-- | Analyse a term, but don't let its top-level lambdas cause calls to
-- escape. Returns the number of lambdas ignored; if the function is partially
-- applied or oversaturated, the calls escape after all.
escAnalRhsTerm :: SeqCoreTerm -> EscM (Term MarkedVar, Int)
escAnalRhsTerm expr
  = do
    let (bndrs, body) = collectBinders expr
    body' <- withoutCandidates bndrs $ escAnalTerm body
    return $ ( mkLambdas [ Marked bndr Keep | bndr <- bndrs ] body'
             , length bndrs )

escAnalTerm :: SeqCoreTerm -> EscM (Term MarkedVar)
escAnalTerm (Var x)
  = do
    env <- getCandidates
    whenIsJust (candidateScope env x) $ \scope -> reportCall x [] scope
    return $ Var x 
escAnalTerm (Lit lit)
  = return $ Lit lit
escAnalTerm expr@(Lam {})
  = do
    let (tyBndrs, valBndrs, body) = collectTypeAndValueBinders expr
    -- Remove value binders from the environment in case of shadowing - we
    -- won't report them as free vars
    body' <- withoutCandidates valBndrs $
             -- Lambdas ruin contification, so the free vars escape
             filterAnalysis markAllAsEscaping $
             escAnalTerm body
    let bndrs' = [ Marked bndr Keep | bndr <- tyBndrs ++ valBndrs ]
    return $ mkLambdas bndrs' body'
escAnalTerm (Type ty)
  = return $ Type ty
escAnalTerm (Coercion co)
  = return $ Coercion co
escAnalTerm (Compute ty comm)
  = Compute ty <$> escAnalComm comm

escAnalComm :: SeqCoreCommand -> EscM (Command MarkedVar)
escAnalComm (Let bind body) 
  = do
    (_escs, bind', body') <- mfix $ \ ~(rec_escs_body, _, _) -> do
      (env', bind') <- escAnalBind NotTopLevel bind rec_escs_body
      (escs_body, body') <- readAnalysis $ withEnv env' $ escAnalComm body
      return (escs_body, bind', body')
    return $ Let bind' body'
escAnalComm (Jump args j)
  = do
    args' <- filterAnalysis markAllAsEscaping $ mapM escAnalTerm args
    return $ Jump args' j
escAnalComm (Eval term frames end)
  | Var fid <- term
  , Return <- end
  , all isAppFrame frames -- TODO Accomodate ticks somehow?
  = -- It's a tail call
    do
    env <- getCandidates
    let args = [ arg | App arg <- frames ]
    whenIsJust (candidateScope env fid) $ \scope -> reportCall fid args scope
    frames' <- mapM escAnalFrame frames
    return $ Eval (Var fid) frames' Return
  | otherwise
  = do
    -- If term is a variable and some of the frames are arguments, this call to
    -- escAnalTerm will briefly record an inaccurate CallInfo (showing no
    -- arguments), but markAllAsEscaping will throw away the CallInfo anyway.
    term'   <- filterAnalysis markAllAsEscaping $ escAnalTerm term
    frames' <- mapM escAnalFrame frames
    end'    <- escAnalEnd end
    return $ Eval term' frames' end'

escAnalFrame :: SeqCoreFrame -> EscM (Frame MarkedVar)
escAnalFrame (App arg) = App <$> filterAnalysis markAllAsEscaping (escAnalTerm arg)
escAnalFrame (Cast co) = return $ Cast co
escAnalFrame (Tick ti) = return $ Tick ti

escAnalEnd :: SeqCoreEnd -> EscM (End MarkedVar)
escAnalEnd Return = return Return
escAnalEnd (Case bndr alts)
  = do
    alts' <- withoutCandidate bndr $ forM alts $ \(Alt con bndrs rhs) -> do
      rhs' <- withoutCandidates bndrs $ escAnalComm rhs
      return $ Alt con (map (`Marked` Keep) bndrs) rhs'
    return $ Case (Marked bndr Keep) alts'

escAnalJoin :: SeqCoreJoin -> EscM (Join MarkedVar)
escAnalJoin (Join bndrs comm)
  = do
    comm' <- withoutCandidates bndrs $ filterAnalysis markAllAsEscaping $
             escAnalComm comm
    return $ Join (map (`Marked` Keep) bndrs) comm'

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
escAnalRule (Core.Rule { Core.ru_bndrs = bndrs, Core.ru_rhs = coreRhs })
  = let rhs = termFromCoreExpr coreRhs
      -- Note: This may be a wildly invalid term if this is a rule for a join
      -- point, since the RHS will translate as an application rather than a
      -- Jump. However, for our purposes here, this doesn't matter; the
      -- important thing is that the arguments escape. 
    in void $ withoutCandidates bndrs $ escAnalTerm rhs
escAnalRule _
  = return ()

escAnalUnfolding :: Unfolding -> EscM ()
escAnalUnfolding (Core.CoreUnfolding { Core.uf_tmpl = rhs  })
  = void $ escAnalTerm (termFromCoreExpr rhs)
escAnalUnfolding (Core.DFunUnfolding { Core.df_args = args })
  = mapM_ (escAnalTerm . termFromCoreExpr) args
escAnalUnfolding _ = return ()

----------------------
-- Phase 2: Contify --
----------------------

-- Continuation calling conventions --

-- | The protocol for invoking a given let-bound continuation. Currently all
-- such continuations must be invoked using a jump, so @ByJump@ is the only
-- constructor, but we must still keep track of which arguments are fixed and
-- should be omitted when converting a function call.
newtype KontCallConv = ByJump [ArgDesc]

-- Auxiliary datatype for idToJoinId
data KontType = KTExists TyVar KontType | KTTuple [KontType] | KTType Type

-- | Convert an id to the id of a join point, changing its type according to the
-- given calling convention. Updates the arity but NOT the rules or unfolding.
idToJoinId :: Id -> KontCallConv -> JoinId
idToJoinId p (ByJump descs)
  = p `setIdType` kontTypeToType (go (idType p) descs)
      `setIdArity` valArgCount
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

-- Environment for contification --

data CfyEnv
  = CE { ce_subst      :: Subst      -- Renamings (var -> var only)
       , ce_contifying :: IdEnv KontCallConv }
       
initCfyEnv :: CfyEnv
initCfyEnv = CE { ce_subst      = emptySubst
                , ce_contifying = emptyVarEnv }

initCfyEnvForTerm :: SeqCoreTerm -> CfyEnv
initCfyEnvForTerm term = initCfyEnv { ce_subst = freeVarSet }
  where
    freeVarSet = mkSubst (mkInScopeSet (freeVars term))
                   emptyVarEnv emptyVarEnv emptyVarEnv

bindAsContifying :: CfyEnv -> JoinId -> KontCallConv -> CfyEnv
bindAsContifying env j conv
  = env { ce_contifying = extendVarEnv (ce_contifying env) j conv }

bindAllAsContifying :: CfyEnv -> [(JoinId, KontCallConv)] -> CfyEnv
bindAllAsContifying env js = foldr (\(j, conv) env' -> bindAsContifying env' j conv) env js

kontCallConv :: CfyEnv -> Var -> Maybe KontCallConv
kontCallConv env var = lookupVarEnv (ce_contifying env) var 

zapSubst :: CfyEnv -> CfyEnv
zapSubst env = env { ce_subst = zapSubstEnv (ce_subst env) }

-- Contification --

cfyInTopLevelBinds :: Program MarkedVar -> SeqCoreProgram
cfyInTopLevelBinds binds = map cfy binds
  where
    cfy (NonRec pair) = NonRec (do_pair pair)
    cfy (Rec pairs)   = Rec (map do_pair pairs)
    
    do_pair pair = cfyInRhs env (unmark (binderOfPair pair)) pair
    
    env = initCfyEnv { ce_subst = extendInScopeIds emptySubst bndrs }
      -- Start fresh for each top-level bind, since only locals can be contified
    bndrs = [ bndr | Marked bndr _ <- bindersOfBinds binds ]

cfyInBind :: CfyEnv -> Bind MarkedVar -> (CfyEnv, SeqCoreBind)
cfyInBind env bind =
  case bind of
    NonRec pair -> (env', NonRec pair')
      where
        x = binderOfPair pair
        (env', x') = cfyInBndr env x
        pair' = cfyInRhs env x' pair

    Rec pairs -> (env', Rec pairs')
      where
        xs = map binderOfPair pairs
        (env', xs') = cfyInRecBndrs env xs
        pairs' = zipWith (cfyInRhs env') xs' pairs

cfyInRhs :: CfyEnv -> Id -> BindPair MarkedVar -> SeqCoreBindPair
cfyInRhs env x' (BindTerm (Marked _ Keep) term)
  = BindTerm x' (cfyInTerm env term)
cfyInRhs env j' (BindTerm (Marked _ (MakeKont descs)) term)
  = BindJoin j' (Join xs body')
  where
    (env', xs, bodyTerm) = etaExpandForJoinBody env descs term
    body  = case bodyTerm of Compute _ comm -> comm
                             _              -> Eval bodyTerm [] Return
    body' = cfyInComm env' body
cfyInRhs env j' (BindJoin (Marked _ Keep) join)
  = BindJoin j' (cfyInJoin env join)
cfyInRhs _ _ (BindJoin (Marked j (MakeKont _)) _)
  = pprPanic "cfyInRhs" (text "Trying to contify a join point" $$ pprBndr LetBind j)

cfyInBndr :: CfyEnv -> MarkedVar -> (CfyEnv, Var)
cfyInBndr env (Marked bndr mark) = (env_final, bndr_final)
  where
    (subst', bndr') = substBndr (ce_subst env) bndr
    bndr''          = case mark of
                        MakeKont descs -> idToJoinId bndr' (ByJump descs)
                        Keep           -> bndr'
    bndr_final      = cfyInIdInfo (zapSubst env) mark bndr''
                        -- zapSubst because bndr'' was already substBndr'd
    subst_final     = extendInScope subst' bndr_final -- update stored version
    
    env'      = env { ce_subst = subst_final }
    env_final = case mark of
                  MakeKont descs -> bindAsContifying env' bndr_final (ByJump descs)
                  Keep           -> env'
    
cfyInRecBndrs :: CfyEnv -> [MarkedVar] -> (CfyEnv, [Var])
cfyInRecBndrs env markedBndrs = (env_final, bndrs_final)
  where
    (bndrs, marks)   = unzip [ (bndr, mark) | Marked bndr mark <- markedBndrs ]
    (subst', bndrs') = substRecBndrs (ce_subst env) bndrs
    bndrs''          = zipWith convert bndrs marks
      where
        convert bndr (MakeKont descs) = idToJoinId bndr (ByJump descs)
        convert bndr Keep             = bndr
    
    bndrs_final      = [ cfyInIdInfo env_bndrs mark bndr
                       | bndr <- bndrs'' | mark <- marks ]
    env_bndrs        = zapSubst env_final -- knot
    subst_final      = extendInScopeIds subst' bndrs_final
    
    env'      = env { ce_subst = subst_final }    
    env_final = bindAllAsContifying env' [ (bndr, ByJump descs) 
                                         | (bndr, MakeKont descs) <- zip bndrs' marks ]
                                             -- okay to use old-ish binders
                                             -- because only unique is used as key
     
-- | Perform contification inside a binder's IdInfo. If the binder itself is
-- being contified, it should already have passed through idToJoinId, which sets
-- the type and arity accordingly. If the binding is recursive, the environment
-- should already be updated for the binder (in knot-tying fashion).
--
-- The binder should have passed through substBndr already, and accordingly the
-- environment's substitution should be zapped (with only an in-scope set).
cfyInIdInfo :: CfyEnv -> KontOrFunc -> Var -> Var
cfyInIdInfo env mark var
  | isTyVar var          = var
  | Keep <- mark
  , not (idHasRules var)
  , unf_is_boring        = var
  | otherwise            = var'
  where
    var' = var `setIdSpecialisation` specInfo'
               `setIdUnfolding` unf'
    
    unf = realIdUnfolding var
    unf_is_boring = case unf of Core.NoUnfolding -> True
                                Core.OtherCon {} -> True
                                _                -> False

    specInfo' = case idSpecialisation var of
                  SpecInfo rules fvs -> SpecInfo (map (cfyInRule env) rules)
                                                 (substVarSet (ce_subst env) fvs)
                                                   -- update with new IdInfo
    unf' = cfyInUnfolding env var mark unf

cfyInTerm :: CfyEnv -> Term MarkedVar -> SeqCoreTerm
cfyInTerm _   (Lit lit)         = Lit lit
cfyInTerm env (Type ty)         = Type (substTy (ce_subst env) ty)
cfyInTerm env (Coercion co)     = Coercion (substCo (ce_subst env) co)
cfyInTerm env (Var x)           = ASSERT2(isNothing (kontCallConv env x_new), ppr x_new)
                                  Var x_new
  where x_new = substIdOcc (ce_subst env) x
cfyInTerm env (Compute ty comm) = Compute (substTy (ce_subst env) ty)
                                          (cfyInComm env comm)
cfyInTerm env (Lam (Marked x mark) body)
  = ASSERT2(isKeep mark, ppr x)
    Lam x' body'
  where
    (subst', x') = substBndr (ce_subst env) x
    -- Lambda variables can have unfoldings, but those unfoldings are only ever
    -- constructor applications to variables, so no need to worry about contifying
    body' = cfyInTerm (env { ce_subst = subst' }) body

cfyInComm :: CfyEnv -> Command MarkedVar -> SeqCoreCommand
cfyInComm env (Let bind comm)
  = Let bind' comm'
  where
    (env', bind') = cfyInBind env bind
    comm' = cfyInComm env' comm
cfyInComm env (Jump args j)
  = Jump (map (cfyInTerm env) args) (substIdOcc (ce_subst env) j)
cfyInComm env (Eval (Var x) frames end)
  | let j' = substIdOcc (ce_subst env) x
  , Just (ByJump descs) <- kontCallConv env j'
  = ASSERT2(all isAppFrame frames, ppr x $$ ppr frames)
    ASSERT2(isReturn end, ppr end)
    let args  = removeFixedArgs [ arg | App arg <- frames ] descs
        args' = map (cfyInTerm env) args
    in Jump args' j'
cfyInComm env (Eval term frames end)
  = Eval (cfyInTerm env term) (map (cfyInFrame env) frames) (cfyInEnd env end)

cfyInFrame :: CfyEnv -> Frame MarkedVar -> SeqCoreFrame
cfyInFrame env (App arg) = App (cfyInTerm env arg)
cfyInFrame env (Cast co) = Cast (substCo (ce_subst env) co)
cfyInFrame env (Tick ti) = Tick (substTickish (ce_subst env) ti)

cfyInEnd :: CfyEnv -> End MarkedVar -> SeqCoreEnd
cfyInEnd _   Return                         = Return
cfyInEnd env (Case (Marked bndr mark) alts) = ASSERT2(isKeep mark, ppr bndr)
                                              Case bndr' alts'
  where
    (subst', bndr') = substBndr (ce_subst env) bndr
    alts'           = map (cfyInAlt (env { ce_subst = subst' })) alts

cfyInAlt :: CfyEnv -> Alt MarkedVar -> SeqCoreAlt
cfyInAlt env (Alt con mbndrs rhs) = ASSERT2(all isKeep marks, ppr mbndrs)
                                    Alt con bndrs' rhs'
  where
    (bndrs, marks)   = unzip [ (bndr, mark) | Marked bndr mark <- mbndrs ]
    (subst', bndrs') = substBndrs (ce_subst env) bndrs
    rhs'             = cfyInComm (env { ce_subst = subst' }) rhs

cfyInJoin :: CfyEnv -> Join MarkedVar -> SeqCoreJoin
cfyInJoin env (Join mbndrs body) = ASSERT2(all isKeep marks, ppr mbndrs)
                                   Join bndrs' body'
  where
    (bndrs, marks)   = unzip [ (bndr, mark) | Marked bndr mark <- mbndrs ]
    (subst', bndrs') = substBndrs (ce_subst env) bndrs
    body'            = cfyInComm (env { ce_subst = subst' }) body

cfyInRule :: CfyEnv -> Core.CoreRule -> Core.CoreRule
cfyInRule _   rule@(Core.BuiltinRule {}) = rule
cfyInRule env rule@(Core.Rule { Core.ru_bndrs = bndrs, Core.ru_args = args, Core.ru_rhs = rhs })
  = rule { Core.ru_bndrs = bndrs', Core.ru_args = map cfy args, Core.ru_rhs = cfy rhs }
  where
    (subst', bndrs') = substBndrs (ce_subst env) bndrs
    env' = env { ce_subst = subst' }
    cfy = onCoreExpr (cfyInTerm env' . runEscM . escAnalTerm)

cfyInUnfolding :: CfyEnv -> Id -> KontOrFunc -> Unfolding -> Unfolding
cfyInUnfolding env id mark unf
  = case unf of
      Core.CoreUnfolding { Core.uf_src = src, Core.uf_tmpl = tmpl, Core.uf_arity = arity
                         , Core.uf_is_top = is_top, Core.uf_guidance = guid }
        | not (Core.isStableSource (Core.uf_src unf)) -> Core.NoUnfolding -- don't bother
        | otherwise -> mkCoreUnfolding src is_top tmpl' arity' guid'
            where
              term = runEscM $ escAnalTerm (termFromCoreExpr tmpl)
              
              (tmpl', arity', guid')
                = case mark of
                    Keep
                      | isJoinId id ->
                          (joinToCoreExpr (termType bodyTerm) (cfyInJoin env join), arity, guid)
                      | otherwise ->
                          (termToCoreExpr (cfyInTerm env term), arity, guid)
                      where
                        join = Join bndrs body
                        -- It's possible there are too many binders (greater than the
                        -- arity of the join point, which is determined by the
                        -- callers), so in general we must put some back.
                        (allBndrs, innerBody) = collectBinders term
                        (bndrs, extraBndrs) = splitAt arity allBndrs
                        bodyTerm = mkLambdas extraBndrs innerBody
                        body = case bodyTerm of
                                 Compute _ comm -> comm
                                 other          -> Eval other [] Return
                    MakeKont descs
                      -> (joinToCoreExpr (termType bodyTerm) join, arity', guid')
                      where
                        join = Join bndrs body'
                        (env', bndrs, bodyTerm) = etaExpandForJoinBody env descs term
                        body = case bodyTerm of
                                 Compute _ comm -> comm
                                 other          -> Eval other [] Return
                        body' = cfyInComm env' body
                        arity' = count isValArgDesc descs `min` 1
                        guid' = fixGuid descs guid
      Core.DFunUnfolding { Core.df_bndrs = bndrs, Core.df_con = con, Core.df_args = args } ->
        warnPprTrace (case mark of MakeKont {} -> True; _ -> False) __FILE__ __LINE__
          (text "Trying to contify a dictionary??" $$ pprBndr LetBind id) $
        mkDFunUnfolding bndrs' con args'
        where
          (subst', bndrs') = substBndrs (ce_subst env) bndrs
          env' = env { ce_subst = subst' }
          args' = map (onCoreExpr (cfyInTerm env' . runEscM . escAnalTerm)) args
      _ -> unf
  where
    fixGuid descs guid@(Core.UnfIfGoodArgs { Core.ug_args = args })
      | not (any isValArgDesc descs)
      = guid { Core.ug_args = [0] } -- We keep a single Void# lambda in the unfolding
      | otherwise
      = guid { Core.ug_args = fixArgs args descs }
    fixGuid _ guid = guid
    
    fixArgs allArgs allDescs = go allArgs allDescs
      where
        go [] [] = []
        go [] (ValArg _ : _)
          = warnPprTrace True __FILE__ __LINE__
              (text "Out of value discounts" $$
               text "Unfolding:" <+> ppr unf $$
               text "Arg descs:" <+> ppr allDescs)
            []
        go args []
          = warnPprTrace True __FILE__ __LINE__
              (text "Leftover arg discounts:" <+> ppr args $$
               text "Unfolding:" <+> ppr unf $$
               text "Arg descs:" <+> ppr allDescs)
            []
        go (arg:args) (ValArg _ : descs)
          = arg : go args descs
        go (_:args) (FixedVoidArg : descs)
          = go args descs
        go args (_ : descs) -- Type argument (fixed or variable)
          = go args descs


etaExpandForJoinBody :: HasId b
                     => CfyEnv -> [ArgDesc] -> Term b
                     -> (CfyEnv, [Var], Term b)
etaExpandForJoinBody env descs expr
  = (env_final, bndrs_final, etaBody)
  where
    -- Calculate outer binders (existing ones from expr, minus fixed args)
    (bndrs, body) = collectNBinders (length descs) expr
    bndrs_unmarked = identifiers bndrs
    subst = ce_subst env
    (subst', bndr_maybes) = mapAccumL doBndr subst (zip bndrs_unmarked descs)
    bndrs' = catMaybes bndr_maybes

    -- Calculate eta-expanding binders and arguments
    extraArgs = drop (length bndrs) descs -- will need to eta-expand with these
    (subst_final, unzip -> (etaBndr_maybes, etaArgs))
      = mapAccumL mkEtaBndr subst' (zip [1..] extraArgs)
    etaBndrs = catMaybes etaBndr_maybes
    bndrs_final = bndrs' ++ etaBndrs
    
    env_final = env { ce_subst = subst_final }
    
    -- Create new join body
    etaBody = mkAppTerm body etaArgs
    
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
    mkEtaBndr :: Subst -> (Int, ArgDesc) -> (Subst, (Maybe Var, Term b))
    mkEtaBndr subst (_, FixedType ty)
      = (subst, (Nothing, Type (substTy subst ty)))
    mkEtaBndr subst (_, FixedVoidArg)
      = (subst, (Nothing, Var voidPrimId))
    mkEtaBndr subst (_, TyArg tyVar)
      = (subst', (Just tv', Type (mkTyVarTy tv')))
      where
        (subst', tv') = substBndr subst tyVar
    mkEtaBndr subst (n, ValArg ty)
      = (subst', (Just x, Var x))
      where
        (subst', x) = freshEtaId n subst ty
        
    collectNBinders :: TotalArity -> Term b -> ([b], Term b)
    collectNBinders = go []
      where
        go acc n (Lam x e) | n /= 0 = go (x:acc) (n-1) e
        go acc _ e                  = (reverse acc, e)

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
  ppr Keep = text "keep"
  ppr (MakeKont _) = text "cont"

instance Outputable MarkedVar where
  ppr (Marked var mark) = ppr var <+> brackets (ppr mark)

instance OutputableBndr MarkedVar where
  pprBndr site (Marked var Keep) = pprBndr site var
  pprBndr site (Marked var mark) = pprBndr site var <+> brackets (ppr mark)
  pprPrefixOcc (Marked var _) = pprPrefixOcc var
  pprInfixOcc  (Marked var _) = pprInfixOcc  var

instance Outputable ArgDesc where
  ppr (FixedType ty) = text "fixed type:" <+> ppr ty
  ppr FixedVoidArg   = text "fixed void#"
  ppr (TyArg tyVar)  = text "type arg:" <+> pprBndr LambdaBind tyVar
  ppr (ValArg ty)    = text "arg of type" <+> ppr ty

-- copied from CoreArity
freshEtaId :: Int -> Subst -> Type -> (Subst, Id)
freshEtaId n subst ty
      = (subst', eta_id')
      where
        ty'     = substTy subst ty
        eta_id' = uniqAway (substInScope subst) $
                  mkSysLocal (fsLit "cfyeta") (mkBuiltinUnique n) ty'
        subst'  = extendInScope subst eta_id'
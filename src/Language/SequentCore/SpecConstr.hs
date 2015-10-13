{-# LANGUAGE ParallelListComp #-}

-- |
-- Module      : Language.SequentCore.SpecConstr
-- Description : SpecConstr reimplementation
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- A simple reimplementation of the SpecConstr pass using Sequent Core.
--
-- Based on
-- <http://research.microsoft.com/en-us/um/people/simonpj/papers/spec-constr Call-pattern specialization for Haskell programs>,
-- Simon Peyton Jones, submitted to ICFP 2007. 

{-

The idea of the SpecConstr (specialization by constructor) pass is to find
instances of calls whose arguments are constructor invocations and replace them
with calls to specialized versions of the called functions, thereby hoping to
avoid needless allocation and case analysis. For instance, consider the
following (contrived) example, found in @examples/SpecConstrExpl.hs@:

    facOrNeg :: Either Int Int -> Int
    facOrNeg (Left 0) = 1
    facOrNeg (Left n) = n * facOrNeg (Left (n-1))
    facOrNeg (Right n) = -n

Depending one whether its argument is @Left@ or @Right, @forOrNeg@ acts as
either the @fac@ or @neg@. But note the recursive call @facOrNeg (Left (n-1))@:
We know it will always be evaluated by one of the first two clauses, which
pulls the @Int@ out again. Thus each recursive call involves creating a Left
value only to deconstruct it immediately.

The result of SpecConstr is the introduction of a companion function:

    facOrNeg :: Either Int Int -> Int
    facOrNeg (Left 0) = 1
    facOrNeg (Left n) = n * facOrNegLeft (n-1)
    facOrNeg (Right n) = -n

    facOrNegLeft :: Int -> Int
    facOrNegLeft 0 = 1
    facOrNegLeft n = n * facOrNegLeft (n-1)

Now there are no superfluous constructions or matchings of Left values.

Implementation
--------------

The basic strategy is the same as for the original Core version of SpecConstr.
During the traversal:

* Track whether each variable is bound as a function or argument (top-down flow)
* Record whenever a function is called, along with the arguments, or an
  argument is case-analyzed (bottom-up flow)
* At each binding site for a recursive function, check whether the body calls
  the function with a saturated constructor application as at least one argument
  that is case-analyzed somewhere else in the body; if so, produce a specialized
  function and a rewrite rule

Like many passes, this one relies heavily on the fact that the simplifier will
run afterward: We don't actually replace calls by the specialized versions, we
only produce the rules that will do so.

Formally, the SPJ paper gives six criteria that a function call must pass in
order to give rise to a specialization:

H1 The function is bound to a lambda
H2 The body of the lambda isn't too big
H3 The binding is recursive and the call is in its RHS
H4 The call is saturated
H5 At least one of the arguments is a constructor application
H6 That argument is case-analysed somewhere in the RHS

Criteria H3 and H4 are met during the course of traversal. The others are
checked at the binding site for each recursive function; see the auxiliary
functions for specialize.

-}

module Language.SequentCore.SpecConstr (
  plugin
) where

import Language.SequentCore.Plugin
import Language.SequentCore.Pretty ()
import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import CoreMonad  ( CoreM
                  , Plugin(installCoreToDos), defaultPlugin
                  , errorMsg, putMsg
                  , reinitializeGlobals
                  , CoreToDo(CoreDoSpecConstr, CoreDoPasses, CoreDoPluginPass) )
import CoreUnfold ( couldBeSmallEnoughToInline )
import CoreSyn    ( CoreRule )
import DynFlags   ( DynFlags(specConstrThreshold), getDynFlags )
import FastString ( fsLit, mkFastString )
import Id         ( Id, mkSysLocalM, idName, idInlineActivation )
import Name       ( nameOccName, occNameString )
import Outputable hiding ((<>))
import Rules      ( mkRule, addIdSpecialisations )
import Var        ( Var, varType )
import VarEnv
import VarSet

import Control.Applicative  ( (<$>), (<|>) )
import Control.Monad
import Data.List            ( nubBy )
import Data.Monoid

tracing :: Bool
tracing = False

-- | Plugin data. The initialization code replaces the built-in SpecConstr pass
-- in the Core-to-Core pipeline.
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = \_ todos -> do
    reinitializeGlobals
    case replace todos of
      Nothing ->
        do
          errorMsg (text "Could not find SpecConstr pass to replace")
          return todos
      Just todos' ->
        return todos'
} where
  replace (CoreDoSpecConstr : todos)
    = Just (specConstrPass : todos)
  replace (cdp@(CoreDoPasses todos1) : todos2)
    = do
        todos1' <- replace todos1
        return $ CoreDoPasses todos1' : todos2
      <|>
      do
        todos2' <- replace todos2
        return $ cdp : todos2'
  replace (todo : todos)
    = (todo :) <$> replace todos
  replace []
    = Nothing

  specConstrPass = CoreDoPluginPass "SeqSpecConstr" (sequentPass specModule)

data ScEnv
  = SCE { sc_size       :: Maybe Int
        , sc_how_bound  :: VarEnv HowBound
        , sc_dflags     :: DynFlags
        }

instance Outputable ScEnv where
  ppr (SCE { sc_size = sz, sc_how_bound = hb })
    = sep [hang (text "SCE {") 2 $ sep [
        text "sc_size" <+> equals <+> maybe (text "(any)") int sz <+> comma,
        text "sc_how_bound" <+> equals <+> ppr hb
      ], char '}']

data ScUsage = ScUsage Calls ArgUsage

instance Outputable ScUsage where
  ppr (ScUsage calls usage)
    = hang (text "ScUsage") 2 $ sep [ppr calls, ppr usage]

type Calls = VarEnv [Call]
type Call = [SeqCoreTerm]

data HowBound = SpecFun | SpecArg

instance Outputable HowBound where
  ppr SpecFun = text "SpecFun"
  ppr SpecArg = text "SpecArg"

type ArgUsage = VarSet

specModule :: [SeqCoreBind] -> CoreM [SeqCoreBind]
specModule binds = do
  env <- initScEnv <$> getDynFlags
  map snd <$> mapM (specInBind env) binds

initScEnv :: DynFlags -> ScEnv
initScEnv dflags = SCE { sc_size = specConstrThreshold dflags
                       , sc_how_bound = emptyVarEnv
                       , sc_dflags = dflags }

emptyScUsage :: ScUsage
emptyScUsage = ScUsage emptyVarEnv emptyVarSet

instance Monoid ScUsage where
  mempty
    = emptyScUsage
  ScUsage calls1 used1 `mappend` ScUsage calls2 used2
    = ScUsage (plusVarEnv_C (++) calls1 calls2) (used1 `unionVarSet` used2)

specInTerm :: ScEnv -> SeqCoreTerm -> CoreM (ScUsage, SeqCoreTerm)
specInTerm env (Lam x t)
  = do
    (usage, t') <- specInTerm env' t
    return (usage, Lam x t')
  where
    env' = env { sc_how_bound = extendVarEnv hb x SpecArg }
    hb   = sc_how_bound env
specInTerm env (Compute kb c)
  = do
    (usage, c') <- specInCommand env c
    return (usage, Compute kb c')
specInTerm _ v
  = return (emptyScUsage, v)

specInKont :: ScEnv -> SeqCoreKont -> CoreM (ScUsage, SeqCoreKont)
specInKont env (frames, end)
  = do
    (usages, frames') <- mapAndUnzipM (specInFrame env) frames
    (usage2, end') <- specInEnd env end
    return (mconcat usages <> usage2, (frames', end'))

specInFrame :: ScEnv -> SeqCoreFrame -> CoreM (ScUsage, SeqCoreFrame)
specInFrame env (App v)
  = do
    (usage, v') <- specInTerm env v
    return (usage, App v')
specInFrame _ frame
  = return (emptyScUsage, frame)

specInEnd :: ScEnv -> SeqCoreEnd -> CoreM (ScUsage, SeqCoreEnd)
specInEnd env (Case x as)
  = do
    (usages, as') <- mapAndUnzipM (specInAlt env) as
    return (mconcat usages, Case x as')
specInEnd _ Return
  = return (emptyScUsage, Return)

specInBindRhs :: ScEnv -> SeqCoreBindPair -> CoreM (ScUsage, SeqCoreBindPair)
specInBindRhs env (BindTerm x term)
  = do
    (usage, term') <- specInTerm env term
    return (usage, BindTerm x term')
specInBindRhs env (BindJoin j (Join xs comm))
  = do
    (usage, comm') <- specInCommand env comm
    return (usage, BindJoin j (Join xs comm'))

specInAlt :: ScEnv -> SeqCoreAlt -> CoreM (ScUsage, SeqCoreAlt)
specInAlt env (Alt ac xs c)
  = do
    (usage, c') <- specInCommand env c
    return (usage, Alt ac xs c')

specInBind :: ScEnv -> SeqCoreBind -> CoreM (ScUsage, SeqCoreBind)
specInBind env b
  = do
    (u, _, b') <- specBind env b
    return (u, b')

specInCommand :: ScEnv -> SeqCoreCommand -> CoreM (ScUsage, SeqCoreCommand)
specInCommand env (Let bind comm)
  = do
    (usage1, env', bind') <- specBind env bind
    (usage2, comm') <- specInCommand env' comm
    return (usage1 <> usage2, Let bind' comm')
specInCommand env (Eval term frames end)
  = do
    (usage, term', frames', end') <- specInCut env term frames end
    return (usage, Eval term' frames' end')
specInCommand env (Jump args j)
  = do
    -- TODO Maybe specialize join points, too?
    (usages, args') <- mapAndUnzipM (specInTerm env) args
    return (mconcat usages, Jump args' j)
    
specInCut :: ScEnv -> SeqCoreTerm -> [SeqCoreFrame] -> SeqCoreEnd
        -> CoreM (ScUsage, SeqCoreTerm, [SeqCoreFrame], SeqCoreEnd)
specInCut env v fs e
  = do
    let u = usageFromCut env v fs e
    (u_v, v') <- specInTerm env v
    (u_k, (fs', e')) <- specInKont env (fs, e)
    return (u <> u_v <> u_k, v', fs', e')

usageFromCut :: ScEnv -> SeqCoreTerm -> [SeqCoreFrame] -> SeqCoreEnd -> ScUsage
usageFromCut env (Var x) [] (Case {})
  | Just SpecArg <- sc_how_bound env `lookupVarEnv` x
  = ScUsage emptyVarEnv (unitVarSet x)
-- Implementation note: The Sequent Core form simplifies this function by making
-- the head of an application immediately available, so that a function like
-- collectArgs isn't necessary to find out what the head is. In this case, that
-- means we can avoid doing any search whatsoever if the head isn't a variable
-- that we know to be bound to a candidate for specialization.
usageFromCut env v@(Var f) fs _
  | Just SpecFun <- sc_how_bound env `lookupVarEnv` f
  , Just (args, _) <- asSaturatedCall v fs
  = ScUsage (unitVarEnv f [args]) emptyVarSet
usageFromCut _ _ _ _
  = emptyScUsage

specBind :: ScEnv -> SeqCoreBind -> CoreM (ScUsage, ScEnv, SeqCoreBind)
specBind env (NonRec pair)
  = do
    (u, pair') <- specInBindRhs env pair
    return (u, env, NonRec pair')
specBind env (Rec pairs)
  = do
    (usages, pairs') <- mapAndUnzipM (specInBindRhs env') pairs
    let
      totalUsages = mconcat usages
    bindss <- forM (zip (map binderOfPair pairs) pairs') $ \(bndr, pair') ->
      case pair' of
        BindTerm _ term -> map (uncurry BindTerm) <$>
                               specialize env' totalUsages (bndr, term)
        BindJoin _ join -> return [BindJoin bndr join]
    return (totalUsages, env', Rec (concat bindss))
  where 
    env'  = env { sc_how_bound = hb' }
    hb'   = mkVarEnv [(binderOfPair pair, SpecFun) | pair <- pairs] `plusVarEnv`
                    sc_how_bound env

data CallPat = [Var] :-> [SeqCoreTerm]

instance Outputable CallPat where
  ppr (xs :-> args) = ppr xs <+> text ":->" <+> ppr args

-- | A generated specialization---the call pattern that gave rise to it, the
-- identifier of the specialized function, and the function's definition.
data Spec = Spec {
  spec_pat :: CallPat,
  spec_id :: Id,
  spec_defn :: SeqCoreTerm
}

instance Outputable Spec where
  ppr spec
    = sep
      [ text "specialization for" <+> parens (ppr $ spec_pat spec)
      , text "id" <+> (ppr $ spec_id spec)
      , text "defn" <+> (ppr $ spec_defn spec)
      ]

specToBinding :: Spec -> (Var, SeqCoreTerm)
specToBinding (Spec { spec_id = x, spec_defn = v }) = (x, v)

-- | The kernel of the SpecConstr pass. Takes the environment, data about how
-- variables are used, and a let binding (part of a recursive block), and
-- returns a new list of bindings---the original one (with specialization rules
-- added) and also all specialized versions.
specialize :: ScEnv -> ScUsage -> (Var, SeqCoreTerm)
                    -> CoreM [(Var, SeqCoreTerm)]
specialize env (ScUsage calls used) (x, v)
  | tracing
  , pprTrace "specialize" (ppr x <+> ppr v) False
  = undefined
  | skip
  = do
    when tracing $ putMsg $ text "specialize: skipping" <+> ppr x
    return [(x, v)]
  | otherwise
  = do
    when tracing $ putMsg $ text "specialize: PROCESSING" <+> ppr x
    -- Create the specializations
    specs <- mkSpecs
    -- Add specization rules to the function's identifier
    let x' = addRulesForSpecs specs
    -- Return the new binding along with all specialized bindings
    return $ (x', v) : map specToBinding specs
  where
    -- | Decide whether to skip this binding altogether. This checks whether
    -- the binding satisfies criteria H1 and H2 (see implementation notes at
    -- top).
    skip :: Bool
    skip | null binders
         = True -- H1 fails
         | Just sz <- sc_size env
         -- TODO Implement couldBeSmallEnoughToInline for ourselves
         , let coreExpr = termToCoreExpr body
         , not $ couldBeSmallEnoughToInline (sc_dflags env) sz coreExpr
         = True -- H2 fails
         | otherwise
         = False

    binders :: [Var] -- ^ Binders for the bound function. Empty if not a function.
    body :: SeqCoreTerm -- ^ Body of the bound function after all lambdas.
    (binders, body) = collectBinders v

    -- Create the specializations for the binding @let x = c@.
    mkSpecs :: CoreM [Spec]
    mkSpecs
      -- Find all calls made to this function
      | Just cs <- calls `lookupVarEnv` x
      = do
        -- Make a pattern for each call that we want to specialize for
        pats <- mapM callToPat (filter shouldSpec cs)
        -- Make a specialized function for each unique call pattern
        mapM specCall (nubBy samePat pats)
      | otherwise
      = return [] -- No calls made to this function

    -- | Decide whether to specialize for a particular call (i.e. check
    -- criteria H5 and H6).
    shouldSpec :: Call -> Bool
    shouldSpec args
      = or $ zipWith qualifyingArg binders args
      where
        qualifyingArg x' term
          = termIsConstruction term && x' `elemVarSet` used

    -- | Create a specialization for a call pattern.
    specCall :: CallPat -> CoreM Spec
    specCall pat@(vars :-> vals)
      = do
        let v' = mkLambdas vars $
                   addLetsToTerm [NonRec (BindTerm x v) | x <- binders | v <- vals] body
        x' <- mkSysLocalM (fsLit "scsc") (termType v')
        return $ Spec { spec_pat = pat, spec_id = x', spec_defn = v' }

    -- | Extract a call pattern, given the arguments in a call.
    callToPat :: Call -> CoreM CallPat
    callToPat args
      = do
        (varss, rhss) <- unzip `liftM` zipWithM argToSubpat binders args
        return $ concat varss :-> rhss

    -- | Given an argument to the call, abstract over it to produce part of a
    -- call pattern. This produces some number of pattern variables and one
    -- argument.
    argToSubpat :: Var -> SeqCoreTerm -> CoreM ([Var], SeqCoreTerm)
    argToSubpat _ term
      | Just (dc, tyArgs, valArgs) <- termAsConstruction term
      -- This is a saturated constructor application, so abstract over its
      -- arguments to produce the subpattern
      = do
        -- Abstract over *value* arguments only
        tmVars <- mapM (mkSysLocalM (fsLit "scsca") . termType) valArgs
        let val = mkConstruction dc tyArgs (map Var tmVars)
        return (tmVars, val)
    argToSubpat var _
      -- Just abstract over the whole argument; it's either a variable or
      -- something like a function application, so specializing for it doesn't
      -- make sense
      = do
        p <- mkSysLocalM (fsLit "scsca") (varType var)
        return ([p], Var p)

    -- | Produce a new version of the bound variable @x@, with a rule attached
    -- for each specialization.
    addRulesForSpecs :: [Spec] -> Var
    addRulesForSpecs specs
      = addIdSpecialisations x (zipWith ruleForSpec specs [1..])

    -- | Create the rewrite rule that activates the given specialization.
    ruleForSpec :: Spec -> Int -> CoreRule
    ruleForSpec (Spec { spec_pat = patVars :-> patArgs, spec_id = x' }) n
      = mkRule auto local name act fn bndrs args rhs
      where
        auto  = True
        local = True
        name  = mkFastString $ "SC:" ++ occNameString (nameOccName (idName x))
                  ++ show n
        act   = idInlineActivation x
        fn    = idName x
        bndrs = patVars
        args  = map termToCoreExpr patArgs
        rhs   = termToCoreExpr $ mkAppTerm (Var x') (map Var patVars)
          
infix 4 `samePat`

-- Decide whether two call patterns are identical up to alpha-renaming.
samePat :: CallPat -> CallPat -> Bool
xs1 :-> cs1 `samePat` xs2 :-> cs2 =
  -- We compare the lists cs1 and cs2 in an environment in which the variables
  -- xs1 in cs1 are identified with the variables xs2 in cs2. (See Syntax.)
  aeqIn env cs1 cs2
  where
    env = rnBndrs2 (mkRnEnv2 emptyInScopeSet) xs1 xs2

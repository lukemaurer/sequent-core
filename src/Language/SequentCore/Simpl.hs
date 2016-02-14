{-# LANGUAGE TupleSections, ViewPatterns, MultiWayIf, CPP #-}

-- | 
-- Module      : Language.SequentCore.Simpl
-- Description : Simplifier reimplementation using Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- A proof of concept to demonstrate that the Sequent Core syntax can be used
-- for basic optimization in the style of GHC's simplifier. In some ways, it is
-- easier to use Sequent Core for these, as the continuations are expressed
-- directly in the program syntax rather than needing to be built up on the fly.

module Language.SequentCore.Simpl (runSimplifier) where

import Language.SequentCore.Arity
import Language.SequentCore.Lint
import Language.SequentCore.OccurAnal
import Language.SequentCore.Pretty (pprTopLevelBinds, pprKont)
import Language.SequentCore.Simpl.Env
import Language.SequentCore.Simpl.Monad
import Language.SequentCore.Simpl.Util
import Language.SequentCore.Syntax
import Language.SequentCore.Syntax.Util
import Language.SequentCore.Translate
import Language.SequentCore.Util
import Language.SequentCore.WiredIn

import BasicTypes
import Coercion    ( coercionKind, isCoVar, mkCoCast, mkSymCo, mkTransCo )
import CoreMonad   ( SimplifierMode(..), Tick(..), CoreM,
                     isZeroSimplCount, pprSimplCount, simplCountN,
                     putMsg,
                     getHscEnv, getRuleBase
                   )
import CoreSyn     ( CoreVect(..), CoreRule, UnfoldingSource(..)
                   , evaldUnfolding
                   , isRuntimeVar, isStableSource, isStableUnfolding
                   , tickishCounts
                   , ruleArity, ruleName )
import DataCon
import Demand      ( StrictSig(..), dmdTypeDepth )
import DynFlags    ( DynFlags, DumpFlag(..), GeneralFlag(..)
                   , gopt, dopt
                   , printInfoForUser
                   , ufKeenessFactor, ufUseThreshold )
import ErrUtils    ( debugTraceMsg, dumpSDoc )
import FamInstEnv
import FastString
import Id
import IdInfo      ( IdInfo, demandInfo, strictnessInfo, vanillaIdInfo,
                     setArityInfo, setDemandInfo, setStrictnessInfo, zapDemandInfo )
import HscTypes    ( ExternalPackageState(..), ModGuts(..), VectInfo(..)
                   , hscEPS )
import Literal     ( litIsDupable, litIsLifted )
import Maybes      ( whenIsJust )
import MkCore      ( mkWildValBinder )
import MonadUtils
import Name        ( isExternalName, mkSystemVarName )
import Outputable
import Pair
import Rules       ( extendRuleBaseList, lookupRule, unionRuleBase )
import Type hiding ( extendTvSubst, substTy, substTyVar )
import TysWiredIn  ( mkTupleTy )
import UniqSupply
import Util        ( debugIsOn )
import VarEnv
import VarSet

import Control.Arrow       ( second )
import Control.Exception   ( assert )
import Control.Monad       ( when )

import Data.List           ( mapAccumL )
import Data.Maybe          ( catMaybes, isJust, mapMaybe )

-- | Run the simplifier on the given Sequent Core module. The Core bindings in the
-- given ModGuts are ignored and returned unchanged, but other parts are considered 
-- valid and may be updated.
runSimplifier :: Int -> SimplifierMode -> ModGuts -> SeqCoreProgram
              -> CoreM (ModGuts, SeqCoreProgram)
runSimplifier iters mode guts binds
  = do
    dflags <- getDynFlags
    liftIO $ debugTraceMsg dflags 2  $ text "RUNNING SEQUENT CORE SIMPLIFIER"
                                    $$ text "Mode:" <+> ppr mode
    runLint "pre-simpl" binds empty
    binds' <- go 1 [] binds
    return (guts, binds')
  where
    rules = mg_rules guts
    famEnvs = mg_fam_inst_env guts
    
    go n prevCounts binds
      | n > iters
      = (warnPprTrace (debugIsOn && iters > 2) __FILE__ __LINE__ $
          text "Simplifier bailing out after" <+> int iters
            <+> text "iterations"
            <+> (brackets $ hsep $ punctuate comma $
                 map (int . simplCountN) (reverse prevCounts)))
        return binds
      | otherwise
      = do
        dflags <- getDynFlags
        ruleBase <- getRuleBase
        hscEnv <- getHscEnv
        eps <- liftIO $ hscEPS hscEnv
        let mod       = mg_module guts
            vectVars  = mkVarSet $
                          catMaybes [ fmap snd $ lookupVarEnv (vectInfoVar (mg_vect_info guts)) bndr
                                    | Vect bndr _ <- mg_vect_decls guts]
                          ++
                          catMaybes [ fmap snd $ lookupVarEnv (vectInfoVar (mg_vect_info guts)) bndr
                                    | bndr <- bindersOfBinds binds]
                                    -- FIXME: This second comprehensions is only needed as long as we
                                    --        have vectorised bindings where we get "Could NOT call
                                    --        vectorised from original version".
            (maybeVects, maybeVectVars)
                      = case sm_phase mode of
                          InitialPhase -> (mg_vect_decls guts, vectVars)
                          _            -> ([], vectVars)
            rule_base1 = unionRuleBase ruleBase (eps_rule_base eps)
            rule_base2 = extendRuleBaseList rule_base1 rules
            famEnvs2 = (eps_fam_inst_env eps, famEnvs)
            env = initialEnv dflags mode rule_base2 famEnvs2
            occBinds = runOccurAnal env mod maybeVects maybeVectVars binds
        whenDumping $ putMsg  $ text "BEFORE" <+> int n
                             $$ text "--------" $$ pprTopLevelBinds occBinds
        runLint "in occurrence analysis" occBinds (text "--- Original Sequent Core: ---"
                                                   $$ pprTopLevelBinds binds)
        whenLinting $ whenIsJust (lintCoreBindings occBinds) $ \err ->
          pprPanic "Sequent Core Lint error (in occurrence analysis)"
            (withPprStyle defaultUserStyle $ err)
        (binds', count) <- runSimplM $ simplModule env occBinds
        -- FIXME Here we should also be updating the rules with the substitution
        -- resulting from simplifying
        whenDumping $ putMsg  $ text "SUMMARY" <+> int n
                             $$ text "---------"
                             $$ pprSimplCount count
                             $$ text "AFTER" <+> int n
                             $$ text "-------"
                             $$ pprTopLevelBinds binds'
        runLint "post-simpl" binds' (text "--- Original Sequent Core: ---"
                                     $$ pprTopLevelBinds occBinds)
        if isZeroSimplCount count
          then do
            when tracing $ putMsg  $  text "Done after"
                                  <+> int n <+> text "iterations"
            return binds'
          else go (n+1) (count:prevCounts) binds'
    
    runOccurAnal env mod vects vectVars binds
      = let isRuleActive = activeRule env
        in occurAnalysePgm mod isRuleActive rules vects vectVars binds
    
    runLint hdr binds extraDoc
      = whenLinting $
        whenIsJust (lintCoreBindings binds) $ \err ->
          pprPgmError ("Sequent Core Lint error (" ++ hdr ++ ")")
            (withPprStyle defaultUserStyle $ err
                                          $$ pprTopLevelBinds binds 
                                          $$ extraDoc)
    
    whenLinting m
      = do
        dflags <- getDynFlags
        when (gopt Opt_DoCoreLinting dflags) m
    
    whenDumping m
      = do
        dflags <- getDynFlags
        when (dopt Opt_D_dump_simpl_iterations dflags) m
      
-----------
-- Binds --
-----------

simplModule :: SimplEnv -> [InBind] -> SimplM [OutBind]
simplModule env0 binds0
  = do  {       -- Put all the top-level binders into scope at the start
                -- so that if a transformation rule has unexpectedly brought
                -- anything into scope, then we don't get a complaint about that.
                -- It's rather as if the top-level binders were imported.
                -- See note [Glomming] in OccurAnal.
        ; let (env1, dsc, csc, _) = enterRecScopes env0 emptyDataScope nullControlScope
                                      (bindersOfBinds binds0)
        ; assert (isEmptyControlScope csc) $ return ()
        ; dflags <- getDynFlags
        ; let dump_flag = dopt Opt_D_verbose_core2core dflags
        ; flts <- simpl_binds dump_flag env1 dsc binds0 []
        ; freeTick SimplifierDone
        ; return $ getFloatBinds flts }
  where
        -- We need to track the zapped top-level binders, because
        -- they should have their fragile IdInfo zapped (notably occurrence info)
        -- That's why we run down binds and bndrs' simultaneously.
        --
        -- The dump-flag emits a trace for each top-level binding, which
        -- helps to locate the tracing for inlining and rule firing
    simpl_binds :: Bool -> SimplEnv -> DataScope -> [InBind] -> [Floats] -> SimplM Floats
    simpl_binds _    _   _   []           fltss = return (catFloats (reverse fltss))
    simpl_binds dump env dsc (bind:binds) fltss = do { (flts, env', dsc', csc') <- trace_bind dump bind $
                                                                                   simpl_bind env dsc bind
                                                     ; assert (isEmptyControlScope csc') $
                                                       simpl_binds dump env' dsc' binds (flts : fltss) }

    trace_bind True  bind = pprTrace "SimplBind" (ppr (bindersOf bind))
    trace_bind False _    = \x -> x

    simpl_bind env dsc (Rec pairs)   = simplRec          env  dsc nullControlScope pairs TopLevel
    simpl_bind env dsc (NonRec pair) = simplRecOrTopPair env' dsc nullControlScope b' pair TopLevel NonRecursive
        where
          b = binderOfPair pair
          (env', b') = addBndrRules env dsc nullControlScope b (lookupRecBndr env dsc nullControlScope b)

{-
simplRec is used for
  * [simplCommand, simplModule] recursive bindings only
-}
simplRec :: SimplEnv -> DataScope -> ControlScope
         -> [InBindPair] -- but binders *already in scope*
         -> TopLevelFlag
         -> SimplM (Floats, SimplEnv, DataScope, ControlScope)
simplRec env0 dsc0 csc0 pairs0 top_lvl
  = do  { let (env_with_info, triples) = mapAccumL add_rules env0 pairs0
        ; (flts, env1, dsc1, csc1) <- go env_with_info dsc0 csc0 triples []
        ; let (flts', env') = env1 `addRecFloats` flts
        ; return (flts', env', dsc1, csc1) }
  where
    add_rules :: SimplEnv -> InBindPair -> (SimplEnv, (OutBndr, InBindPair))
        -- Add the (substituted) rules to the binder
    add_rules env pair = (env', (bndr', pair))
        where
          bndr = binderOfPair pair
          (env', bndr') = addBndrRules env dsc0 csc0 bndr (lookupRecBndr env dsc0 csc0 bndr)

    go env dsc csc [] fltss = return (catFloats (reverse fltss), env, dsc, csc)

    go env dsc csc ((new_bndr, old_bind_pair) : pairs) fltss
        = do { (flts, env', dsc', csc') <- simplRecOrTopPair env dsc csc
                                             new_bndr old_bind_pair top_lvl Recursive
             ; go env' dsc' csc' pairs (flts : fltss) }

{-
simplRecOrTopPair is used for
        * recursive bindings (whether top level or not)
        * top-level non-recursive bindings

It assumes the binder has already been simplified, but not its IdInfo.
-}

simplRecOrTopPair :: SimplEnv -> DataScope -> ControlScope
                  -> OutBndr -> InBindPair
                  -> TopLevelFlag -> RecFlag
                  -> SimplM (Floats, SimplEnv, DataScope, ControlScope)
simplRecOrTopPair env dsc csc new_bndr old_pair top_lvl is_rec
  = do -- Check for unconditional inline
       preInline <- preInlineUnconditionally env dsc old_pair top_lvl
       if preInline
           then do tick (PreInlineUnconditionally old_bndr)
                   let (dsc', csc') = extendSubstWithInBindPair dsc csc dsc csc old_pair
                   return (emptyFloats, env, dsc', csc')
           else simplLazyOrJoinBind env dsc csc new_bndr dsc csc old_pair top_lvl is_rec
  where old_bndr = binderOfPair old_pair

simplLazyOrJoinBind :: SimplEnv -> DataScope -> ControlScope
                    -> OutVar -> DataScope -> ControlScope -> InBindPair -> TopLevelFlag
                    -> RecFlag -> SimplM (Floats, SimplEnv, DataScope, ControlScope)
simplLazyOrJoinBind env dsc csc new_bndr dsc_rhs csc_rhs pair level recFlag
  = case pair of
      BindTerm old_bndr term -> do
        (flts, env', dsc') <- simplLazyBind env dsc new_bndr dsc_rhs
                                            old_bndr term level recFlag
        return (flts, env', dsc', csc)
      BindJoin old_bndr join ->
        assert (isNotTopLevel level) $ do
          (flts, csc_rhs') <- ensureDupableKont env dsc_rhs csc_rhs
            -- Note [Call ensureDupableKont around join point]
          (flts', env', csc') <- simplJoinBind (env `augmentFromFloats` flts)
                                                dsc csc new_bndr dsc_rhs csc_rhs'
                                                old_bndr join recFlag
          return (flts `addFloats` flts', env', dsc, csc')

{-
simplLazyBind is used for
  * [simplRecOrTopPair] recursive bindings (whether top level or not)
  * [simplRecOrTopPair] top-level non-recursive bindings
  * [simplNonRec]      non-top-level *lazy* non-recursive bindings

Nota bene:
    1. It assumes that the binder is *already* simplified,
       and is in scope, and its IdInfo too, except unfolding

    2. It assumes that the binder type is lifted.

    3. It does not check for pre-inline-unconditionallly;
       that should have been done already.
-}

simplLazyBind :: SimplEnv -> DataScope -> OutVar -> DataScope -> InVar -> InTerm -> TopLevelFlag
              -> RecFlag -> SimplM (Floats, SimplEnv, DataScope)
simplLazyBind env dsc new_bndr dsc_rhs old_bndr term level recFlag
  | tracing
  , pprTraceShort "simplLazyBind" (ppr old_bndr <+> (if old_bndr == new_bndr then empty else darrow <+> ppr new_bndr)
                                      <+> ppr level <+> ppr recFlag $$ pprBndr LetBind new_bndr $$ ppr term) False
  = undefined
  | isCoVar old_bndr
  , Coercion co <- assert (isCoArg term) term
  = let co' = simplCoercion env dsc_rhs co
    in return (emptyFloats, env, extendCvSubst dsc old_bndr co')
  | otherwise
  = do
    let   (tvs, body) = case collectTypeBinders term of
                          (tvs, body) | not_lam body -> (tvs,body)
                                      | otherwise    -> ([], term)
          not_lam (Lam _ _) = False
          not_lam _         = True
                  -- Do not do the "abstract tyyvar" thing if there's
                  -- a lambda inside, because it defeats eta-reduction
                  --    f = /\a. \x. g a x
                  -- should eta-reduce(flts, term') <- simplTerm env dsc_rhs RhsCtxt term
          (env_body, dsc_body, tvs') = enterTermScopes env dsc_rhs tvs 
    (flts, body') <- simplTerm env_body dsc_body RhsCtxt body
    (flts', body'') <- prepareRhsTerm (env `augmentFromFloats` flts) level new_bndr body'
    let flts_all = flts `addFloats` flts'
    (flts_out, env_x', term_final)
      <- if | not (doFloatFromRhs level recFlag False body'' flts_all)
              -> do term' <- mkLam True tvs' $ wrapFloatsAroundTerm flts_all body''
                    return (emptyFloats, env, term')
            | null tvs 
              -> do tick LetFloatFromLet
                    return (flts_all, env `augmentFromFloats` flts_all, body'')
            | otherwise
              -> do tick LetFloatFromLet
                    (poly_binds, body''') <- abstractFloats tvs' env_body flts_all body''
                    term' <- mkLam True tvs' body'''
                    poly_flts <- addPolyBinds env dsc nullControlScope level poly_binds
                    return (poly_flts, env `augmentFromFloats` poly_flts, term')
    addingFloats2 flts_out $ completeTermBind env_x' dsc old_bndr new_bndr term_final level

{-
simplNonRecInCommand is used for
  * [simplCommand] non-recursive lets in commands
-}
-- c.f. Simplify.simplNonRecE
simplNonRecInCommand :: SimplEnv -> DataScope -> ControlScope
                     -> DataScope -> ControlScope -> InBindPair
                     -> InCommand
                     -> SimplM (Floats, OutCommand)
simplNonRecInCommand env dsc csc dsc_rhs csc_rhs pair _comm
  | tracing
  , pprTraceShort "simplNonRecInCommand" (ppr env $$ ppr dsc $$ ppr csc $$
                                          ppr (binderOfPair pair) $$
                                          ppr dsc_rhs $$ ppr csc_rhs $$
                                          ppr pair) False
  = undefined
simplNonRecInCommand env dsc csc dsc_rhs _csc_rhs pair comm
  | BindTerm x (Type ty) <- pair
  = let ty' = substTy env dsc_rhs ty
    in simplCommand env (extendTvSubst dsc x ty') csc comm
  | isTyVar (binderOfPair pair)
  = pprPanic "simplNonRec" (ppr pair)
simplNonRecInCommand env dsc csc dsc_rhs csc_rhs pair comm
  = do
    let x = binderOfPair pair
    preInline <- preInlineUnconditionally env dsc_rhs pair NotTopLevel
    case () of 
      _ | preInline
       -> do
          tick (PreInlineUnconditionally x)
          let (dsc', csc') = extendSubstWithInBindPair dsc csc dsc_rhs csc_rhs pair
          simplCommand env dsc' csc' comm
        | isStrictId x
        , BindTerm _ term <- pair -- A join point could be marked strict by happenstance,
                                  -- but it's hard to see what the meaning would be here
       -> do
          let (csc', _) = enterKontScope env dsc_rhs BoringCtxt (idType x)
              mk = StrictLet { mk_scope   = (dsc, csc)
                             , mk_binder  = x
                             , mk_command = comm }
          simplTermInCommand env dsc_rhs term []
                             (Incoming (dsc_rhs, csc' `setRetKont` mk) Return)
        | otherwise
       -> do
          let (env',  dsc', csc', x')  = enterScope env dsc csc x
              (env'', x'') = addBndrRules env' dsc' csc' x x'
          (flts, env_final, dsc_final, csc_final) <- simplLazyOrJoinBind env'' dsc' csc' x'' dsc_rhs csc_rhs pair
                                                                         NotTopLevel NonRecursive
          addingFloats flts $ simplCommand env_final dsc_final csc_final comm

{-
simplBeta is used for
  * [simplTermInCommand] beta reduction
-}
-- TODO A frustrating amount of this is C&P from simplNonRecInCommand, but
-- previous attempts suggest the cure is worse than the disease.
simplBeta :: SimplEnv -> DataScope
          -> DataScope -> InVar -> InTerm
          -> InTerm -> [ScopedFrame] -> ScopedEnd
          -> SimplM (Floats, OutCommand)
simplBeta env dsc dsc_rhs bndr rhs _body _fs _end
  | tracing
  , pprTraceShort "simplBeta" (ppr env $$ ppr dsc $$
                               ppr (BindTerm bndr rhs) $$
                               ppr dsc_rhs) False
  = undefined
simplBeta env dsc dsc_rhs x rhs body fs end
  | Type ty <- rhs
  = let ty' = substTy env dsc_rhs ty
    in simplTermInCommand env (extendTvSubst dsc x ty') body fs end
  | isTyVar x
  = pprPanic "simplNonRec" (ppr (BindTerm x rhs))
simplBeta env dsc dsc_rhs x rhs body fs end
  = do
    let pair = BindTerm x rhs
    preInline <- preInlineUnconditionally env dsc_rhs pair NotTopLevel
    case () of 
      _ | preInline
       -> do
          tick (PreInlineUnconditionally x)
          let dsc' = extendIdSubst dsc x (Susp dsc_rhs rhs)
          simplTermInCommand env dsc' body fs end
        | isStrictId x
       -> do
          let (csc', _) = enterKontScope env dsc_rhs BoringCtxt (idType x)
              mk = StrictLamBind { mk_dataScope = dsc
                                 , mk_binder   = x
                                 , mk_term     = body
                                 , mk_frames   = fs
                                 , mk_end      = end }
          simplTermInCommand env dsc_rhs rhs []
                             (Incoming (dsc_rhs, csc' `setRetKont` mk) Return)
        | otherwise
       -> do
          let (env',  dsc', x') = enterTermScope env dsc x
              (env'', x'') = addBndrRules env' dsc' nullControlScope x x'
          (flts, env_final, dsc_final) <- simplLazyBind env'' dsc' x'' dsc_rhs x rhs
                                                        NotTopLevel NonRecursive
          addingFloats flts $ simplTermInCommand env_final dsc_final body fs end

-- c.f. Simplify.simplNonRecX
simplNonRecOut :: SimplEnv -> DataScope -> InId -> OutTerm -> SimplM (Floats, SimplEnv, DataScope)
simplNonRecOut env dsc bndr rhs
  | isDeadBinder bndr
  = return (emptyFloats, env, dsc)
  | Coercion co <- rhs
  = return (emptyFloats, env, extendCvSubst dsc bndr co)
  | otherwise
  = let (env', dsc', bndr') = enterTermScope env dsc bndr
    in completeNonRecOut env' dsc' NotTopLevel (isStrictId bndr) bndr bndr' rhs

-- c.f. Simplify.completeNonRecX
completeNonRecOut :: SimplEnv -> DataScope -> TopLevelFlag -> Bool -> InId -> OutId
                  -> OutTerm -> SimplM (Floats, SimplEnv, DataScope)
completeNonRecOut env dsc level isStrict bndr bndr' rhs
  = do
    (flts, rhs')   <- prepareRhsTerm env level bndr' rhs
    (flts', rhs'') <-
      if doFloatFromRhs level NonRecursive isStrict rhs' flts
        then do
             tick LetFloatFromLet
             return (flts, rhs')
        else return (emptyFloats, wrapFloatsAroundTerm flts rhs')
    addingFloats2 flts' $
      completeTermBind (env `augmentFromFloats` flts') dsc bndr bndr' rhs'' level

prepareRhsTerm :: SimplEnv -> TopLevelFlag -> OutId -> OutTerm
               -> SimplM (Floats, OutTerm)
prepareRhsTerm _ _ _ v
  | isTrivialTerm v
  = return (emptyFloats, v)
prepareRhsTerm env level x (Compute ty comm)
  = prepComm comm
  where
    prepComm (Eval term fs Return)
      = do
        (_isExp, flts, fs', co_maybe) <- go (0 :: Int) fs
        case co_maybe of
          Just co -> do
                     -- The situation: We have
                     --     x = compute < term | fs; cast co; ret >
                     -- We will call makeTrivial on < term | fs; ret >. Typically
                     -- this will generate
                     --     x' = compute < term | fs; ret >
                     -- thus giving us
                     --     compute < x' | cast co; ret >
                     -- as the new RHS for x.
                     --
                     -- Note that we already know what the strictness and demand
                     -- of x' should be - namely those of x. So we propagate
                     -- some of the idInfo over.
                     let Pair fromTy _toTy = coercionKind co
                         rhs' = mkCompute fromTy (Eval term fs' Return)
                         info = idInfo x
                         sanitizedInfo = vanillaIdInfo `setStrictnessInfo` strictnessInfo info
                                                       `setDemandInfo` demandInfo info
                     (flts', rhs'') <- makeTrivialWithInfo level (env `augmentFromFloats` flts)
                                         sanitizedInfo rhs'
                     return (flts `addFloats` flts', mkCast rhs'' co)
          Nothing -> return (flts, Compute ty (Eval term fs' Return))
      where
        -- The possibility of a coercion split makes all of this tricky. Suppose
        -- we have
        --
        --   let x = compute (p :: Cont# b). < v | ... `cast` (g :: a ~ b); ret p >
        --
        -- where the ellipses indicate some arguments and inner coercions. We're
        -- going to want to split this in two:
        --   
        --   let x' = compute (q :: Cont# a). < v | ... ret q >
        --       x  = compute (p :: Cont# b). < x' | `cast` (g :: a ~ b); ret p >
        --
        -- Now we get to inline x everywhere and hope to find more redexes (see
        -- Note [Float coercions] in GHC Simplify.lhs).
        -- 
        -- Whether or not we do the split, the arguments in the ellipses will
        -- get let-bound if we learn that this is an expandable application (a PAP
        -- or application of a constructor or CONLIKE function).
        --
        -- The protocol: go nValArgs kont takes the number of value args seen
        -- so far and the remaining continuation. It returns:
        --
        --   * True iff it turns out this is an expandable application
        --   * New bindings being floated
        --   * A list of frames, represented as the ellipses above. If we do a
        --     coercion split, these will end up in the new binding; otherwise,
        --     they will stay in the original one.
        --   * The top-level coercion, if we're doing a coercion split.
        -- 
        -- TODO It would be easier to pass everything downward instead,
        -- employing a bit of knot-tying for the Bool, but for some reason
        -- there's no MonadFix CoreM, so we can't write MonadFix SimplM.
        go :: Int -> [OutFrame] -> SimplM (Bool, Floats, [OutFrame], Maybe OutCoercion)
        go nValArgs (App (Type ty) : fs)
          = prepending (App (Type ty)) $ go nValArgs fs
        go nValArgs (App arg : fs)
          = do
            (isExp, flts, fs', split) <- go (nValArgs+1) fs
            if isExp
              then do
                   (flts', arg') <- makeTrivial level (env `augmentFromFloats` flts) arg
                   return (True,  flts `addFloats` flts', App arg' : fs', split)
              else return (False, flts,                   App arg  : fs', split)
        go nValArgs [Cast co]
          | let Pair fromTy _toTy = coercionKind co
          , not (isUnLiftedType fromTy) -- Don't coercion-split on unlifted type
          = return (isExpFor nValArgs, emptyFloats, [], Just co)
        go nValArgs (Cast co : fs)
          = prepending (Cast co) $ go nValArgs fs
        go nValArgs []
          = return (isExpFor nValArgs, emptyFloats, [], Nothing)
        go _ _
          = return (False, emptyFloats, [], Nothing)
        
        isExpFor nValArgs
          | Var f <- term = isExpandableApp f nValArgs
          | otherwise     = False
        
        prepending f m
          = do { (isExp, flts, fs, split) <- m; return (isExp, flts, f : fs, split) }
    prepComm comm
      = return (emptyFloats, Compute ty comm)
prepareRhsTerm _ _ _ term
  = return (emptyFloats, term)

{-
simplJoinBind is used for
  * [simplRecOrTopPair] recursive join bindings
  * [simplNonRec]       non-recursive join bindings

Nota bene:
    1. It assumes that the binder is *already* simplified,
       and is in scope, and its IdInfo too, except unfolding

    2. It does not check for pre-inline-unconditionallly;
       that should have been done already.
-}
simplJoinBind :: SimplEnv -> DataScope -> ControlScope
              -> OutJoinId -> DataScope -> ControlScope -> InJoinId -> InJoin
              -> RecFlag -> SimplM (Floats, SimplEnv, ControlScope)
simplJoinBind _env _dsc _csc new_bndr _dsc_rhs _csc_rhs old_bndr join recFlag
  | tracing
  , pprTraceShort "simplJoinBind" (ppr old_bndr <+> (if old_bndr == new_bndr then empty else darrow <+> ppr new_bndr) <+>
                                    ppr recFlag $$ ppr join) False
  = undefined
simplJoinBind env dsc csc new_bndr dsc_rhs csc_rhs old_bndr join _recFlag
  = do
    join' <- simplJoin env dsc_rhs csc_rhs join
    -- Note [Don't float from join point] 
    completeJoinBind env dsc csc old_bndr new_bndr join' NotTopLevel

{-
Note [Don't float from join point]

We used to float from nullary join points because we could, but this was
probably never useful as it could not have increased sharing. Float Out is the
proper place to be floating from lambdas and such.

Note [Call ensureDupableKont outside join point]

We need to make sure we call ensureDupableKont whenever the same binding of ret,
the return continuation, appears in two places. When there are no join points in
scope, we can just wait until we see a multi-branch case, but join points make
this trickier: A ret inside a join point might be the only occurrence, but maybe
not. One solution would be to leverage the occurrence analyzer: It could count
the rets just like any other name, and we could add an OccInfo (or a placeholder
binder) to the Compute constructor to hold it. For the time being, we assume
that any join point needs the continuation to be duplicable. At worst, this
might cause an extra iteration if mkDupableKont creates bindings that are only
used once.
-}

simplJoin :: SimplEnv -> DataScope -> ControlScope -> InJoin -> SimplM OutJoin
simplJoin env dsc csc (Join xs comm)
  = do
    let (env', dsc', xs') = enterLamScopes env dsc xs
    comm' <- simplCommandNoFloats env' dsc' csc comm
    return $ Join xs' comm'

completeBind :: SimplEnv -> DataScope -> ControlScope -> InVar -> OutBindPair
             -> TopLevelFlag -> SimplM (Floats, SimplEnv, DataScope, ControlScope)
completeBind env dsc csc x pair level
  | isCoVar x
  = case pair of
      BindTerm _ (Coercion co) -> return (emptyFloats, env, extendCvSubst dsc x co, csc)
      BindJoin _ _             -> pprPanic "completeBind" (ppr x <+> ppr pair)
      _                        -> return (unitFloat (NonRec pair), env, dsc, csc)
  | otherwise
  = do
    (newArity, pair') <- tryEtaExpandRhs env pair
    let oldDef = findRealDef env x
        occInfo = idOccInfo x -- use occ info of *old* binder (new one is zapped)
    newDef <- simplDef env dsc csc level x pair' oldDef
    postInline <- postInlineUnconditionally env pair' occInfo level newDef
    if postInline
      then do
        tick (PostInlineUnconditionally x)
        -- We were going to rename x, but we're substituting intead, so throw
        -- out the new binder
        let (dsc', csc') = extendSubstWithOutBindPair dsc csc (pair' `setPairBinder` x)
        return (emptyFloats, env, dsc', csc')
      else do
        let x' = binderOfPair pair'
            info1 = idInfo x' `setArityInfo` newArity
            (env', x'') = setDef env (x' `setIdInfo` info1) newDef
            info2 = idInfo x''
              -- Demand info: Note [Setting the demand info] in GHC Simplify
              --
              -- We also have to nuke demand info if for some reason
              -- eta-expansion *reduces* the arity of the binding to less
              -- than that of the strictness sig. This can happen: see Note [Arity decrease].
            info3 | defIsEvald newDef
                    || (case strictnessInfo info2 of
                          StrictSig dmd_ty -> newArity < dmdTypeDepth dmd_ty)
                  = zapDemandInfo info2 `orElse` info2
                  | otherwise
                  = info2
            x_final = x'' `setIdInfo` info3
        
        when tracing $ liftCoreM $ putMsg (text "defined" <+> ppr x_final <+> equals <+> ppr newDef)
        return (unitFloat (NonRec (pair' `setPairBinder` x_final)), env', dsc, csc)

completeTermBind :: SimplEnv -> DataScope -> InVar -> OutVar -> OutTerm
                 -> TopLevelFlag -> SimplM (Floats, SimplEnv, DataScope)
completeTermBind env dsc old_id new_id term level
  = do
    (flts, env', dsc', csc') <- completeBind env dsc nullControlScope old_id
                                             (BindTerm new_id term) level
    assert (isEmptyControlScope csc') $
      return (flts, env', dsc')

completeJoinBind :: SimplEnv -> DataScope -> ControlScope
                 -> InVar -> OutVar -> OutJoin -> TopLevelFlag
                 -> SimplM (Floats, SimplEnv, ControlScope)
completeJoinBind env dsc csc old_jv new_jv join level
  = do
    (flts, env', dsc', csc') <- completeBind env dsc csc old_jv
                                             (BindJoin new_jv join) level
    assert (isEmptyDataScope dsc') $
      return (flts, env', csc')

-- (from Simplify.simplUnfolding)
------------------------------
simplDef :: SimplEnv -> DataScope -> ControlScope -> TopLevelFlag
         -> InId
         -> OutBindPair
         -> Definition -> SimplM Definition
-- Note [Setting the new unfolding]
simplDef env dsc csc top_lvl id new_pair def
  = case def of
      BoundToDFun { dfun_bndrs = bndrs, dfun_dataCon = con, dfun_args = args }
        -> do { let (env', dsc', bndrs') = enterLamScopes rule_env dsc bndrs
              ; args' <- mapM (simplTermNoFloats env' dsc' BoringCtxt) args
              ; return (mkBoundToDFun bndrs' con args') }

      BoundToTerm { def_term = term, def_arity = arity
                  , def_src = src, def_guidance = guide }
        | isStableSource src
        -> do { term' <- simplTermNoFloats rule_env dsc RhsCtxt term
              ; case guide of
                  UnfWhen {}   -- Happens for INLINE things
                     -> let guide' = guide { ug_boring_ok = termInlineBoringOk term' }
                        -- Refresh the boring-ok flag, in case expr'
                        -- has got small. This happens, notably in the inlinings
                        -- for dfuns for single-method classes; see
                        -- Note [Single-method classes] in TcInstDcls.
                        -- A test case is Trac #4138
                        in return (mkBoundToTermWithGuidance term' src top_lvl arity guide')
                            -- See Note [Top-level flag on inline rules] in CoreUnfold

                  _other              -- Happens for INLINABLE things
                     -> bottoming `seq` -- See Note [Force bottoming field]
                        do { let dflags = dynFlags env
                           ; return (mkBoundToTerm dflags term' src top_lvl bottoming) } }
                -- If the guidance is UnfIfGoodArgs, this is an INLINABLE
                -- unfolding, and we need to make sure the guidance is kept up
                -- to date with respect to any changes in the unfolding.

      BoundToJoin { def_join = join, def_arity = arity
                  , def_src = src, def_guidance = guide }
        | isStableSource src
        -> do { join' <- simplJoin rule_env dsc csc join
              ; case guide of
                  UnfWhen {}
                     -> let guide' = guide { ug_boring_ok = joinInlineBoringOk join' }
                        in return (mkBoundToJoinWithGuidance join' src arity guide')

                  _other
                     -> bottoming `seq`
                        do { let dflags = dynFlags env
                           ; return (mkBoundToJoin dflags join' src) } }

      _other -> bottoming `seq`
                do { let dflags = dynFlags env
                   ; case new_pair of
                       BindTerm _ term ->
                         return (mkBoundToTerm dflags term InlineRhs top_lvl bottoming)
                       BindJoin _ join ->
                         return (mkBoundToJoin dflags join InlineRhs) }
                     -- We make an  unfolding *even for loop-breakers*.
                     -- Reason: (a) It might be useful to know that they are WHNF
                     --         (b) In TidyPgm we currently assume that, if we want to
                     --             expose the unfolding then indeed we *have* an unfolding
                     --             to expose.  (We could instead use the RHS, but currently
                     --             we don't.)  The simple thing is always to have one.
  where
    bottoming = isBottomingId id
    act      = idInlineActivation id
    rule_env = updMode (updModeForInlineRules act) env
               -- See Note [Simplifying inside InlineRules] in SimplUtils

updModeForInlineRules :: Activation -> SimplifierMode -> SimplifierMode
-- See Note [Simplifying inside InlineRules]
updModeForInlineRules inline_rule_act current_mode
  = current_mode { sm_phase = phaseFromActivation inline_rule_act
                 , sm_inline = True
                 , sm_eta_expand = False }
                 -- For sm_rules, just inherit; sm_rules might be "off"
                 -- because of -fno-enable-rewrite-rules
  where
    phaseFromActivation (ActiveAfter n) = Phase n
    phaseFromActivation _               = InitialPhase

tryEtaExpandRhs :: SimplEnv -> OutBindPair -> SimplM (Arity, OutBindPair)
tryEtaExpandRhs env (BindTerm x v)
  = do (arity, v') <- tryEtaExpandRhsTerm env x v
       return (arity, BindTerm x v')
tryEtaExpandRhs _   (BindJoin j join@(Join xs _))
  = return (length (filter isId xs), BindJoin j join)
      -- TODO Somehow take into account the arity of the outer context

tryEtaExpandRhsTerm :: SimplEnv -> OutId -> OutTerm -> SimplM (Arity, OutTerm)
-- See Note [Eta-expanding at let bindings]
-- and Note [Eta expansion to manifest arity]
tryEtaExpandRhsTerm env bndr rhs
  = do { dflags <- getDynFlags
       ; (new_arity, new_rhs) <- try_expand dflags

       ; warnPprTrace (new_arity < old_arity) __FILE__ __LINE__ (
               (ptext (sLit "Arity decrease:") <+> (ppr bndr <+> ppr old_arity
                <+> ppr new_arity) $$ ppr new_rhs) )
                        -- Note [Arity decrease]
         return (new_arity, new_rhs) }
  where
    try_expand dflags
      | isTrivialTerm rhs
      = return (termArity rhs, rhs)

      | sm_eta_expand (getMode env)      -- Provided eta-expansion is on
      , let new_arity = findRhsArity dflags bndr rhs old_arity
      , new_arity > manifest_arity      -- And the curent manifest arity isn't enough
      = do { tick (EtaExpansion bndr)
           ; return (new_arity, etaExpand new_arity rhs) }
      | otherwise
      = return (manifest_arity, rhs)

    manifest_arity = manifestArity rhs
    old_arity  = idArity bndr

-- Function named after that in GHC Simplify, so named for historical reasons it
-- seems. Basically, do completeBind but don't post-inline or do anything but
-- update the definition and float the binding.
addPolyBind :: SimplEnv -> DataScope -> ControlScope
            -> TopLevelFlag -> OutBind -> SimplM Floats
addPolyBind env dsc csc level (NonRec pair)
  = do
    def <- simplDef env dsc csc level (binderOfPair pair) pair NoDefinition
    let (_, x') = setDef env (binderOfPair pair) def
    return $ unitFloat (NonRec (pair `setPairBinder` x'))
addPolyBind _env _dsc _csc _level bind@(Rec _)
  -- Be conservative like the original simplifier here; recursiveness is tricky
  -- (worst case is we cause extra iteration by not updating definitions now)
  = return $ unitFloat bind

addPolyBinds :: SimplEnv -> DataScope -> ControlScope
             -> TopLevelFlag -> [OutBind] -> SimplM Floats
addPolyBinds _ _ _ _ []
  = return emptyFloats
addPolyBinds env dsc csc level (bind : binds)
  = do
    flts1 <- addPolyBind env dsc csc level bind
    flts2 <- addPolyBinds (env `augmentFromFloats` flts1) dsc csc level binds
    return $ flts1 `addFloats` flts2

-----------------
-- Expressions --
-----------------

simplCommandNoFloats :: SimplEnv -> DataScope -> ControlScope
                     -> InCommand -> SimplM OutCommand
simplCommandNoFloats env dsc csc comm
  = do
    (flts, comm') <- simplCommand env dsc csc comm
    return $ wrapFloats flts comm'

simplCommandNoKontFloats :: SimplEnv -> DataScope -> ControlScope
                         -> InCommand -> SimplM (Floats, OutCommand)
simplCommandNoKontFloats env dsc csc comm
  = do
    (flts, comm') <- simplCommand env dsc csc comm
    return (zapKontFloats flts, wrapKontFloats flts comm')

simplCommand :: SimplEnv -> DataScope -> ControlScope -> InCommand
             -> SimplM (Floats, OutCommand)
simplCommand env dsc csc (Let (Rec pairs) comm)
  = do
    let (env', dsc', csc', _) = enterRecScopes env dsc csc (map binderOfPair pairs)
    (flts, env'', dsc'', csc'') <- simplRec env' dsc' csc' pairs NotTopLevel
    addingFloats flts $ simplCommand env'' dsc'' csc'' comm
simplCommand env dsc csc (Let (NonRec pair) comm)
  = simplNonRecInCommand env dsc csc dsc csc pair comm
simplCommand env dsc csc (Eval term fs end)
  = simplTermInCommand env dsc term (Incoming dsc <$> fs) (Incoming (dsc, csc) end)
simplCommand env dsc csc (Jump args j)
  = simplJump env dsc csc args j

simplTermNoFloats :: SimplEnv -> DataScope -> CallCtxt -> InTerm -> SimplM OutTerm
simplTermNoFloats env dsc ctxt (Compute ty comm)
  = do
    let (csc, ty') = enterKontScope env dsc ctxt ty
    comm' <- simplCommandNoFloats env dsc csc comm
    return $ mkCompute ty' comm'
simplTermNoFloats env dsc ctxt term
  = do
    (flts, term') <- simplTerm env dsc ctxt term
    return $ wrapFloatsAroundTerm flts term'

simplTerm :: SimplEnv -> DataScope -> CallCtxt -> InTerm -> SimplM (Floats, OutTerm)
simplTerm env dsc _ctxt (Type ty)
  = return (emptyFloats, Type (substTy env dsc ty))
simplTerm env dsc _ctxt (Coercion co)
  = return (emptyFloats, Coercion (simplCoercion env dsc co))
simplTerm env dsc ctxt (Compute ty comm)
  = do
    let (csc, ty') = enterKontScope env dsc ctxt ty
    -- Terms are closed with respect to continuation variables, so they can
    -- safely float past this binder. Continuations must *never* float past it,
    -- however, because they necessarily invoke the continuation bound here.
    (flts, comm') <- simplCommandNoKontFloats env dsc csc comm
    return (flts, mkCompute ty' comm')
simplTerm env dsc ctxt v
  = do
    let (csc, ty') = enterKontScope env dsc ctxt ty
    (flts, comm) <- simplTermInCommand env dsc v [] (Incoming (dsc, csc) Return)
    return (emptyFloats, mkCompute ty' (wrapFloats flts comm))
  where ty = substTy env dsc (termType v)

{-
Note [Main simplifier loop]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Most interesting terms go through the following sequence of mutually
tail-recursive functions. There are a few more in between, but these are the
most important steps.

Note that the environment in most of these functions is a SimplTermEnv. This is
because terms and frames cannot have free occurrences of continuation variables
(either join points or the special "ret" continuation), so continuation bindings
are not needed until the End, at which point they are found in the ScopedEnd.

simplTermInCommand     :: SimplEnv -> DataScope -> InTerm
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (Floats, OutCommand)

Simplifies the term, based on its unsimplified context. Inlining and
beta-reduction apply here, as does entering Compute terms.

simplTermInCommandDone :: SimplEnv -> DataScope -> OutTerm
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (Floats, OutCommand)

Called when simplTermInCommand finishes. Packages up the term and the (possible)
coercion to build the initial ArgInfo, then continues onto simplKont.

simplKont              :: SimplEnv -> DataScope -> ArgInfo
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (Floats, OutCommand)

Simplifies the continuation, going frame by frame and then processing the end.
Each frame may interrupt the flow by going into a strict argument, which pulls
the whole state into a StrictArg metacontinuation before jumping into the
argument. After a frame is processed, it is added to the ArgInfo, whose
ai_frames field acts as an accumulator. Rewrite rules fire after all the frames
but before the end.

invokeMetaKont         :: SimplEnv -> DataScope -> ControlScope -> OutTerm
                       -> SimplM (Floats, OutCommand)

Pulls the metacontinuation from the environment, if any, and invokes it. This
may resume an earlier loop from where a strict argument or binding was found.

simplKontDone          :: SimplEnv -> DataScope -> ControlScope -> OutTerm -> OutEnd
                       -> SimplM (Floats, OutCommand)

Called at the very end, either when a Return is encountered with no bound
metacontinuation or after all the branches of a Case are recursed into. Attaches
the Term to the End and returns.
-}

simplTermInCommand     :: SimplEnv -> DataScope -> InTerm
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (Floats, OutCommand)
simplTermInCommand env dsc v fs end
  | tracing
  , pprTraceShort "simplTermInCommand" (
      ppr env $$ ppr dsc $$ ppr v $$ pprMultiScopedKont fs end
    ) False
  = undefined
simplTermInCommand env dsc v fs end
  = let (fs', end') = normalizeKont env (fs, end)
    in simplTermInNormCommand env dsc v fs' end'

normalizeKont :: SimplEnv -> ScopedKont -> ScopedKont
normalizeKont env (fs, end)
  = -- Pull in syntactic continuations from the metacont
    let (fs', end') = doReturns [fs] end
    -- Push casts inward while combining, simplifying them
    in (doCasts Nothing fs', end')
  where
    doReturns :: [[ScopedFrame]] -> ScopedEnd -> ScopedKont
    doReturns acc end
      | (_, csc, Return) <- openScopedEnd end
      , SynKont { mk_frames = fs', mk_end = end' } <- retKont csc
      = doReturns (fs' : acc) end'
      | otherwise
      = (concat (reverse acc), end)
    
    doCasts :: Maybe OutCoercion -> [ScopedFrame] -> [ScopedFrame]
    doCasts Nothing (f : fs)
      = case substScopedFrame env f of
          -- Here and below we use substScoped because we may need to combine
          -- bits of syntax from different scopes; the only way to do so is to
          -- apply their substitutions early. This may be inefficient, but we
          -- hope that we don't do it often.
          Cast co  -> doCasts (Just co) fs
          _        -> f : doCasts Nothing fs
    doCasts Nothing [] = []
    doCasts (Just co) (f : fs)
      = case substScopedFrame env f of
          Cast co' -> doCasts (Just (co `mkTransCo` co')) fs
          App arg   | Just (arg', co') <- castApp arg co
                   -> let f' = case f of
                                 Incoming _ _         -> Incoming emptyDataScope (App arg')
                                   -- We substituted in f by calling substScoped,
                                   -- so arg (hence arg') is an OutTerm, but we
                                   -- never *simplified* it. Hence we clear the
                                   -- environment but keep the frame marked
                                   -- Incoming.
                                 Simplified flag mk _ -> Simplified flag mk (App arg')
                                   -- Adding a cast to arg can't change its
                                   -- ok-to-dup-ness.
                      in f' : doCasts (Just co') fs
          _        -> simplified co `consMaybe` doCasts Nothing (f : fs)
    doCasts (Just co) [] = simplified co `consMaybe` []

    simplified co = Simplified NoDup () . Cast <$> simplOutCoercion_maybe co
                      -- Not OkToDup because an OkToDup frame must not precede a
                      -- NoDup frame

simplTermInNormCommand :: SimplEnv -> DataScope -> InTerm
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (Floats, OutCommand)
simplTermInNormCommand _ _ (Type ty) _ _
  = pprPanic "simplTermInCommand" (ppr ty)
simplTermInNormCommand env_v dsc (Var x) fs end
  = case substId env_v dsc x of
      DoneId x'
        -> do
           let lone | (unScope -> App {}) : _ <- fs = False
                    | otherwise                     = True
               term'_maybe = callSiteInlineTerm env_v x' (activeUnfolding env_v x')
                                                lone fs end
           case term'_maybe of
             Nothing
               -> simplTermInCommandDone env_v (Var x') fs end
             Just term'
               -> do
                  tick (UnfoldingDone x')
                  dump_inline (dynFlags env_v) term' fs end
                  simplTermInCommand env_v emptyDataScope term' fs end
      Done v
        -- Term already simplified (then PostInlineUnconditionally'd), so
        -- don't do any substitutions when processing it again
        -> simplTermInCommand env_v emptyDataScope v fs end
      Susp dsc' v
        -> simplTermInCommand env_v dsc' v fs end
  where
    dump_inline dflags def fs end
      | not (tracing || dopt Opt_D_dump_inlinings dflags) = return ()
      | not (tracing || dopt Opt_D_verbose_core2core dflags)
      = when (isExternalName (idName x)) $
            liftIO $ printInfoForUser dflags alwaysQualify $
                sep [text "Inlining done:", nest 4 (ppr x)]
      | otherwise
      = liftIO $ printInfoForUser dflags alwaysQualify $
           sep [text "Inlining done: " <> ppr x,
                nest 4 (vcat [text "Inlined fn: " <+> nest 2 (ppr def),
                              text "Cont:  " <+> nest 2 (pprMultiScopedKont fs end)])]

simplTermInNormCommand env_v dsc (Compute ty c) fs end
  = do
    let (csc, _) = enterKontScope env_v dsc (kontContext (fs, end)) ty
        csc'     = csc `setRetKont` SynKont { mk_dup    = NoDup
                                            , mk_frames = fs
                                            , mk_end    = end }
    simplCommand env_v dsc csc' c
simplTermInNormCommand env dsc (Coercion co) (f : fs) end
  | (dsc_coCo, Cast coCo) <- openScopedFrame f
  = let co_out   = substCo env dsc      co
        coCo_out = substCo env dsc_coCo coCo
        co'      = simplOutCoercion (mkCoCast coCo_out co_out) in
    simplTermInCommandDone env (Coercion co') fs end
simplTermInNormCommand env_v dsc (Coercion co) fs end
  = let co' = simplCoercion env_v dsc co in
    simplTermInCommandDone env_v (Coercion co') fs end
simplTermInNormCommand env_v dsc v@(Lam x body) (f : fs) end
  -- discard a non-counting tick on a lambda.  This may change the
  -- cost attribution slightly (moving the allocation of the
  -- lambda elsewhere), but we don't care: optimisation changes
  -- cost attribution all the time. (comment from Simplify.simplLam)
  | Tick ti <- f'
  , not (tickishCounts ti)
  = simplTermInCommand env_v dsc v fs end
  | App arg <- f'
  = do
    tick (BetaReduction x)
    simplBeta env_v dsc dsc_k x arg body fs end
  where
    (dsc_k, f') = openScopedFrame f
simplTermInNormCommand env_v dsc term@(Lam {}) fs end
  = do
    let (xs, body) = collectBinders term
        (env_v', dsc', xs') = enterLamScopes env_v dsc xs
    body' <- simplTermNoFloats env_v' dsc' BoringCtxt body
    let (_, csc, _) = openScopedEnd end
        isRhsCtxt   = case getContext csc of { RhsCtxt -> True; _ -> False }
    term' <- mkLam isRhsCtxt xs' body'
    simplTermInCommandDone env_v term' fs end
simplTermInNormCommand env_v _dsc term@(Lit {}) fs end
  = simplTermInCommandDone env_v term fs end

simplTermInCommandDone :: SimplEnv -> OutTerm
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (Floats, OutCommand)

simplTermInCommandDone env_v v fs end
  = simplKont env_v (mkArgInfo env_v v fs end) fs end

{-
Note [simplKont invariants]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

simplKont is used in two rather different situations:
  1. Simplifying the continuation in an Eval command (then possibly invoking rules)
  2. Simplifying the arguments to a jump

The ArgInfo contains a "target" that identifies the case: In case 1, the target
is a TermTarget with the term on the left of the command, and in case 2, the
target identifies a parameterized continuation (either by its body or by its
name).

As a jump has a very specific form, case 2 has some invariants:
  - All the frames are App frames, and there are exactly as many as the arity
    of the join point
  - The end is a Return
-}

simplKont :: SimplEnv 
          -> ArgInfo
          -> [ScopedFrame] -> ScopedEnd
          -> SimplM (Floats, OutCommand)
simplKont env (ai@ArgInfo { ai_strs = [] }) fs end
  -- We've run out of strictness arguments, meaning the call is definitely bottom
  | hasTerm
  , not trivialKont -- Don't bother throwing away a trivial continuation
  = simplKontDone env term (Case (mkWildValBinder ty) []) -- Skips invokeMetaKont
  | not hasTerm
  , not trivialKont
  = warnPprTrace (not hasTerm) __FILE__ __LINE__
      (hang (text "Join point bottoms out at less than apparent arity:") 2
            (ppr ai $$ pprMultiScopedKont fs end)) $
    simplKont env (ai { ai_strs = [False] }) fs end
  where
    trivialKont | all (isTrivialFrame . unScope) fs
                , (_, csc, Return) <- openScopedEnd end
                , Stop {} <- retKont csc
                = True
                | otherwise
                = False
    
    hasTerm = argInfoHasTerm ai
    term = argInfoToTerm ai
    ty = termType term
simplKont env ai (Simplified _ _ f : fs) end
  = simplKont env (addFrameToArgInfo ai f) fs end
simplKont env ai (f : fs) end
  = case openScopedFrame f of
      (dsc', f') -> simplKontFrame env dsc' ai f' fs end
simplKont env ai [] end
  = case openScopedEnd end of
      (dsc', csc, end') -> simplKontEnd env dsc' csc ai end'

simplKontFrame :: SimplEnv -> DataScope -> ArgInfo
               -> InFrame -> [ScopedFrame] -> ScopedEnd
               -> SimplM (Floats, OutCommand)
simplKontFrame env dsc ai f fs end
  | tracing
  , pprTraceShort "simplKontFrame" (
      ppr env $$ ppr dsc $$ ppr ai $$ ppr f $$ pprMultiScopedKont fs end
    ) False
  = undefined
simplKontFrame env dsc ai (Cast co) fs end
  -- Since the frames were already normalized, we know there's nothing clever to
  -- do here
  = simplKont env (addFrameToArgInfo ai (Cast co')) fs end
  where
    co' = simplCoercion env dsc co
simplKontFrame env dsc ai (App (Type tyArg)) fs end
  = do
    let ty' = substTy env dsc tyArg
    simplKont env (addFrameToArgInfo ai (App (Type ty'))) fs end
simplKontFrame _ _ (ArgInfo { ai_discs = [] }) _ _ _
  = pprPanic "simplKontFrame" (text "out of discounts??")
simplKontFrame _ _ ai@(ArgInfo { ai_strs = [] }) f _ _
  = pprPanic "simplKontFrame" (text "should have dealt with bottom already" $$ ppr ai $$ ppr f)
simplKontFrame env dsc ai@(ArgInfo { ai_strs = str:_
                                   , ai_discs = disc:_ }) (App arg) fs end
  | str
  = do
    -- Push the current evaluation state into the environment as a
    -- meta-continuation. We'll continue with the rest of the frames when we
    -- finish simplifying the term. This, of course, reflects left-to-right
    -- call-by-value evaluation.
    let mk = StrictArg { mk_dup = NoDup
                       , mk_argInfo = ai
                       , mk_frames = fs
                       , mk_context = cci
                       , mk_end = end }
        (csc, _ty') = enterKontScope env dsc cci (termType arg)
        csc' = csc `setRetKont` mk
    simplCommand env dsc csc' (Eval arg [] Return)
  | otherwise
  = do
    -- Don't float out of lazy arguments (see Simplify.rebuildCall)
    arg_final <- simplTermNoFloats env dsc cci arg
    simplKont env (addFrameToArgInfo ai (App arg_final)) fs end
  where
    cci | ai_encl ai = RuleArgCtxt
        | disc > 0   = DiscArgCtxt
        | otherwise  = BoringCtxt
simplKontFrame env _dsc ai f@(Tick _) fs end
  -- FIXME Tick handling is actually rather delicate! In fact, we should
  -- (somehow) be putting a float barrier here (see Simplify.simplTick).
  = simplKont env (addFrameToArgInfo ai f) fs end

simplKontEnd :: SimplEnv -> DataScope -> ControlScope
             -> ArgInfo
             -> InEnd
             -> SimplM (Floats, OutCommand)
simplKontEnd env dsc csc ai e
  | tracing
  , pprTraceShort "simplKontEnd" (
      ppr env $$ ppr dsc $$ ppr csc $$ ppr ai $$ ppr e
    ) False
  = undefined
{-
If simplifying a Jump, rules cannot apply, there cannot be a coercion, the end
must be Return, and the metacontinuation will not be invoked (it is only invoked
by a Return from an actual Eval command). Thus we skip out here.
-}
simplKontEnd _env _dsc _csc (ArgInfo { ai_target = JumpTarget j, ai_frames = fs }) end
  = assert (isReturn end && all isAppFrame fs) $ -- Note [simplKont invariants]
    return (emptyFloats, Jump [ arg | App arg <- reverse fs ] j)
simplKontEnd env _dsc _csc (ArgInfo { ai_target = JoinTarget join, ai_frames = fs }) end
  = assert (isReturn end && all isAppFrame fs) $ -- Note [simplKont invariants]
    do
    let (dsc', csc', Join xs comm) = openScopedJoin join
        args = [ arg | App arg <- reverse fs ]
    ((env', dsc''), flts) <- mapAccumLM (\(env, dsc) (x, v) -> twist <$> simplNonRecOut env dsc x v)
                                        (env, dsc') (zip xs args)
    addingFloats (catFloats flts) $ simplCommand env' dsc'' csc' comm
  where
    twist (a, b, c) = ((b, c), a)
simplKontEnd env dsc csc ai@(ArgInfo { ai_target = TermTarget (Var fun), ai_rules = rules }) end
  | not (null rules)
  = do
    let (args, extraFrames) = argInfoSpanArgs ai
    match_maybe <- tryRules env rules fun args
    case match_maybe of
      Just (ruleRhs, extraArgs) ->
        let simplFrames = map (Simplified NoDup ()) (map App extraArgs ++ extraFrames)
        in simplTermInCommand env emptyDataScope ruleRhs simplFrames (Incoming (dsc, csc) end)
      Nothing -> simplKontAfterRules env dsc csc ai end    
simplKontEnd env dsc csc ai end
  = simplKontAfterRules env dsc csc ai end

simplKontAfterRules :: SimplEnv -> DataScope -> ControlScope
                    -> ArgInfo
                    -> InEnd
                    -> SimplM (Floats, OutCommand)
simplKontAfterRules _ _ _ ai@(ArgInfo { ai_target = target }) end
  | not (argInfoHasTerm ai)
  = pprPanic "simplKontAfterRules" (text "Not a term target:" <+> ppr target $$
                                    text "Continuation:" <+> ppr end)
simplKontAfterRules env dsc csc ai (Case x alts)
  | TermTarget (Lit lit) <- ai_target ai
  , not (litIsLifted lit)
  , null (ai_frames ai) -- TODO There could be ticks here; deal with them
  = do
    tick (KnownBranch x)
    case findAlt (LitAlt lit) alts of
      Nothing -> missingAlt x alts
      Just (Alt _ binds rhs) -> bindCaseBndr binds rhs
  | Just (dc, tyArgs, valArgs) <- termIsConApp_maybe env (getUnfoldingInRuleMatch env) scrut
  = do
    tick (KnownBranch x)
    case findAlt (DataAlt dc) alts of
      Nothing -> missingAlt x alts
      Just (Alt DEFAULT binds rhs) -> bindCaseBndr binds rhs
      Just (Alt _       binds rhs) -> knownCon env dsc csc scrut dc tyArgs valArgs x binds rhs 
  where
    scrut = assert (argInfoHasTerm ai) $ argInfoToTerm ai
              -- Note [simplKont invariants]
    bindCaseBndr binds rhs
      = assert (null binds) $ do
        (flts, env', dsc') <- simplNonRecOut env dsc x scrut
        addingFloats flts $ simplCommand env' dsc' csc rhs
simplKontAfterRules env dsc csc ai (Case case_bndr [Alt _ bndrs rhs])
 | all isDeadBinder bndrs       -- bndrs are [InId]
 
 , if isUnLiftedType (idType case_bndr)
   then elim_unlifted        -- Satisfy the let-binding invariant
   else elim_lifted
  = do  { -- pprTraceShort "case elim" (vcat [ppr case_bndr, ppr (exprIsHNF scrut),
          --                            ppr ok_for_spec,
          --                            ppr scrut]) $
          tick (CaseElim case_bndr)
        ; (flts, env', dsc') <- simplNonRecOut env dsc case_bndr scrut
        ; addingFloats flts $ simplCommand env' dsc' csc rhs }
  where
    elim_lifted   -- See Note [Case elimination: lifted case]
      = termIsHNF scrut
     || (is_plain_seq && ok_for_spec)
              -- Note: not the same as exprIsHNF
     || case_bndr_evald_next rhs
 
    elim_unlifted
      | is_plain_seq = termOkForSideEffects scrut
            -- The entire case is dead, so we can drop it,
            -- _unless_ the scrutinee has side effects
      | otherwise    = ok_for_spec
            -- The case-binder is alive, but we may be able
            -- turn the case into a let, if the expression is ok-for-spec
            -- See Note [Case elimination: unlifted case]
 
    ok_for_spec      = termOkForSpeculation scrut
    is_plain_seq     = isDeadBinder case_bndr -- Evaluation *only* for effect
 
    case_bndr_evald_next :: SeqCoreCommand -> Bool
      -- See Note [Case binder next]
    case_bndr_evald_next (Eval (Var v) _ _) = v == case_bndr
    case_bndr_evald_next _                  = False
      -- Could allow for let bindings,
      -- but the original code in Simplify suggests doing so would be expensive
      
    scrut = argInfoToTerm ai
simplKontAfterRules env dsc csc ai (Case x alts)
  = do
    (flts, csc') <- if length alts > 1
                       then ensureDupableKont env dsc csc -- we're about to duplicate the context
                       else return (emptyFloats, csc)
    let env'  = env `augmentFromFloats` flts
        scrut = argInfoToTerm ai
    
    (co_m, x', alts') <- simplAlts env' dsc csc' scrut x alts
    let ai' = case co_m of
                Just co -> ai { ai_frames = Cast co : ai_frames ai }
                Nothing -> ai
    dflags <- getDynFlags
    (fs', end') <- mkCase dflags x' alts'
    let ai_final = addFramesToArgInfo ai' fs'
        term_final = argInfoToTerm ai_final
    addingFloats flts $ simplKontDone env' term_final end'
simplKontAfterRules env dsc csc ai Return
  = invokeMetaKont env dsc csc (argInfoToTerm ai)

-- | Pulls the metacontinuation from the environment and invokes it. This
-- function determines the semantics of each metacontinuation constructor.
invokeMetaKont :: SimplEnv -> DataScope -> ControlScope -> OutTerm
               -> SimplM (Floats, OutCommand)
invokeMetaKont env dsc csc term
  | tracing
  , let mk = retKont csc
  , not (isStopMetaKont mk)
  , pprTraceShort "invokeMetaKont" (ppr mk $$ ppr term) False
  = undefined
  | otherwise
  = case retKont csc of
      Stop {}
        -> simplKontDone env term Return
      SynKont { mk_frames = fs, mk_end = end }
        -> warnPprTrace True __FILE__ __LINE__
             (text "SynKont lasted until invokeMetaKont" $$ ppr env $$ ppr term) $
             simplTermInCommand env dsc term fs end
      StrictArg { mk_argInfo = ai'
                , mk_frames  = fs
                , mk_end     = end }
        -> simplKont env
                     (addFrameToArgInfo ai' (App term)) fs end
      StrictLet { mk_scope   = (dsc_outer, csc_outer)
                , mk_binder  = bndr
                , mk_command = comm }
        -> do
           (flts, env', dsc') <- simplNonRecOut env dsc_outer bndr term
           addingFloats flts $ simplCommand env' dsc' csc_outer comm
      StrictLamBind { mk_dataScope = dsc_outer
                    , mk_binder    = bndr
                    , mk_term      = body
                    , mk_frames    = fs
                    , mk_end       = end }
        -> do
           (flts, env', dsc') <- simplNonRecOut env dsc_outer bndr term
           addingFloats flts $ simplTermInCommand env' dsc' body fs end

simplKontDone :: SimplEnv -> OutTerm -> OutEnd
              -> SimplM (Floats, OutCommand)
simplKontDone env term end
  | tracing
  , pprTraceShort "simplKontDone" (ppr env $$ ppr term $$ ppr end) False
  = undefined
  | Compute _ (Eval term' fs Return) <- term
      -- Common code path: simplKontAfterRules -> invokeKont -> simplKontDone
  = return (emptyFloats, Eval term' fs end)
  | otherwise
  = return (emptyFloats, Eval term [] end)

-----------
-- Jumps --
-----------

simplJump :: SimplEnv -> DataScope -> ControlScope -> [InArg] -> InJoinId -> SimplM (Floats, OutCommand)
simplJump env dsc csc args j
  | tracing
  , pprTraceShort "simplJump" (ppr env $$ ppr dsc $$ ppr csc $$
                               parens (pprWithCommas ppr args) $$ pprBndr LetBind j)
    False
  = undefined
simplJump env dsc csc args j
  = case substJv env csc j of
      DoneId j'
        -> do
           let -- Pretend to callSiteInline that we're just applying a bunch of
               -- arguments to a function
               rhs'_maybe = callSiteInlineJoin env j' (activeUnfolding env j') frames end
          
           case rhs'_maybe of
             Nothing
               -> simplKont env (mkJumpArgInfo env j' frames) frames end
                    -- Activate case 2 of simplKont (Note [simplKont invariants])
             Just join'
               -> do
                  tick (UnfoldingDone j')
                  dump_inline (dynFlags env) join'
                  reduce env emptyDataScope (zapControlScope csc) join'
      Done pk
        -> reduce env emptyDataScope (zapControlScope csc) pk
      Susp (dsc', csc') pk
        -> reduce env dsc' csc' pk
  where
    frames = map (Incoming dsc . App) args
    end    = Simplified OkToDup (retType csc, Stop { mk_context = getContext csc }) Return
    reduce env_join dsc_join csc_join join
      = simplKont env_join
                  (mkJoinArgInfo env_join (Incoming (dsc_join, csc_join) join) frames)
                  frames end
    
    dump_inline dflags def
      | not (tracing || dopt Opt_D_dump_inlinings dflags) = return ()
      | not (tracing || dopt Opt_D_verbose_core2core dflags)
      = when (isExternalName (idName j)) $
            liftIO $ printInfoForUser dflags alwaysQualify $
                sep [text "Inlining done:", nest 4 (ppr j)]
      | otherwise
      = liftIO $ printInfoForUser dflags alwaysQualify $
           sep [text "Inlining done: " <> ppr j,
                nest 4 (vcat [text "Inlined join point: " <+> nest 2 (ppr def),
                              text "Args:  " <+> ppr args])]

-------------------
-- Case handling --
-------------------

simplAlts :: SimplEnv -> DataScope -> ControlScope -> OutTerm -> InId -> [InAlt]
          -> SimplM (Maybe OutCoercion, OutId, [OutAlt])
simplAlts env dsc csc scrut case_bndr alts
  = do  { let env0 = env

        ; let (alt_env, dsc1, case_bndr1) = enterTermScope env0 dsc case_bndr

        ; let fam_envs = getFamEnvs alt_env
        ; (alt_dsc, co_m, case_bndr') <- improveSeq fam_envs dsc1
                                                    case_bndr case_bndr1 alts
        ; let scrut' = case co_m of
                         Just co -> mkCast scrut co
                         Nothing -> scrut
        ; (imposs_deflt_cons, in_alts) <- prepareAlts scrut' case_bndr' alts
          -- NB: it's possible that the returned in_alts is empty: this is handled
          -- by the caller (rebuildCase) in the missingAlt function

        ; alts' <- mapM (simplAlt alt_env alt_dsc csc (Just scrut') imposs_deflt_cons case_bndr') in_alts
        ; -- pprTrace "simplAlts" (ppr case_bndr $$ ppr alts_ty $$ ppr alts_ty' $$ ppr alts $$ ppr cont') $
          return (co_m, case_bndr', alts') }

improveSeq :: (FamInstEnv, FamInstEnv) -> DataScope
           -> InId -> OutId -> [InAlt]
           -> SimplM (DataScope, Maybe OutCoercion, OutId)
-- Note [Improving seq] in GHC's Simplify
improveSeq fam_envs dsc case_bndr case_bndr1 [Alt DEFAULT _ _]
  | not (isDeadBinder case_bndr) -- Not a pure seq!  See Note [Improving seq]
  , Just (co, ty2) <- topNormaliseType_maybe fam_envs (idType case_bndr1)
  = do { case_bndr2 <- mkSysLocalM (fsLit "nt") ty2
        ; let rhs  = Done (mkCast (Var case_bndr2) (mkSymCo co))
              dsc2 = extendIdSubst dsc case_bndr rhs
        ; return (dsc2, Just co, case_bndr2) }

improveSeq _ dsc _ case_bndr1 _
  = return (dsc, Nothing, case_bndr1)

simplAlt :: SimplEnv -> DataScope -> ControlScope
         -> Maybe OutTerm -> [AltCon] -> OutId
         -> InAlt
         -> SimplM OutAlt
simplAlt env dsc csc _ notAmong caseBndr (Alt DEFAULT bndrs rhs)
  = assert (null bndrs) $ do
    let (env', _) = setDef env caseBndr (NotAmong notAmong)
    rhs' <- simplCommandNoFloats env' dsc csc rhs
    return $ Alt DEFAULT [] rhs'
simplAlt env dsc csc scrut_maybe _ caseBndr (Alt (LitAlt lit) bndrs rhs)
  = assert (null bndrs) $ do
    env' <- addAltUnfoldings env scrut_maybe caseBndr (Lit lit)
    rhs' <- simplCommandNoFloats env' dsc csc rhs
    return $ Alt (LitAlt lit) [] rhs'
simplAlt env dsc csc scrut' _ case_bndr' (Alt (DataAlt con) vs rhs)
  = do  {       -- Deal with the pattern-bound variables
                -- Mark the ones that are in ! positions in the
                -- data constructor as certainly-evaluated.
                -- NB: enterLamScopes preserves this eval info
        ; let vs_with_evals = add_evals (dataConRepStrictness con)
        ; let (env', dsc', vs') = enterLamScopes env dsc vs_with_evals

                -- Bind the case-binder to (con args)
        ; let inst_tys' = tyConAppArgs (idType case_bndr')
              con_app :: OutTerm
              con_app = mkConstruction con inst_tys' (map mkVarArg vs')

        ; env'' <- addAltUnfoldings env' scrut' case_bndr' con_app
        ; rhs' <- simplCommandNoFloats env'' dsc' csc rhs
        ; return $ Alt (DataAlt con) vs' rhs' }
  where
        -- add_evals records the evaluated-ness of the bound variables of
        -- a case pattern.  This is *important*.  Consider
        --      data T = T !Int !Int
        --
        --      case x of { T a b -> < T | $ (a+1); $ b; ret > }
        --
        -- We really must record that b is already evaluated so that we don't
        -- go and re-evaluate it when constructing the result.
        -- See Note [Data-con worker strictness] in MkId.lhs
    add_evals the_strs
        = go vs the_strs
        where
          go [] [] = []
          go (v:vs') strs | isTyVar v = v : go vs' strs
          go (v:vs') (str:strs)
            | isMarkedStrict str = evald_v  : go vs' strs
            | otherwise          = zapped_v : go vs' strs
            where
              zapped_v = zapIdOccInfo v   -- See Note [Case alternative occ info]
              evald_v  = zapped_v `setIdUnfolding` evaldUnfolding
          go _ _ = pprPanic "cat_evals" (ppr con $$ ppr vs $$ ppr the_strs)

addAltUnfoldings :: SimplEnv -> Maybe OutTerm -> OutId -> OutTerm -> SimplM SimplEnv
addAltUnfoldings env scrut case_bndr con_app
  = do { let con_app_def = mkTermDef env NotTopLevel con_app
             (env1, _) = setDef env case_bndr con_app_def

             -- See Note [Add unfolding for scrutinee]
             (env2, _) = case scrut of
                      Just (Var v)           -> setDef env1 v con_app_def
                      Just (Compute _ (Eval (Var v) [Cast co] Return))
                                             -> setDef env1 v $
                                                mkTermDef env1 NotTopLevel (mkCast con_app (mkSymCo co))
                      _                      -> (env1, undefined)

       ; when tracing $ pprTraceShort "addAltUnf" (vcat [ppr case_bndr <+> ppr scrut, ppr con_app]) return ()
       ; return env2 }

simplVar :: SimplEnv -> DataScope -> InVar -> SimplM OutTerm
simplVar env dsc x
  | isTyVar x = return $ Type (substTyVar env dsc x)
  | isCoVar x = return $ Coercion (substCoVar env dsc x)
  | otherwise
  = case substId env dsc x of
      DoneId x' -> return $ Var x'
      Done v -> return v
      Susp dsc' v -> simplTermNoFloats env dsc' BoringCtxt v

knownCon :: SimplEnv -> DataScope -> ControlScope
         -> OutTerm                             -- The scrutinee
         -> DataCon -> [OutType] -> [OutTerm]   -- The scrutinee (in pieces)
         -> InId -> [InBndr] -> InCommand       -- The alternative
         -> SimplM (Floats, OutCommand)
knownCon env dsc csc scrut dc tyArgs valArgs bndr binds rhs
  = do
    (flts, env', dsc')    <- bindArgs env dsc binds valArgs []
    (flts', env'', dsc'') <- bindCaseBndr env' dsc'
    addingFloats (flts `addFloats` flts') $ simplCommand env'' dsc'' csc rhs
  where
    -- If b isn't dead, make sure no bound variables are marked dead
    zap_occ b | isDeadBinder bndr = b
              | otherwise         = zapIdOccInfo b
    
    bindArgs env' dsc' []      _                fltss = return (catFloats (reverse fltss), env', dsc')
    bindArgs env' dsc' (b:bs') (Type ty : args) fltss = assert (isTyVar b) $
                                                        bindArgs env' (extendTvSubst dsc' b ty) bs' args fltss
    bindArgs env' dsc' (b:bs') (arg : args)     fltss = assert (isId b) $ do
                                                        let b' = zap_occ b
                                                        (flts, env'', dsc'') <- simplNonRecOut env' dsc' b' arg
                                                        bindArgs env'' dsc'' bs' args (flts:fltss)
    bindArgs _    _    _       _                _     = pprPanic "bindArgs" $ ppr dc $$ ppr binds $$ ppr valArgs $$
                                                                              text "scrut:" <+> ppr scrut
    
       -- It's useful to bind bndr to scrut, rather than to a fresh
       -- binding      x = Con arg1 .. argn
       -- because very often the scrut is a variable, so we avoid
       -- creating, and then subsequently eliminating, a let-binding
       -- BUT, if scrut is a not a variable, we must be careful
       -- about duplicating the arg redexes; in that case, make
       -- a new con-app from the args (comment from Simplify.knownCon)
    bindCaseBndr env dsc
      | isDeadBinder bndr   = return (emptyFloats, env, dsc)
      | isTrivialTerm scrut = return (emptyFloats, env, extendIdSubst dsc bndr (Done scrut))
      | otherwise           = do { args <- mapM (simplVar env dsc) binds
                                         -- tyArgs are aready OutTypes,
                                         -- but binds are InBndrs
                                 ; let con_app = mkCompute (substTy env dsc (idType bndr)) $
                                                 Eval (Var (dataConWorkId dc))
                                                      (map (App . Type) tyArgs ++
                                                       map App args)
                                                       Return
                                 ; simplNonRecOut env dsc bndr con_app }

missingAlt :: Id -> [InAlt] -> SimplM (Floats, OutCommand)
                -- This isn't strictly an error, although it is unusual.
                -- It's possible that the simplifer might "see" that
                -- an inner case has no accessible alternatives before
                -- it "sees" that the entire branch of an outer case is
                -- inaccessible.  So we simply put an error case here instead.
                -- (comment from Simplify.missingAlt)
missingAlt case_bndr _
  = warnPprTrace True __FILE__ __LINE__ ( ptext (sLit "missingAlt") <+> ppr case_bndr )
    return (emptyFloats, impossibleCommand)

-------------------
-- Rewrite rules --
-------------------

tryRules :: SimplEnv -> [CoreRule]
         -> Id -> [OutArg]
         -> SimplM (Maybe (OutTerm, [OutArg]))
tryRules env rules fn args
  | null rules
  = return Nothing
  | otherwise
  = do { dflags <- getDynFlags
       ; case lookupRule dflags (getInScopeSet env, getUnfoldingInRuleMatch env)
                         (activeRule env) fn coreArgs rules of {
           Nothing               -> return Nothing ;   -- No rule matches
           Just (rule, rule_rhs) ->
             do { checkedTick (RuleFired (ruleName rule))
                ; dump dflags rule rule_rhs
                ; let term' = termFromCoreExpr rule_rhs
                ; let extraArgs = drop (ruleArity rule) args
                      -- (ruleArity rule) says how many args the rule consumed
                      
                ; return (Just (term', extraArgs)) }}}
  where
    coreArgs = map termToCoreExpr args
        
    dump dflags rule rule_rhs
      | dopt Opt_D_dump_rule_rewrites dflags
      = log_rule dflags Opt_D_dump_rule_rewrites "Rule fired" $ vcat
          [ text "Rule:" <+> ftext (ruleName rule)
          , text "Before:" <+> hang (ppr fn) 2 (sep (map ppr $ take arity args))
          , text "After: " <+> ppr rule_rhs
          , text "Cont:  " <+> pprKont (map App $ drop arity args, Return) ]

      | dopt Opt_D_dump_rule_firings dflags
      = log_rule dflags Opt_D_dump_rule_firings "Rule fired:" $
          ftext (ruleName rule)

      | otherwise
      = return ()
      where
        arity = ruleArity rule

    log_rule dflags flag hdr details = liftIO . dumpSDoc dflags flag "" $
      sep [text hdr, nest 4 details]

--------------
-- Inlining --
--------------

-- Based on preInlineUnconditionally in SimplUtils; see comments there
preInlineUnconditionally :: SimplEnv -> DataScope -> InBindPair
                         -> TopLevelFlag -> SimplM Bool
preInlineUnconditionally env_x _dsc_rhs pair level
  = do
    ans <- go (getMode env_x) <$> getDynFlags
    when tracing $ liftCoreM $ putMsg $ text "preInline" <+> ppr x <> colon <+> text (show ans)
    return ans
  where
    x = binderOfPair pair
  
    go mode dflags
      | not active                              = False
      | isStableUnfolding (idUnfolding x)       = False  -- Note [InlineRule and preInlineUnconditionally] in GHC SimplUtils
      | not enabled                             = False
      | TopLevel <- level, isBottomingId x      = False
      | isCoVar x                               = False
      | otherwise = case idOccInfo x of
                      IAmDead                  -> True
                      OneOcc inLam True intCxt -> try_once inLam intCxt
                      _                        -> False
      where
        active = isActive (sm_phase mode) act
        act = idInlineActivation x
        enabled = gopt Opt_SimplPreInlining dflags
        try_once inLam intCxt
          | not inLam = isNotTopLevel level || early_phase
          | BindTerm _ rhs <- pair = intCxt && canInlineTermInLam rhs
          | otherwise = False
        canInlineInLam c
          | Just v <- asValueCommand c   = canInlineTermInLam v
          | otherwise                    = False
        canInlineTermInLam (Lit _)       = True
        canInlineTermInLam (Lam x t)     = isRuntimeVar x
                                         || canInlineTermInLam t
        canInlineTermInLam (Compute _ c) = canInlineInLam c
        canInlineTermInLam _             = False
        early_phase = case sm_phase mode of
                        Phase 0 -> False
                        _       -> True

-- Based on postInlineUnconditionally in SimplUtils; see comments there
postInlineUnconditionally :: SimplEnv -> OutBindPair -> OccInfo -> TopLevelFlag
                          -> Definition
                          -> SimplM Bool
postInlineUnconditionally env pair occ_info level def
  = do
    ans <- go (getMode env) <$> getDynFlags
    when tracing $ liftCoreM $ putMsg $ text "postInline" <+> ppr (binderOfPair pair) <> colon <+> text (show ans)
    return ans
  where
    go mode dflags
      | not active                  = False
      | isWeakLoopBreaker occ_info  = False
      | isExportedId x              = False
      | isTopLevel level            = False
      | defIsStable def             = False
      | trivial                     = True
      | otherwise
      = case occ_info of
          OneOcc in_lam _one_br int_cxt
            ->     defIsSmallEnoughToInline dflags def
               && (not in_lam ||
                    (defIsCheap def && int_cxt))
          IAmDead -> True
          _ -> False

      where
        x = binderOfPair pair
        active = isActive (sm_phase mode) (idInlineActivation x)
        trivial = case pair of
          BindTerm _ term -> isTrivialTerm term
          BindJoin _ join -> isTrivialJoin join

computeDiscount :: DynFlags -> Arity -> [Int] -> Int -> [ArgSummary] -> CallCtxt
                -> Int
computeDiscount dflags uf_arity arg_discounts res_discount arg_infos cont_info
         -- We multiple the raw discounts (args_discount and result_discount)
        -- ty opt_UnfoldingKeenessFactor because the former have to do with
        --  *size* whereas the discounts imply that there's some extra 
        --  *efficiency* to be gained (e.g. beta reductions, case reductions) 
        -- by inlining.

  = 10          -- Discount of 1 because the result replaces the call
                -- so we count 1 for the function itself

    + 10 * length (take uf_arity arg_infos)
                  -- Discount of (un-scaled) 1 for each arg supplied, 
                  -- because the result replaces the call

    + round (ufKeenessFactor dflags *
             fromIntegral (arg_discount + res_discount'))
  where
    arg_discount = sum (zipWith mk_arg_discount arg_discounts arg_infos)

    mk_arg_discount _              TrivArg    = 0 
    mk_arg_discount _        NonTrivArg = 10
    mk_arg_discount discount ValueArg   = discount 

    res_discount' = case cont_info of
                        BoringCtxt  -> 0
                        CaseCtxt    -> res_discount  -- Presumably a constructor
                        ValAppCtxt  -> res_discount  -- Presumably a function
                        _           -> 40 `min` res_discount
                -- ToDo: this 40 `min` res_dicount doesn't seem right
                --   for DiscArgCtxt it shouldn't matter because the function will
                --    get the arg discount for any non-triv arg
                --   for RuleArgCtxt we do want to be keener to inline; but not only
                --    constructor results
                --   for RhsCtxt I suppose that exposing a data con is good in general
                --   And 40 seems very arbitrary
                --
                -- res_discount can be very large when a function returns
                -- constructors; but we only want to invoke that large discount
                -- when there's a case continuation.
                -- Otherwise we, rather arbitrarily, threshold it.  Yuk.
                -- But we want to aovid inlining large functions that return 
                -- constructors into contexts that are simply "interesting"

callSiteInlineTerm :: SimplEnv -> OutId -> Bool -> Bool -> [ScopedFrame] -> ScopedEnd -> Maybe OutTerm
callSiteInlineTerm env id active_unfolding lone_variable fs end
  = case findDef env id of 
      -- idUnfolding checks for loop-breakers, returning NoUnfolding
      -- Things with an INLINE pragma may have an unfolding *and* 
      -- be a loop breaker  (maybe the knot is not yet untied)
      BoundToTerm { def_term = unf_term, def_level = is_top 
                  , def_isWorkFree = is_wf,  def_arity = uf_arity
                  , def_guidance = guidance, def_isExpandable = is_exp }
                  | active_unfolding -> let (arg_infos, cont_info) = distillKont env fs end
                                        in tryUnfolding (dynFlags env) id lone_variable
                                            arg_infos cont_info unf_term (isTopLevel is_top)
                                            is_wf is_exp uf_arity guidance
                  | let dflags = dynFlags env
                  , tracing || dopt Opt_D_dump_inlinings dflags && dopt Opt_D_verbose_core2core dflags
                  -> pprTrace "Inactive unfolding:" (ppr id) Nothing
                  | otherwise -> Nothing
      _           -> Nothing

callSiteInlineJoin :: SimplEnv -> OutJoinId -> Bool -> [ScopedFrame] -> ScopedEnd -> Maybe OutJoin
callSiteInlineJoin env id active_unfolding fs end
  = case findDef env id of 
      -- idUnfolding checks for loop-breakers, returning NoUnfolding
      -- Things with an INLINE pragma may have an unfolding *and* 
      -- be a loop breaker  (maybe the knot is not yet untied)
      BoundToJoin { def_join = unf_join, def_arity = uf_arity
                  , def_guidance = guidance }
                  | active_unfolding -> let (arg_infos, cont_info) = distillKont env fs end
                                        in tryUnfolding (dynFlags env) id False
                                            arg_infos cont_info unf_join
                                            False True True
                                              -- top-level no, work-free yes, expandable yes
                                            uf_arity guidance
                  | let dflags = dynFlags env
                  , tracing || dopt Opt_D_dump_inlinings dflags && dopt Opt_D_verbose_core2core dflags
                  -> pprTrace "Inactive unfolding:" (ppr id) Nothing
                  | otherwise -> Nothing
      _           -> Nothing

-- Impedence mismatch between Sequent Core code and logic from CoreUnfold.
distillKont :: SimplEnv -> [ScopedFrame] -> ScopedEnd -> ([ArgSummary], CallCtxt)
distillKont env fs end = (mapMaybe (doFrame . substScopedFrame env) fs, doEnd (substScopedEnd env end))
  where
    doFrame (App v)    | not (isTypeArg v)
                       = Just (interestingArg v)
    doFrame _          = Nothing
    
    doEnd (Return {})  = getContext csc
    doEnd (Case {})    = CaseCtxt
    
    (_, csc, _) = openScopedEnd end

tryUnfolding :: DynFlags -> Id -> Bool -> [ArgSummary] -> CallCtxt
             -> a -> Bool -> Bool -> Bool -> Arity -> UnfoldingGuidance
             -> Maybe a
tryUnfolding dflags id lone_variable 
             arg_infos cont_info unf_template is_top 
             is_wf is_exp uf_arity guidance
                        -- uf_arity will typically be equal to (idArity id), 
                        -- but may be less for InlineRules
 | tracing || dopt Opt_D_dump_inlinings dflags && dopt Opt_D_verbose_core2core dflags
 = pprTrace ("Considering inlining: " ++ showSDocDump dflags (ppr id))
                 (vcat [text "arg infos" <+> ppr arg_infos,
                        text "uf arity" <+> ppr uf_arity,
                        text "interesting continuation" <+> ppr cont_info,
                        text "some_benefit" <+> ppr some_benefit,
                        text "is exp:" <+> ppr is_exp,
                        text "is work-free:" <+> ppr is_wf,
                        text "guidance" <+> ppr guidance,
                        extra_doc,
                        text "ANSWER =" <+> if yes_or_no then text "YES" else text "NO"])
                 result
  | otherwise  = result

  where
    n_val_args = length arg_infos
    saturated  = n_val_args >= uf_arity
    cont_info' | n_val_args > uf_arity = ValAppCtxt
               | otherwise             = cont_info

    result | yes_or_no = Just unf_template
           | otherwise = Nothing

    interesting_args = any nonTriv arg_infos 
            -- NB: (any nonTriv arg_infos) looks at the
            -- over-saturated args too which is "wrong"; 
            -- but if over-saturated we inline anyway.

           -- some_benefit is used when the RHS is small enough
           -- and the call has enough (or too many) value
           -- arguments (ie n_val_args >= arity). But there must
           -- be *something* interesting about some argument, or the
           -- result context, to make it worth inlining
    some_benefit 
       | not saturated = interesting_args        -- Under-saturated
                                                 -- Note [Unsaturated applications]
       | otherwise = interesting_args            -- Saturated or over-saturated
                  || interesting_call

    interesting_call 
      = case cont_info' of
          CaseCtxt   -> not (lone_variable && is_wf)  -- Note [Lone variables]
          ValAppCtxt -> True                          -- Note [Cast then apply]
          RuleArgCtxt -> is_function  -- See Note [Unfold info lazy contexts]
          DiscArgCtxt -> is_function  --
          RhsCtxt     -> is_function  --
          _           -> not is_top && is_function    -- Note [Nested functions]
                                                      -- Note [Inlining in ArgCtxt]

    is_function | isJoinId id = True -- Join points are always functions
                | otherwise = uf_arity > 0

    (yes_or_no, extra_doc)
      = case guidance of
          UnfNever -> (False, empty)

          UnfWhen { ug_unsat_ok = unsat_ok, ug_boring_ok = boring_ok }
             -> (enough_args && (boring_ok || some_benefit), empty )
             where      -- See Note [INLINE for small functions (3)]
               enough_args = saturated || (unsat_ok && n_val_args > 0)

          UnfIfGoodArgs { ug_args = arg_discounts, ug_res = res_discount,
                          ug_size = size }
             -> ( is_wf && some_benefit && small_enough
                , (text "discounted size =" <+> int discounted_size) )
                 where
                   discounted_size = size - discount
                   small_enough = discounted_size <= ufUseThreshold dflags
                   discount = computeDiscount dflags uf_arity arg_discounts 
                                              res_discount arg_infos cont_info'

-------------------------------
-- Continuations and sharing --
-------------------------------

ensureDupableKont :: SimplEnv -> DataScope -> ControlScope
                  -> SimplM (Floats, ControlScope)
ensureDupableKont env dsc csc
  | let mk = retKont csc
  , not (canDupMetaKont mk)
  = do
    (flts, mk') <- mkDupableKont env dsc csc (retType csc) mk
    return (flts, csc `setRetKont` mk')
  | otherwise
  = return (emptyFloats, csc)

-- | Make a continuation into something we're okay with duplicating into each
-- branch of a case (and each branch of those branches, ...). This may generate
-- a number of bound terms and join points.
--
-- The rules:
--   1. Duplicate returns.
--   2. Duplicate casts.
--   3. Don't duplicate ticks (because GHC doesn't).
--   4. Duplicate applications, but let-bind them first to share the arguments.
--   5. Don't duplicate single-branch cases.
--   6. Duplicate cases, but "let-bind" in a dual sense by creating a join point
--        for each branch.

mkDupableKont :: SimplEnv -> DataScope -> ControlScope
              -> Type -> MetaKont
              -> SimplM (Floats, MetaKont)
mkDupableKont _env _dsc _csc _ty kont
  | canDupMetaKont kont
  = return (emptyFloats, kont)
mkDupableKont env dsc csc ty kont
  = do
    when tracing $ liftCoreM $ putMsg $
      hang (text "mkDupableKont") 4 (ppr env $$ ppr ty $$ ppr kont)
    (flts, ans) <- case kont of
      SynKont { mk_frames = fs, mk_end = end }
        -> do
           (flts, fs', end') <- go env [] [] ty fs end
           return (flts, SynKont { mk_dup = OkToDup
                                 , mk_frames = map (Simplified OkToDup ()) fs'
                                 , mk_end = end' })
      StrictArg { mk_argInfo = ai
                , mk_frames  = fs
                , mk_end     = end }
        -> do
           (flts, fs', end') <- go env [] [] ty fs end
           let env' = env `augmentFromFloats` flts
           (flts', ai') <- case ai_dup ai of
             NoDup -> do 
                      (flts', outFrames) <- makeTrivialFrames NotTopLevel env' (ai_frames ai)
                      return (flts', ai { ai_frames = outFrames, ai_dup = OkToDup })
             OkToDup -> return (emptyFloats, ai)
           return (flts `addFloats` flts', kont { mk_dup     = OkToDup
                                                , mk_argInfo = ai'
                                                , mk_frames  = map (Simplified OkToDup ()) fs'
                                                , mk_end     = end' })
      
      StrictLet { mk_scope = (dsc', csc'), mk_binder = bndr, mk_command = comm }
        -> do
           let kontTy = mkKontTy (mkTupleTy UnboxedTuple [ty])
           (env', j) <- mkFreshVar env (fsLit "*letj") kontTy
           -- The binder will always end up being bound
           -- to the case binder below, so the inline
           -- pragma makes more sense there.
           let bndr' = bndr `setInlinePragma` defaultInlinePragma
               (env_rhs, dsc_rhs, join_bndr) = enterTermScope env' dsc' bndr'
               csc_rhs = csc'
               join_rhs = Join [join_bndr] comm
           (flts, env_kont, csc_kont) <- simplJoinBind env_rhs dsc csc j dsc_rhs csc_rhs j join_rhs NonRecursive
           let (env_jump, dsc_jump, case_bndr)
                 = enterTermScope env_kont dsc_rhs bndr
           jump_comm <- simplCommandNoFloats env_jump dsc_jump csc_kont $
                          Jump [Var case_bndr] j
           let mk' = Stop { mk_context = getContext csc' }
               join_end = Simplified OkToDup (retType csc_kont, mk') $
                            Case case_bndr [Alt DEFAULT [] jump_comm]
           return (flts, SynKont { mk_dup = OkToDup
                                 , mk_frames = []
                                 , mk_end = join_end })
      _ -> do
           (flts, joinKont) <- mkJoinPoint env dsc csc ty (fsLit "*mkj") kont
           let mk' = Stop { mk_context = getContext csc }
           return (flts, SynKont { mk_dup = OkToDup
                                 , mk_frames = []
                                 , mk_end = Simplified OkToDup (retType csc, mk') joinKont })
           
    when tracing $ liftCoreM $ putMsg $ hang (text "mkDupableKont DONE") 4 $
      ppr kont $$ darrow $$
      ppr ans $$ vcat (map ppr (getFloatBinds flts))
    return (flts, ans)
  where
    go :: SimplEnv -> RevList Floats -> RevList OutFrame -> OutType
       -> [ScopedFrame] -> ScopedEnd
       -> SimplM (Floats, [OutFrame], ScopedEnd)
    go env fltss fs' ty (f : fs) end
      | Simplified OkToDup _ f' <- f
      = go env fltss (f' : fs') (frameType ty f') fs end
      | otherwise
      = case openScopedFrame f of
          (dsc', f') -> doFrame env dsc' fltss fs' ty f' f fs end
    go env fltss fs' ty [] end
      = case openScopedEnd end of
          (dsc', csc', end') -> doEnd env dsc' csc' fltss fs' ty end' end
    
    doFrame :: SimplEnv -> DataScope -> RevList Floats -> RevList OutFrame -> OutType
            -> InFrame -> ScopedFrame -> [ScopedFrame] -> ScopedEnd
            -> SimplM (Floats, [OutFrame], ScopedEnd)
    doFrame env dsc fltss fs' _ty (Cast co) _ fs end
      = let co' = simplCoercion env dsc co
        in go env fltss (Cast co' : fs') (pSnd (coercionKind co')) fs end
    
    doFrame env dsc fltss fs' ty (Tick {}) f_orig fs end
      = split env dsc csc fltss fs' ty (f_orig : fs) end (fsLit "*tickj")
    
    doFrame env dsc fltss fs' ty (App (Type tyArg)) _ fs end
      = let tyArg' = substTy env dsc tyArg
            ty'    = applyTy ty tyArg'
        in go env fltss (App (Type tyArg') : fs') ty' fs end
    
    doFrame env dsc fltss fs' ty (App arg) _ fs end
      = do
        (flts, arg') <- mkDupableTerm env dsc arg
        go (env `augmentFromFloats` flts) (flts:fltss) (App arg' : fs') (funResultTy ty) fs end

    doEnd :: SimplEnv -> DataScope -> ControlScope
          -> RevList Floats -> RevList OutFrame -> OutType
          -> InEnd -> ScopedEnd
          -> SimplM (Floats, [OutFrame], ScopedEnd)
    doEnd env dsc csc fltss fs' ty Return _
      | let mk = retKont csc
      = case mk of
          _                       | canDupMetaKont mk
                                 -> done fltss fs' (Simplified OkToDup (retType csc, mk) Return)
          SynKont { mk_frames = fs, mk_end = end }
                                 -> go env fltss fs' ty fs end
          StrictArg { mk_argInfo = ai }
                                  | argInfoHasTerm ai
                                 -> do
                                    let ty'  = funResultTy (termType (argInfoToTerm ai))
                                    (flts, mk') <- mkDupableKont env dsc csc ty' mk
                                    done (flts:fltss) fs' (Simplified OkToDup (retType csc, mk') Return)
          StrictLet { mk_binder = bndr }
                                 -> do
                                    let ty' = idType bndr
                                    (flts, mk') <- mkDupableKont env dsc csc ty' mk
                                    done (flts:fltss) fs' (Simplified OkToDup (ty', mk') Return)
          _                      -> split env dsc csc fltss fs' ty [] (Simplified OkToDup (retType csc, mk) Return)
                                                                      (fsLit "*imkj")
    
    -- Don't duplicate seq (see Note [Single-alternative cases] in GHC Simplify.lhs)
    doEnd env dsc csc fltss fs' ty (Case caseBndr [Alt _altCon bndrs _rhs]) end_orig
      | all isDeadBinder bndrs
      , not (isUnLiftedType (idType caseBndr))
      = split env dsc csc fltss fs' ty [] end_orig (fsLit "*seqj")

    doEnd env dsc csc fltss fs' _ty (Case caseBndr alts) _
      -- This is dual to the App case: We have several branches and we want to
      -- bind each to a join point.
      = do
        -- NOTE: At this point, mkDupableCont in GHC Simplify.lhs calls
        -- prepareCaseCont (ultimately a recursive call) on the outer
        -- continuation. We have no outer continuation for a case; in the
        -- equivalent situation, we would have already dealt with the outer
        -- case. May be worth checking that we get the same result.
        
        let (altEnv, altDsc, caseBndr') = enterTermScope env dsc caseBndr
        alts' <- mapM (simplAlt altEnv altDsc csc Nothing [] caseBndr') alts
        (flts, alts'') <- mkDupableAlts env caseBndr' alts'
        
        done (flts:fltss) fs' (Simplified OkToDup (retType csc, Stop { mk_context = getContext csc })
                                                  (Case caseBndr' alts''))

    split :: SimplEnv -> DataScope -> ControlScope
          -> RevList Floats -> RevList OutFrame
          -> Type -> [ScopedFrame] -> ScopedEnd
          -> FastString
          -> SimplM (Floats, [OutFrame], ScopedEnd)
    split env dsc csc fltss fs' ty fs end name
        -- XXX This is a bit ugly, but it is currently the only way to split a
        -- non-parameterized continuation in two:
        --   Edup[Knodup] ==> let cont j x = < x | Knodup >
        --                    in Edup[case of x -> < jump x | j >]
        -- Notice that it's only okay to put the case there because Knodup is a
        -- strict context, which is only necessarily true because all
        -- continuations are strict contexts. If that changes, we'll need to
        -- revisit this.
      = do
        (flts, join_kont)
          <- mkJoinPoint env dsc csc ty name (SynKont { mk_frames = fs
                                                      , mk_end    = end
                                                      , mk_dup    = NoDup })
        done (flts:fltss) fs' (Simplified OkToDup (retType csc, retKont csc) join_kont)
    
    done :: RevList Floats -> RevList OutFrame -> ScopedEnd
         -> SimplM (Floats, [OutFrame], ScopedEnd)
    done fltss fs end = return (catFloats (reverse fltss), reverse fs, end)
    
    mkJoinPoint :: SimplEnv -> DataScope -> ControlScope -> OutType -> FastString
                -> MetaKont
                -> SimplM (Floats, OutEnd)
    mkJoinPoint env dsc csc ty name mk
      = do
        let kontTy = mkKontTy (mkTupleTy UnboxedTuple [ty])
        (env', j) <- mkFreshVar env name kontTy
        let (env_rhs, dsc_rhs, x) = enterTermScope env' dsc (mkKontArgId ty)
            csc_rhs   = csc `setRetKont` mk
            join_rhs  = Join [x] (Eval (Var x) [] Return)
        (flts, env_kont, csc_kont) <- simplJoinBind env_rhs dsc csc j dsc_rhs csc_rhs j join_rhs NonRecursive
        (flts', jump_comm) <- simplJump env_kont dsc_rhs csc_kont [Var x] j
        let join_kont = Case x [Alt DEFAULT [] jump_comm]
        return (flts `addFloats` flts', join_kont)
    
mkDupableTerm :: SimplEnv -> DataScope -> InTerm
                          -> SimplM (Floats, OutTerm)
mkDupableTerm env dsc term
  = do
    (env', bndr) <- mkFreshVar env (fsLit "triv") (substTy env dsc (termType term))
    (flts, env'', dsc') <- simplLazyBind env' dsc bndr dsc bndr term NotTopLevel NonRecursive
    term_final <- simplVar env'' dsc' bndr
    return (flts, term_final)

mkDupableAlts :: SimplEnv -> OutId -> [OutAlt] -> SimplM (Floats, [OutAlt])
mkDupableAlts env caseBndr = go env [] []
  where
    go _   fltss alts' []           = return (catFloats (reverse fltss), reverse alts')
    go env fltss alts' (alt : alts) = do (flts, alt') <- mkDupableAlt env caseBndr alt
                                         go (env `augmentFromFloats` flts) (flts:fltss) (alt':alts') alts

mkDupableAlt :: SimplEnv -> OutId -> OutAlt -> SimplM (Floats, OutAlt)
mkDupableAlt env caseBndr alt@(Alt altCon bndrs rhs)
  = do
    dflags <- getDynFlags
    if commandIsDupable dflags rhs
      then return (emptyFloats, alt)
      else do
        let scrut_ty = idType caseBndr
        
            case_bndr_w_unf
              = case altCon of
                    DEFAULT    -> caseBndr
                    DataAlt dc -> snd (setDef env caseBndr unf)
                        where
                               -- See Note [Case binders and join points]
                           unf = mkInlineTermDef Nothing rhs
                           rhs = mkAppTerm (Var (dataConWorkId dc)) $
                                   (map Type (tyConAppArgs scrut_ty) ++
                                    map mkVarArg bndrs)

                    LitAlt {} -> warnPprTrace True __FILE__ __LINE__ (
                                   ptext (sLit "mkDupableAlt")
                                              <+> ppr caseBndr <+> ppr altCon ) $
                                 caseBndr
                         -- The case binder is alive but trivial, so why has
                         -- it not been substituted away?
        
        let used_bndrs | isDeadBinder case_bndr_w_unf = filter abstract_over bndrs
                       | otherwise = bndrs ++ [case_bndr_w_unf]
                  
            abstract_over bndr
                | isTyVar bndr = True -- Abstract over all type variables just in case
                | otherwise    = not (isDeadBinder bndr)
                -- The deadness info on the new Ids is preserved by simplBinders_
        
        let (tyBndrs, valBndrs) = span isTyVar used_bndrs
            bndrTys = map idType valBndrs
            argTy   = foldr mkUbxExistsTy (mkTupleTy UnboxedTuple bndrTys) tyBndrs
        
        (_, join_bndr) <- mkFreshVar env (fsLit "*j") (mkKontTy argTy)
        
        let join_rhs  = Join used_bndrs rhs
            join_args = map (Type . mkTyVarTy) tyBndrs ++ map Var valBndrs
            join_comm = Jump join_args join_bndr
        
        when tracing $ liftCoreM $
          putMsg (text "created join point" <+> pprBndr LetBind join_bndr $$
                  ppr join_rhs $$
                  ppr (Alt altCon bndrs join_comm))
        
        flts <- addPolyBind env emptyDataScope nullControlScope
                            NotTopLevel (NonRec (BindJoin join_bndr join_rhs))
          -- addPolyBind only uses the scopes by passing them to simplDef, which
          -- only uses them to re-simplify a stable unfolding. Since join_bndr is
          -- fresh, then, the scopes don't matter.
        return (flts, Alt altCon bndrs join_comm)
            
commandIsDupable :: DynFlags -> SeqCoreCommand -> Bool
commandIsDupable dflags c
  = isJust (goC dupAppSize c)
  where
    goC n (Eval v fs Return)
                        = goT n  v >>= \n' ->
                          goF n' fs
    goC _ _             = Nothing
    
    goT n (Type {})     = Just n
    goT n (Coercion {}) = Just n
    goT n (Var {})      = decrement n
    goT n (Lit lit)     | litIsDupable dflags lit = decrement n
    goT _ _             = Nothing
    
    goF n (Tick _ : fs) = goF n fs
    goF n (Cast _ : fs) = goF n fs
    goF n (App  v : fs) = goT n v >>= \n' ->
                          goF n' fs
    goF n []            = Just n
    
    decrement :: Int -> Maybe Int
    decrement 0 = Nothing
    decrement n = Just (n-1)

-- see GHC CoreUtils.lhs
dupAppSize :: Int
dupAppSize = 8

makeTrivial :: TopLevelFlag -> SimplEnv -> OutTerm -> SimplM (Floats, OutTerm)
-- Binds the expression to a variable, if it's not trivial, returning the variable
makeTrivial top_lvl env term = makeTrivialWithInfo top_lvl env vanillaIdInfo term

makeTrivialFrame :: TopLevelFlag -> SimplEnv -> OutFrame -> SimplM (Floats, OutFrame)
makeTrivialFrame top_lvl env frame
  = case frame of App arg -> second App <$> makeTrivial top_lvl env arg
                  other   -> return (emptyFloats, other)

makeTrivialFrames :: TopLevelFlag -> SimplEnv -> [OutFrame] -> SimplM (Floats, [OutFrame])
makeTrivialFrames top_level env frames
  = do
    (_, unzip -> (fltss, frames')) <- mapAccumLM mkFrame env frames
    return (catFloats fltss, frames')
  where
    mkFrame env frame = do (flts, frame') <- makeTrivialFrame top_level env frame
                           return (env `augmentFromFloats` flts, (flts, frame'))

makeTrivialWithInfo :: TopLevelFlag -> SimplEnv -> IdInfo
                    -> OutTerm -> SimplM (Floats, OutTerm)
-- Propagate strictness and demand info to the new binder
-- Note [Preserve strictness when floating coercions]
-- Returned SimplEnv has same substitution as incoming one
makeTrivialWithInfo top_lvl env info term
  | isTrivialTerm term                          -- Already trivial
  || not (bindingOk top_lvl term term_ty)       -- Cannot trivialise
                                                --   See Note [Cannot trivialise]
  = return (emptyFloats, term)
  | otherwise           -- See Note [Take care] below
  = do  { uniq <- getUniqueM
        ; let name = mkSystemVarName uniq (fsLit "a")
              var = mkLocalIdWithInfo name term_ty info
        ; (flts, env', dsc)  <- completeNonRecOut env emptyDataScope top_lvl False var var term
        ; expr'              <- simplVar env' dsc var
        ; return (flts, expr') }
        -- The simplVar is needed becase we're constructing a new binding
        --     a = rhs
        -- And if rhs is of form (rhs1 |> co), then we might get
        --     a1 = rhs1
        --     a = a1 |> co
        -- and now a's RHS is trivial and can be substituted out, and that
        -- is what completeNonRecX will do
        -- To put it another way, it's as if we'd simplified
        --    let var = e in var
  where
    term_ty = termType term

bindingOk :: TopLevelFlag -> SeqCoreTerm -> Type -> Bool
-- True iff we can have a binding of this expression at this level
-- Precondition: the type is the type of the expression
bindingOk top_lvl _ term_ty
  | isTopLevel top_lvl = not (isUnLiftedType term_ty)
  | otherwise          = True


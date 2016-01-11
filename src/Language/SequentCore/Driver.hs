module Language.SequentCore.Driver ( installSequentCorePasses ) where

import Language.SequentCore.Driver.Flags as SeqFlags
import Language.SequentCore.FloatOut   ( runFloatOut )
import Language.SequentCore.Lint
import Language.SequentCore.Pretty
import Language.SequentCore.Simpl      ( runSimplifier )
import Language.SequentCore.SpecConstr ( runSpecConstr )
import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import BasicTypes ( CompilerPhase(..) )
import CoreMonad  ( CoreM, CoreToDo(..), SimplifierMode(..) )
import qualified CoreMonad as Core
import CoreSyn    ( CoreRule )
import DynFlags
import qualified ErrUtils as Err
import HscTypes   ( ModGuts(..) )
import Maybes     ( whenIsJust )
import MonadUtils
import Outputable
import qualified PprCore as Core

import Control.Monad ( foldM, when )
import Data.List

installSequentCorePasses :: SeqFlags -> [CoreToDo] -> CoreM [CoreToDo]
installSequentCorePasses sflags corePasses
  = do
    dflags <- getDynFlags
    dump dflags "Initial Core pipeline" $ pprCoreToDoTree corePasses
    let seqPasses = mkSeqCorePipeline dflags sflags corePasses
    dump dflags "Sequent Core pipeline" $ pprSeqCoreToDoTree seqPasses
    let corePasses' = toCorePipeline sflags seqPasses
    dump dflags "Modified Core pipeline" $ pprCoreToDoTree corePasses'
    return corePasses'
  where
    dump dflags hdr doc
      = when (sdopt Opt_D_dump_seq_pipeline sflags) $ liftIO $
          Err.debugTraceMsg dflags 2 $ vcat [ blankLine, text hdr, dashes, doc ]
      where
        dashes = text $ replicate (length hdr) '-'
    
data SeqCoreToDo
  = SeqCoreDoSimplify
      Int -- Max iterations 
      SimplifierMode
  | SeqCoreDoSpecConstr
  | SeqCoreDoFloatOutwards FloatOutSwitches
  | SeqCoreDoPasses [SeqCoreToDo]
  | SeqCoreDoNothing
  | SeqCoreDoCore CoreToDo

dumpFlag :: SeqCoreToDo -> Maybe DumpFlag
dumpFlag (SeqCoreDoSimplify {})      = Just Opt_D_dump_simpl_phases
dumpFlag (SeqCoreDoFloatOutwards {}) = Just Opt_D_verbose_core2core
dumpFlag SeqCoreDoSpecConstr         = Just Opt_D_dump_spec

dumpFlag SeqCoreDoNothing            = Nothing
dumpFlag (SeqCoreDoPasses {})        = Nothing
dumpFlag (SeqCoreDoCore {})          = Nothing

mkSeqCorePipeline :: DynFlags -> SeqFlags -> [CoreToDo] -> [SeqCoreToDo]
mkSeqCorePipeline dflags sflags
  = installLateLambdaLift dflags sflags . map xlate
  where
    xlate CoreDoNothing                = SeqCoreDoNothing
    xlate (CoreDoPasses inner)         = SeqCoreDoPasses (map xlate inner)
    xlate (CoreDoSimplify iters mode)  | sgopt Opt_EnableSeqSimpl sflags
                                       = SeqCoreDoSimplify iters mode
    xlate CoreDoSpecConstr             | sgopt Opt_EnableSeqSpecConstr sflags
                                       = SeqCoreDoSpecConstr
    xlate (CoreDoFloatOutwards fs)     | sgopt Opt_EnableSeqFloatOut sflags
                                       = SeqCoreDoFloatOutwards (xlateFloatOutSwitches fs)
    xlate other                        = SeqCoreDoCore other

xlateFloatOutSwitches :: Core.FloatOutSwitches -> FloatOutSwitches
xlateFloatOutSwitches fos
  = FloatOutSwitches {
      floatOutLambdas             = Core.floatOutLambdas             fos,
      floatOutConstants           = Core.floatOutConstants           fos,
      floatOutPartialApplications = Core.floatOutPartialApplications fos,
      finalPass_                  = Nothing
    }

installLateLambdaLift :: DynFlags -> SeqFlags -> [SeqCoreToDo] -> [SeqCoreToDo]
installLateLambdaLift dflags sflags todos
  = todos ++ [runWhen (sgopt SeqFlags.Opt_LLF sflags) lateLambdaLift]
      -- qualify Opt_LLF for compatibility with GHC llf branch
  where
    lateLambdaLift
      = SeqCoreDoPasses [
          SeqCoreDoFloatOutwards switchesForFinal,
          simplAfterLateLambdaLift
        ]

    simplAfterLateLambdaLift
      = runWhen (sgopt SeqFlags.Opt_LLF_Simpl sflags) $
          simpl_phase 0 ["post-late-lam-lift"] max_iter
    
    switchesForFinal = FloatOutSwitches
      { floatOutLambdas             = SeqFlags.lateFloatNonRecLam sflags
      , floatOutConstants           = False
      , floatOutPartialApplications = False
      , finalPass_                  = Just finalPassSwitches
      }

    finalPassSwitches = FinalPassSwitches
      { fps_trace          = sdopt SeqFlags.Opt_D_dump_llf       sflags
      , fps_stabilizeFirst = sgopt SeqFlags.Opt_LLF_Stabilize    sflags
      , fps_rec            = SeqFlags.lateFloatRecLam            sflags
      , fps_absUnsatVar    = sgopt SeqFlags.Opt_LLF_AbsUnsat     sflags
      , fps_absSatVar      = sgopt SeqFlags.Opt_LLF_AbsSat       sflags
      , fps_absOversatVar  = sgopt SeqFlags.Opt_LLF_AbsOversat   sflags
      , fps_createPAPs     = sgopt SeqFlags.Opt_LLF_CreatePAPs   sflags
      , fps_ifInClo        = SeqFlags.lateFloatIfInClo           sflags
      , fps_cloGrowth      = SeqFlags.lateFloatCloGrowth         sflags
      , fps_cloGrowthInLam = SeqFlags.lateFloatCloGrowthInLam    sflags
      , fps_strictness     = sgopt SeqFlags.Opt_LLF_UseStr       sflags
      , fps_oneShot        = sgopt SeqFlags.Opt_LLF_OneShot      sflags
      }
    
    -- Sadly, here we must C&P a bunch of code from CoreMonad so we can say to
    -- simplify gently after LLL
    max_iter      = maxSimplIterations dflags
    rule_check    = ruleCheck          dflags

    rules_on      = gopt Opt_EnableRewriteRules           dflags
    eta_expand_on = gopt Opt_DoLambdaEtaExpansion         dflags

    maybe_rule_check phase = runMaybe rule_check $ \str -> SeqCoreDoCore (CoreDoRuleCheck phase str)

    maybe_strictness_before phase
      = runWhen (phase `elem` strictnessBefore dflags) (SeqCoreDoCore CoreDoStrictness)

    base_mode = SimplMode { sm_phase      = panic "base_mode"
                          , sm_names      = []
                          , sm_rules      = rules_on
                          , sm_eta_expand = eta_expand_on
                          , sm_inline     = True
                          , sm_case_case  = True }

    simpl_phase phase names iter
      = SeqCoreDoPasses
      $   [ maybe_strictness_before phase
          , mkSimplifyPass iter
                (base_mode { sm_phase = Phase phase
                           , sm_names = names })

          , maybe_rule_check (Phase phase) ]

          -- Vectorisation can introduce a fair few common sub expressions involving
          --  DPH primitives. For example, see the Reverse test from dph-examples.
          --  We need to eliminate these common sub expressions before their definitions
          --  are inlined in phase 2. The CSE introduces lots of  v1 = v2 bindings,
          --  so we also run simpl_gently to inline them.
      ++  (if gopt Opt_Vectorise dflags && phase == 3
            then [SeqCoreDoCore CoreCSE, simpl_gently]
            else [])

        -- initial simplify: mk specialiser happy: minimum effort please
    simpl_gently = mkSimplifyPass max_iter
                       (base_mode { sm_phase = InitialPhase
                                  , sm_names = ["Gentle"]
                                  , sm_rules = rules_on   -- Note [RULEs enabled in SimplGently]
                                  , sm_inline = False
                                  , sm_case_case = False })
                          -- Don't do case-of-case transformations.
                          -- This makes full laziness work better
    
    mkSimplifyPass iters mode
      | sgopt Opt_EnableSeqSimpl sflags = SeqCoreDoSimplify iters mode
      | otherwise                       = SeqCoreDoCore (CoreDoSimplify iters mode)                        
    
    runWhen cond todo | cond      = todo
                      | otherwise = SeqCoreDoNothing
    
    runMaybe (Just x) f = f x
    runMaybe Nothing  _ = SeqCoreDoNothing
  
-- Flattens the pipeline as a side effect, but this is unlikely to matter much.
toCorePipeline :: SeqFlags -> [SeqCoreToDo] -> [CoreToDo]
toCorePipeline sflags seqPipeline = go [] seqPipeline []
  where
    go :: [SeqCoreToDo]   -- Previous Sequent Core passes, in reverse
                          --   (invariant: not SeqCoreDoCore, SeqCoreDoPasses,
                          --      or SeqCoreDoNothing)
       -> [SeqCoreToDo]   -- Passes to process
       -> [[SeqCoreToDo]] -- Remaining batches of passes (pushed when
                          --   recursing into SeqCoreDoPasses)
       -> [CoreToDo]
    -- Note that arguments appear in pipeline order
    go seqPasses (todo : todos) rest
      = case todo of
          SeqCoreDoCore corePass -> wrapSeqPasses (reverse seqPasses) ++
                                      corePass : go [] todos rest
          SeqCoreDoPasses inner  -> go seqPasses inner (todos : rest)
          SeqCoreDoNothing       -> go seqPasses todos rest
          other                  -> go (other : seqPasses) todos rest
    
    go seqPasses [] (todos : rest)
      = go seqPasses todos rest
    
    go seqPasses [] []
      = wrapSeqPasses (reverse seqPasses)
    
    wrapSeqPasses [] = []
    wrapSeqPasses todos
      | sgopt Opt_CombineSeqPasses sflags
      = [ CoreDoPluginPass (name todos) (runSeqCorePasses sflags todos) ]
      | otherwise
      = [ CoreDoPluginPass (name [pass]) (runSeqCorePasses sflags [pass])
        | pass <- todos ]
      where
        name todos = "Sequent Core: " ++ intercalate " | " (map desc todos)
        
        desc (SeqCoreDoSimplify _ m)             = "Simplifier \"" ++ head (sm_names m) ++
                                                   "\" (" ++ showPhase (sm_phase m) ++ ")"
        desc SeqCoreDoSpecConstr                 = "SpecConstr"
        desc (SeqCoreDoFloatOutwards fos)          
          = case finalPass_ fos of Nothing      -> "Float Out"
                                   Just _       -> "Late Lambda-Lifting"
        desc other                               = pprPanic "toCorePipeline" (ppr other)
        
        showPhase InitialPhase = "InitialPhase"
        showPhase (Phase n)    = show n

runSeqCorePasses :: SeqFlags -> [SeqCoreToDo] -- Invariant: not SeqCoreDoCore
                 -> ModGuts -> CoreM ModGuts
runSeqCorePasses sflags todos guts
  = do
    dflags <- getDynFlags
    let binds = fromCoreModule (mg_binds guts)
    liftIO $
      Err.dumpIfSet dflags (dumping dflags) "Translated Sequent Core" $
        pprTopLevelBinds binds
    (guts', binds') <- doPasses (guts, binds) todos
    return $ guts' { mg_binds = bindsToCore binds' }
  where
    doPasses = foldM doPass 
    
    doPass (guts, binds) pass
      = do
        dflags <- getDynFlags
        liftIO $ showPass dflags pass
        (guts', binds') <- case pass of
          SeqCoreDoSimplify iters mode  -> runSimplifier iters mode guts binds
          SeqCoreDoFloatOutwards fs     -> bindsOnly $ runFloatOut fs sflags binds
          SeqCoreDoSpecConstr           -> bindsOnly $ runSpecConstr binds
          SeqCoreDoPasses inner         -> doPasses (guts, binds) inner
          SeqCoreDoNothing              -> return (guts, binds)
          SeqCoreDoCore _               -> pprPanic "runSeqCorePasses" (ppr pass)
        liftIO $ endPass dflags pass binds' (mg_rules guts')
        return (guts', binds')
      where
        bindsOnly m = m >>= \binds' -> return (guts, binds')
    
    dumping dflags = sdopt Opt_D_dump_seq_xlate sflags ||
                     dopt Opt_D_verbose_core2core dflags

showPass :: DynFlags -> SeqCoreToDo -> IO ()
showPass dflags pass = Err.showPass dflags ("(Sequent Core) " ++ showPpr dflags pass)

endPass :: DynFlags -> SeqCoreToDo -> SeqCoreProgram -> [CoreRule] -> IO ()
endPass dflags pass binds rules
  = do { dumpPassResult dflags mb_flag (ppr pass) (pprPassDetails pass) binds rules
       ; lintPassResult dflags pass binds }      
  where
    mb_flag = case dumpFlag pass of
                Just flag | dopt flag dflags                    -> Just flag
                          | dopt Opt_D_verbose_core2core dflags -> Just flag
                _ -> Nothing

dumpPassResult :: DynFlags 
               -> Maybe DumpFlag		-- Just df => show details in a file whose
	       	  			--            name is specified by df
               -> SDoc 			-- Header
               -> SDoc 			-- Extra info to appear after header
               -> SeqCoreProgram -> [CoreRule] 
               -> IO ()
dumpPassResult dflags mb_flag hdr extra_info binds rules
  | Just flag <- mb_flag
  = Err.dumpSDoc dflags flag (showSDoc dflags hdr) dump_doc

  | otherwise
  = return () -- TODO Report result size

  where
    dump_doc  = vcat [ nest 2 extra_info
		                 , blankLine
                     , pprTopLevelBinds binds 
                     , ppUnless (null rules) pp_rules ]
    pp_rules = vcat [ blankLine
                    , text "------ Local rules for imported ids --------"
                    , Core.pprRules rules ]

lintPassResult :: DynFlags -> SeqCoreToDo -> SeqCoreProgram -> IO ()
lintPassResult dflags pass binds
  | not (gopt Opt_DoCoreLinting dflags)
  = return ()
  | otherwise
  = do { let errs = lintCoreBindings binds
       ; Err.showPass dflags ("Sequent Core Linted result of " ++ showPpr dflags pass)
       ; whenIsJust errs $ \err ->
           pprPgmError "Sequent Core Lint error"
               (withPprStyle defaultUserStyle $ err
                                             $$ pprTopLevelBinds binds) }

pprCoreToDoTree :: [CoreToDo] -> SDoc
pprCoreToDoTree = vcat . map pprPass
  where
    pprPass pass = hang bullet 2 $ pprCoreToDo pass
      where
        bullet = case pass of CoreDoNothing -> empty
                              _             -> char '*'

pprCoreToDo :: CoreToDo -> SDoc
pprCoreToDo (CoreDoPasses inner) = pprCoreToDoTree inner
pprCoreToDo CoreDoNothing        = text "(skip)"
pprCoreToDo (CoreDoSimplify _ m) = text "Simplifier:" <+>
                                   doubleQuotes (text (head (sm_names m))) <+>
                                   parens (ppr (sm_phase m))
pprCoreToDo pass                 = ppr pass

pprSeqCoreToDoTree :: [SeqCoreToDo] -> SDoc
pprSeqCoreToDoTree = vcat . map pprPass
  where
    pprPass pass = hang bullet 2 $ pprSeqCoreToDo pass
      where
        bullet = case pass of SeqCoreDoNothing -> empty
                              _                -> char '*'

pprSeqCoreToDo :: SeqCoreToDo -> SDoc
pprSeqCoreToDo (SeqCoreDoPasses inner) = pprSeqCoreToDoTree inner
pprSeqCoreToDo SeqCoreDoNothing        = text "(skip)"
pprSeqCoreToDo (SeqCoreDoSimplify _ m) = text "Simplifier:" <+>
                                         doubleQuotes (text (head (sm_names m))) <+>
                                         parens (ppr (sm_phase m))
pprSeqCoreToDo (SeqCoreDoFloatOutwards f)
                                       = text "Float out" <> parens (ppr f)
pprSeqCoreToDo SeqCoreDoSpecConstr     = text "SpecConstr"
pprSeqCoreToDo (SeqCoreDoCore pass)    = text "Core:" <+> pprCoreToDo pass

instance Outputable SeqCoreToDo where
  ppr = pprSeqCoreToDo

pprPassDetails :: SeqCoreToDo -> SDoc
pprPassDetails (SeqCoreDoSimplify iters mode) = vcat [ text "Max iterations =" <+> int iters 
                                                     , ppr mode ]
pprPassDetails _ = empty

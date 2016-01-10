module Language.SequentCore.Driver.Flags (
  SeqFlags(..), SeqDumpFlag(..), SeqGeneralFlag(..),
  FloatOutSwitches(..), FinalPassSwitches(..),
  
  sgopt, sgopt_set, sgopt_unset,
  sdopt, sdopt_set, sdopt_unset,
  
  parseSeqFlags
) where

import CmdLineParser
import FastString
import MonadUtils
import Outputable
import Panic
import SrcLoc

import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

parseSeqFlags :: MonadIO m => [String]
              -> m (SeqFlags, [String], [String])
parseSeqFlags args = do
  let ((leftover, errs, warns), sflags)
          = runCmdLine (processArgs seqFlags (map noLoc args))
                       defaultSeqFlags
  unless (null errs) $ liftIO $
      throwGhcExceptionIO $ errorsToGhcException errs

  return (sflags, map unLoc leftover, map unLoc warns)

data SeqDumpFlag
  = Opt_D_dump_llf
  | Opt_D_dump_seq_xlate
  | Opt_D_dump_seq_pipeline
  deriving (Eq, Ord, Enum)

data SeqGeneralFlag
  = Opt_EnableSeqSimpl      -- ^ Use Sequent Core simplifier (Language.SequentCore.Simpl)
  | Opt_EnableSeqFloatOut   -- ^ Use Sequent Core implementation of Float Out (Language.SequentCore.FloatOut)
  | Opt_EnableSeqSpecConstr -- ^ Use Sequent Core implementation of SpecConstr (Language.SequentCore.SpecConstr)
  
  | Opt_CombineSeqPasses    -- ^ Avoid churning between Core and Sequent Core
                            -- TODO Contify more often so that there is nothing to gain by going back and forth
  
  | Opt_ProtectLastValArg
  | Opt_IgnoreRealWorld
  | Opt_FloatNullaryJoins   -- ^ Always allowed to float a nullary join point

  | Opt_LLF                 -- ^ Enable the late lambda lift pass
  | Opt_LLF_AbsUnsat        -- ^ allowed to abstract undersaturated applied let-bound variables?
  | Opt_LLF_AbsSat          -- ^ allowed to abstract      saturated applied let-bound variables?
  | Opt_LLF_AbsOversat      -- ^ allowed to abstract  oversaturated applied let-bound variables?
  | Opt_LLF_CreatePAPs      -- ^ allowed to float function bindings that occur unapplied
  | Opt_LLF_Simpl           -- ^ follow the late lambda lift with a simplification pass?
  | Opt_LLF_Stabilize
  | Opt_LLF_UseStr          -- ^ use strictness in the late lambda float
  | Opt_LLF_OneShot
  deriving (Eq, Ord, Enum)

data SeqFlags = SeqFlags {
  seqDumpFlags            :: IntSet,
  seqGeneralFlags         :: IntSet,
  lateFloatNonRecLam      :: Maybe Int,   -- ^ Limit on # abstracted variables for *late* non-recursive function floating (Nothing => all, Just 0 => none)
  lateFloatRecLam         :: Maybe Int,   -- ^   "    " "     "          "     for *late*     recursive function floating
  lateFloatIfInClo        :: Maybe Int,   -- ^ Limit on # abstracted variables for floating a binding that occurs in a closure
  lateFloatCloGrowth      :: Maybe Int,   -- ^ Limit on # additional free variables for closures in which the function occurs
  lateFloatCloGrowthInLam :: Maybe Int
}

defaultSeqFlags :: SeqFlags
defaultSeqFlags =
  SeqFlags {
    seqDumpFlags            = IntSet.empty,
    seqGeneralFlags         = IntSet.fromList (map fromEnum defaultGeneralFlags),
    lateFloatNonRecLam      = Just 10,
    lateFloatRecLam         = Just 6,
    lateFloatIfInClo        = Nothing,
    lateFloatCloGrowth      = Just 0,
    lateFloatCloGrowthInLam = Just 0
  }

defaultGeneralFlags :: [SeqGeneralFlag]
defaultGeneralFlags = [ Opt_LLF_AbsUnsat, Opt_LLF_UseStr, Opt_LLF_OneShot,
                        Opt_LLF_Simpl, Opt_LLF_Stabilize ]

-- | Test whether a 'SeqGeneralFlag' is set
sgopt :: SeqGeneralFlag -> SeqFlags -> Bool
sgopt f sflags  = fromEnum f `IntSet.member` seqGeneralFlags sflags

-- | Set a 'SeqGeneralFlag'
sgopt_set :: SeqFlags -> SeqGeneralFlag -> SeqFlags
sgopt_set sfs f = sfs{ seqGeneralFlags = IntSet.insert (fromEnum f) (seqGeneralFlags sfs) }

-- | Unset a 'SeqGeneralFlag'
sgopt_unset :: SeqFlags -> SeqGeneralFlag -> SeqFlags
sgopt_unset sfs f = sfs{ seqGeneralFlags = IntSet.delete (fromEnum f) (seqGeneralFlags sfs) }

-- | Test whether a 'SeqDumpFlag' is set
sdopt :: SeqDumpFlag -> SeqFlags -> Bool
sdopt f sflags = fromEnum f `IntSet.member` seqDumpFlags sflags

-- | Set a 'SeqDumpFlag'
sdopt_set :: SeqFlags -> SeqDumpFlag -> SeqFlags
sdopt_set sfs f = sfs{ seqDumpFlags = IntSet.insert (fromEnum f) (seqDumpFlags sfs) }

-- | Unset a 'SeqDumpFlag'
sdopt_unset :: SeqFlags -> SeqDumpFlag -> SeqFlags
sdopt_unset sfs f = sfs{ seqDumpFlags = IntSet.delete (fromEnum f) (seqDumpFlags sfs) }

seqFlags :: [Flag (CmdLineP SeqFlags)]
seqFlags = [
    Flag "ddump-llf"                     (setDumpFlag Opt_D_dump_llf)
  , Flag "ddump-seq-xlate"               (setDumpFlag Opt_D_dump_seq_xlate)
  , Flag "ddump-seq-pipeline"            (setDumpFlag Opt_D_dump_seq_pipeline)
                  
  , Flag "fllf-nonrec-lam-limit"         (intSuffix (\n f -> f{ lateFloatNonRecLam = Just n }))
  , Flag "fllf-nonrec-lam-any"           (noArg       (\f -> f{ lateFloatNonRecLam = Nothing }))
  , Flag "fno-llf-nonrec-lam"            (noArg       (\f -> f{ lateFloatNonRecLam = Just 0 }))
  , Flag "fllf-rec-lam-limit"            (intSuffix (\n f -> f{ lateFloatRecLam = Just n }))
  , Flag "fllf-rec-lam-any"              (noArg       (\f -> f{ lateFloatRecLam = Nothing }))
  , Flag "fno-llf-rec-lam"               (noArg       (\f -> f{ lateFloatRecLam = Just 0 }))
  , Flag "fllf-clo-growth-limit"         (intSuffix (\n f -> f{ lateFloatCloGrowth = Just n }))
  , Flag "fllf-clo-growth-any"           (noArg       (\f -> f{ lateFloatCloGrowth = Nothing }))
  , Flag "fno-llf-clo-growth"            (noArg       (\f -> f{ lateFloatCloGrowth = Just 0 }))
  , Flag "fllf-in-clo-limit"             (intSuffix (\n f -> f{ lateFloatIfInClo = Just n }))
  , Flag "fllf-in-clo-any"               (noArg       (\f -> f{ lateFloatIfInClo = Nothing }))
  , Flag "fno-llf-in-clo"                (noArg       (\f -> f{ lateFloatIfInClo = Just 0 }))
  , Flag "fllf-clo-growth-in-lam-limit"  (intSuffix (\n f -> f{ lateFloatCloGrowthInLam = Just n }))
  , Flag "fllf-clo-growth-in-lam-any"    (noArg       (\f -> f{ lateFloatCloGrowthInLam = Nothing }))
  , Flag "fno-llf-clo-growth-in-lam"     (noArg       (\f -> f{ lateFloatCloGrowthInLam = Just 0 }))
 ]
 ++ map (mkFlag turnOn  "f"    setGeneralFlag  ) sFlags
 ++ map (mkFlag turnOff "fno-" unSetGeneralFlag) sFlags

type TurnOnFlag = Bool   -- True  <=> we are turning the flag on
                        -- False <=> we are turning the flag off
turnOn  :: TurnOnFlag; turnOn  = True
turnOff :: TurnOnFlag; turnOff = False

type FlagSpec flag
  = ( String   -- Flag in string form
    , flag     -- Flag in internal form
    , TurnOnFlag -> DynP ())    -- Extra action to run when the flag is found
                                -- Typically, emit a warning or error

mkFlag :: TurnOnFlag            -- ^ True <=> it should be turned on
      -> String                -- ^ The flag prefix
      -> (flag -> DynP ())     -- ^ What to do when the flag is found
      -> FlagSpec flag         -- ^ Specification of this particular flag
      -> Flag (CmdLineP SeqFlags)
mkFlag turn_on flagPrefix f (name, flag, extra_action)
   = Flag (flagPrefix ++ name) (NoArg (f flag >> extra_action turn_on))

nop :: TurnOnFlag -> DynP ()
nop _ = return ()

sFlags :: [FlagSpec SeqGeneralFlag]
sFlags = [
  ( "seq-simpl",                 Opt_EnableSeqSimpl, nop),
  ( "seq-full-laziness",         Opt_EnableSeqFloatOut, nop),
  ( "seq-spec-constr",           Opt_EnableSeqSpecConstr, nop),
  
  ( "seq-combine-passes",        Opt_CombineSeqPasses, nop),
  
  ( "llf",                       Opt_LLF, nop),
  ( "llf-abstract-undersat",     Opt_LLF_AbsUnsat, nop),
  ( "llf-abstract-sat",          Opt_LLF_AbsSat, nop),
  ( "llf-abstract-oversat",      Opt_LLF_AbsOversat, nop),
  ( "llf-create-PAPs",           Opt_LLF_CreatePAPs, nop),
  ( "llf-simpl",                 Opt_LLF_Simpl, nop),
  ( "llf-stabilize",             Opt_LLF_Stabilize, nop),
  ( "llf-use-strictness",        Opt_LLF_UseStr, nop),
  ( "llf-oneshot",               Opt_LLF_OneShot, nop),
  ( "float-nullary-joins",       Opt_FloatNullaryJoins, nop)
 ]

type DynP = EwM (CmdLineP SeqFlags)

noArg :: (SeqFlags -> SeqFlags) -> OptKind (CmdLineP SeqFlags)
noArg fn = NoArg (upd fn)

intSuffix :: (Int -> SeqFlags -> SeqFlags) -> OptKind (CmdLineP SeqFlags)
intSuffix fn = IntSuffix (\n -> upd (fn n))

upd :: (SeqFlags -> SeqFlags) -> DynP ()
upd f = liftEwM (do dflags <- getCmdLineState
                    putCmdLineState $! f dflags)

setDumpFlag :: SeqDumpFlag -> OptKind (CmdLineP SeqFlags)
setDumpFlag dump_flag = NoArg (setDumpFlag' dump_flag)

--------------------------
setGeneralFlag, unSetGeneralFlag :: SeqGeneralFlag -> DynP ()
setGeneralFlag   f = upd (setGeneralFlag' f)
unSetGeneralFlag f = upd (unSetGeneralFlag' f)

setGeneralFlag' :: SeqGeneralFlag -> SeqFlags -> SeqFlags
setGeneralFlag' f dflags = sgopt_set dflags f
unSetGeneralFlag' :: SeqGeneralFlag -> SeqFlags -> SeqFlags
unSetGeneralFlag' f dflags = sgopt_unset dflags f

setDumpFlag' :: SeqDumpFlag -> DynP ()
setDumpFlag' dump_flag = upd (\dfs -> sdopt_set dfs dump_flag)

--------------------------

-- These two datatypes are copied from CoreMonad in the wip/llf branch. Defined
-- here so that both Driver and FloatOut can use them.

data FloatOutSwitches = FloatOutSwitches {
  floatOutLambdas   :: Maybe Int,
  -- ^ Just n <=> float lambdas to top level, if doing so will
  -- abstract over n or fewer value variables Nothing <=> float all
  -- lambdas to top level, regardless of how many free variables Just
  -- 0 is the vanilla case: float a lambda iff it has no free vars
  floatOutConstants :: Bool,
  -- ^ True <=> float constants to top level, even if they do not
  -- escape a lambda
  floatOutPartialApplications :: Bool,
  -- ^ True <=> float out partial applications based on arity
  -- information.
  finalPass_        :: Maybe FinalPassSwitches
  -- ^ Nothing <=> not the final pass, behave like normal
  }

data FinalPassSwitches = FinalPassSwitches
  { fps_rec            :: !(Maybe Int)
  -- ^ used as floatOutLambdas for recursive lambdas
  , fps_absUnsatVar    :: !Bool
  -- ^ abstract over undersaturated applied variables?
  , fps_absSatVar      :: !Bool
  -- ^ abstract over exactly saturated applied variables? Doing so might lose some fast entries
  , fps_absOversatVar  :: !Bool
  -- ^ abstracting over oversaturated applied variables?
  , fps_createPAPs     :: !Bool
  -- ^ allowed to float functions occuring unapplied
  , fps_cloGrowth    :: !(Maybe Int)
  -- ^ limits the number of free variables added to closures using the floated function
  , fps_ifInClo        :: !(Maybe Int)
  -- ^ limits the number of abstracted variables allowed if the binder occurs in a closure
  , fps_stabilizeFirst   :: !Bool
  -- ^ stabilizes an unstable unfolding before floating things out of
  -- it, since floating out precludes specialization at the call-site
  , fps_cloGrowthInLam :: !(Maybe Int)
  -- ^ disallow the floating of a binding if it occurs in closure that
  -- is allocated inside a lambda
  , fps_trace             :: !Bool
  , fps_strictness        :: !Bool
  , fps_oneShot           :: !Bool
  }

instance Outputable FloatOutSwitches where
    ppr = pprFloatOutSwitches

pprFloatOutSwitches :: FloatOutSwitches -> SDoc
pprFloatOutSwitches sw 
  = ptext (sLit "FOS") <+> (braces $
     sep $ punctuate comma $ 
     [ ptext (sLit "Lam =")    <+> ppr (floatOutLambdas sw)
     , ptext (sLit "Consts =") <+> ppr (floatOutConstants sw)
     , ptext (sLit "PAPs =")   <+> ppr (floatOutPartialApplications sw)
     , ptext (sLit "Late =")   <+> ppr (finalPass_ sw)])

instance Outputable FinalPassSwitches where
    ppr = pprFinalPassSwitches

pprFinalPassSwitches :: FinalPassSwitches -> SDoc
pprFinalPassSwitches sw = sep $ punctuate comma $
  [ ptext (sLit "Rec =")    <+> ppr (fps_rec sw)
  , ptext (sLit "AbsUnsatVar =") <+> ppr (fps_absUnsatVar sw)
  , ptext (sLit "AbsSatVar =") <+> ppr (fps_absSatVar sw)
  , ptext (sLit "AbsOversatVar =") <+> ppr (fps_absOversatVar sw)
  , ptext (sLit "ClosureGrowth =") <+> ppr (fps_cloGrowth sw)
  , ptext (sLit "ClosureGrowthInLam =") <+> ppr (fps_cloGrowthInLam sw)
  , ptext (sLit "StabilizeFirst =") <+> ppr (fps_stabilizeFirst sw)
  ]
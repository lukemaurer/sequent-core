module Language.SequentCore.FloatOut.Flags (
  FloatFlags(..), FloatGeneralFlag(..), fgopt, FinalPassSwitches(..),
  
  parseFloatFlags
) where

import CmdLineParser
import Panic
import MonadUtils
import SrcLoc

import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

parseFloatFlags :: MonadIO m => [String]
                -> m (FloatFlags, [String], [String])
parseFloatFlags args = do
  let ((leftover, errs, warns), fflags)
          = runCmdLine (processArgs floatFlags (map noLoc args))
                       defaultFloatFlags
  when (not (null errs)) $ liftIO $
      throwGhcExceptionIO $ errorsToGhcException errs

  return (fflags, map unLoc leftover, map unLoc warns)

data FloatGeneralFlag
  = Opt_ProtectLastValArg
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

data FloatFlags = FloatFlags {
  doptDumpLateFloat       :: Bool,
  floatGeneralFlags       :: IntSet,
  lateFloatNonRecLam      :: Maybe Int,   -- ^ Limit on # abstracted variables for *late* non-recursive function floating (Nothing => all, Just 0 => none)
  lateFloatRecLam         :: Maybe Int,   -- ^   "    " "     "          "     for *late*     recursive function floating
  lateFloatIfInClo        :: Maybe Int,   -- ^ Limit on # abstracted variables for floating a binding that occurs in a closure
  lateFloatCloGrowth      :: Maybe Int,   -- ^ Limit on # additional free variables for closures in which the function occurs
  lateFloatCloGrowthInLam :: Maybe Int
}

defaultFloatFlags :: FloatFlags
defaultFloatFlags =
  FloatFlags {
    doptDumpLateFloat       = False,
    floatGeneralFlags       = IntSet.fromList (map fromEnum defaultGeneralFlags),
    lateFloatNonRecLam      = Just 10,
    lateFloatRecLam         = Just 6,
    lateFloatIfInClo        = Nothing,
    lateFloatCloGrowth      = Just 0,
    lateFloatCloGrowthInLam = Just 0
  }

defaultGeneralFlags :: [FloatGeneralFlag]
defaultGeneralFlags = [ Opt_LLF_AbsUnsat, Opt_LLF_UseStr, Opt_LLF_OneShot,
                        Opt_LLF_Simpl, Opt_LLF_Stabilize ]

-- | Test whether a 'FloatGeneralFlag' is set
fgopt :: FloatGeneralFlag -> FloatFlags -> Bool
fgopt f fflags  = fromEnum f `IntSet.member` floatGeneralFlags fflags

-- | Set a 'FloatGeneralFlag'
fgopt_set :: FloatFlags -> FloatGeneralFlag -> FloatFlags
fgopt_set ffs f = ffs{ floatGeneralFlags = IntSet.insert (fromEnum f) (floatGeneralFlags ffs) }

-- | Unset a 'FloatGeneralFlag'
fgopt_unset :: FloatFlags -> FloatGeneralFlag -> FloatFlags
fgopt_unset ffs f = ffs{ floatGeneralFlags = IntSet.delete (fromEnum f) (floatGeneralFlags ffs) }

floatFlags :: [Flag (CmdLineP FloatFlags)]
floatFlags = [
    Flag "ddump-llf"                     (noArg       (\f -> f{ doptDumpLateFloat = True }))
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
 ++ map (mkFlag turnOn  "f"    setGeneralFlag  ) fFlags
 ++ map (mkFlag turnOff "fno-" unSetGeneralFlag) fFlags

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
      -> Flag (CmdLineP FloatFlags)
mkFlag turn_on flagPrefix f (name, flag, extra_action)
   = Flag (flagPrefix ++ name) (NoArg (f flag >> extra_action turn_on))

nop :: TurnOnFlag -> DynP ()
nop _ = return ()

fFlags :: [FlagSpec FloatGeneralFlag]
fFlags = [
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

type DynP = EwM (CmdLineP FloatFlags)

noArg :: (FloatFlags -> FloatFlags) -> OptKind (CmdLineP FloatFlags)
noArg fn = NoArg (upd fn)

intSuffix :: (Int -> FloatFlags -> FloatFlags) -> OptKind (CmdLineP FloatFlags)
intSuffix fn = IntSuffix (\n -> upd (fn n))

upd :: (FloatFlags -> FloatFlags) -> DynP ()
upd f = liftEwM (do dflags <- getCmdLineState
                    putCmdLineState $! f dflags)

--------------------------
setGeneralFlag, unSetGeneralFlag :: FloatGeneralFlag -> DynP ()
setGeneralFlag   f = upd (setGeneralFlag' f)
unSetGeneralFlag f = upd (unSetGeneralFlag' f)

setGeneralFlag' :: FloatGeneralFlag -> FloatFlags -> FloatFlags
setGeneralFlag' f dflags = fgopt_set dflags f
unSetGeneralFlag' :: FloatGeneralFlag -> FloatFlags -> FloatFlags
unSetGeneralFlag' f dflags = fgopt_unset dflags f

--------------------------
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
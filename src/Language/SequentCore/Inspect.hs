-- |
-- Module      : Language.SequentCore.Inspect
-- Description : Sequent Core information dumper
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- An optimizer plugin that reports specified information about the module from
-- a Sequent Core standpoint.

module Language.SequentCore.Inspect (
  plugin
) where

import GhcPlugins ( Plugin(installCoreToDos), CommandLineOption
                  , defaultPlugin
                  , reinitializeGlobals
                  , CoreM, CoreToDo(CoreDoPluginPass)
                  , putMsg, fatalErrorMsg, liftIO
                  , getDynFlags, ufCreationThreshold
                  )

import Language.SequentCore.FVs
import Language.SequentCore.Lint
import Language.SequentCore.Simpl.ExprSize
import Language.SequentCore.Syntax
import Language.SequentCore.Plugin

import ErrUtils   ( ghcExit )
import Outputable
import Maybes     ( whenIsJust )
import VarSet

import Control.Monad ( forM_, unless, when )

-- | The plugin. A GHC plugin is a module that exports a value called @plugin@
-- with the type 'Plugin'.
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install cmdLine todos =
  do reinitializeGlobals
     let opts    = parseOpts cmdLine
         newPass = mkPass opts
         todos'  = case opt_where opts of
                     AtStart -> newPass : todos
                     AtEnd   -> todos ++ [newPass]
                     AtBoth  -> newPass : todos ++ [newPass]
         unknownOpts = opt_badOptions opts
     unless (null unknownOpts) $ do
       fatalErrorMsg $ hang (text "Language.SequentCore.Inspect: Unrecognized option(s): ") 4
                       (pprWithCommas (quotes . text) unknownOpts)
       dflags <- getDynFlags
       liftIO $ ghcExit dflags 1
     
     return todos'
  where
    mkPass opts   = CoreDoPluginPass "SeqCoreInspect" (passFunc opts)
    passFunc opts = sequentPass (inspectSequentCore opts)

data Options = Options { opt_where :: Where
                       , opt_silent, opt_lint, opt_sizes :: Bool
                       , opt_defs, opt_fvs :: Bool
                       , opt_badOptions :: [CommandLineOption] }

data Where   = AtStart | AtEnd | AtBoth

defaults :: Options
defaults = Options { opt_where  = AtStart
                   , opt_silent = False
                   , opt_lint   = True
                   , opt_sizes  = False
                   , opt_defs   = False
                   , opt_fvs    = False
                   , opt_badOptions = [] }

parseOpts :: [CommandLineOption] -> Options
parseOpts = foldl parse defaults . concatMap (split ',')
  where
    parse opts str = case str of
      "start"  -> opts { opt_where  = AtStart }
      "end"    -> opts { opt_where  = AtEnd   }
      "both"   -> opts { opt_where  = AtBoth  }
      "lint"   -> opts { opt_lint   = True    }
      "nolint" -> opts { opt_lint   = False   }
      "silent" -> opts { opt_silent = True    }
      "size"   -> opts { opt_sizes  = True    }
      "defs"   -> opts { opt_defs   = True    }
      "fvs"    -> opts { opt_fvs    = True    }
      _        -> opts { opt_badOptions = str : opt_badOptions opts }
    
    split _ [] = []
    split c cs = case break (== c) cs of
                   (end, []) -> [end]
                   (next, _:rest) -> next : split c rest

inspectSequentCore :: Options -> [SeqCoreBind] -> CoreM [SeqCoreBind]
inspectSequentCore opts bs = do
  inspect opts bs
  when (opt_lint opts) $
    whenIsJust (lintCoreBindings bs) $ \err -> do
      fatalErrorMsg $ hang (text "lint error in dumped code") 4 err
      dflags <- getDynFlags
      liftIO $ ghcExit dflags 1
  return bs

inspect :: Options -> [SeqCoreBind] -> CoreM ()
inspect (Options { opt_silent = True }) _ = return ()
inspect opts bs = do
  forM_ bs $ \bind -> case bind of
    NonRec pair -> showBind opts pair
    Rec pairs -> forM_ pairs (showBind opts)

showBind :: Options -> SeqCoreBindPair -> CoreM ()
showBind opts pair
  = do
    dflags <- getDynFlags
    let x = binderOfPair pair
        idPart = ppr x
        cap = ufCreationThreshold dflags
        sizePart | opt_sizes opts = ppr size
                 | otherwise      = empty
        size = case pair of
                 BindTerm _ term -> termSize dflags cap term
                 BindJoin _ join -> joinSize dflags cap join
        fvPart = ppWhen (opt_fvs opts) $
                   text "FVs:" <+> pprWithCommas ppr (varSetElems (freeVars pair))
        defPart = ppWhen (opt_defs opts) $ ppr pair
    putMsg $ sep [ idPart, sizePart, fvPart, defPart ]

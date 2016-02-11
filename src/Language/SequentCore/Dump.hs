-- |
-- Module      : Language.SequentCore.Dump
-- Description : Example plugin
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- An example GHC optimizer plugin using Sequent Core. Simply translates the
-- given Core code to Sequent Core, passes it through Lint, dumps it to the
-- screen, then translates back. This allows inspection of the Sequent Core code
-- for a module and also tests the translation and linting functions.
--
-- Note that translating to Sequent Core and back should give an /equivalent/
-- program, but it may vary slightly. The effects should be benign, such as a
-- @let@ floating around in an expression (but never across a lambda).

module Language.SequentCore.Dump (
  plugin
) where

import GhcPlugins ( Plugin(installCoreToDos), CommandLineOption
                  , defaultPlugin
                  , reinitializeGlobals
                  , CoreM, CoreToDo(CoreDoPluginPass)
                  , errorMsg, putMsg
                  )

import Language.SequentCore.Driver.Flags
import Language.SequentCore.Lint
import Language.SequentCore.Syntax
import Language.SequentCore.Plugin
import Language.SequentCore.Pretty (pprTopLevelBinds)

import Outputable ( pprPanic
                  , withPprStyle, defaultUserStyle
                  , vcat, text )

import Control.Monad ( unless )

-- | The plugin. A GHC plugin is a module that exports a value called @plugin@
-- with the type 'Plugin'.
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
  do reinitializeGlobals
     (sflags, leftovers, warns) <- parseSeqFlags (concatMap words opts)
     unless (null warns) $
       errorMsg $ vcat (map text warns)
     let newPass  = CoreDoPluginPass "sequent-core-dump" passFunc
         passFunc = sequentPassWithFlags sflags showSequentCore
     return $ case leftovers of
                ["end"]  -> todos ++ [newPass]
                ["both"] -> newPass : todos ++ [newPass]
                _        -> newPass : todos

showSequentCore :: [SeqCoreBind] -> CoreM [SeqCoreBind]
showSequentCore bs = do
  putMsg (pprTopLevelBinds bs)
  case lintCoreBindings bs of
    Just err -> pprPanic "lint error in dumped code" $
                  withPprStyle defaultUserStyle err
    Nothing  -> return bs

module SequentCore (plugin) where

import Language.SequentCore.Driver
import Language.SequentCore.Driver.Flags

import Control.Monad

import CoreMonad   ( Plugin(..)
                   , defaultPlugin, getDynFlags, reinitializeGlobals )

import ErrUtils
import MonadUtils
import Outputable

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = \cmdLine todos -> do
    reinitializeGlobals
    let cmdLine' = concatMap words cmdLine
          -- Allow -fplugin-opt=plugin:"opt1 opt2"
    (sflags, leftovers, warns) <- parseSeqFlags cmdLine'
    dflags <- getDynFlags
    unless (null leftovers) $
      liftIO $ errorMsg dflags $
        text "Leftover options to SequentCore:" $$
        vcat (map text leftovers)
    unless (null warns) $
      liftIO $ errorMsg dflags $ vcat (map text warns)
    installSequentCorePasses sflags todos
}

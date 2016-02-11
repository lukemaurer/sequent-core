-- |
-- Module      : Language.SequentCore.Plugin
-- Description : GHC plugin library
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Tools for writing a GHC plugin using the Sequent Core language in place of
-- GHC Core.

module Language.SequentCore.Plugin (
  sequentPass, sequentPassWithFlags
) where

import Language.SequentCore.Driver.Flags
import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import GhcPlugins ( ModGuts, CoreM
                  , bindsOnlyPass
                  , deShadowBinds
                  )

-- | Given a function that processes a module's bindings as Sequent Core terms,
-- perform the same processing as a Core-to-Core pass usable from a GHC plugin.
-- Intended to be passed to the @CoreDoPluginPass@ constructor as part of your
-- plugin's @installCoreToDos@ function. See "Language.SequentCore.Dump" for an
-- example and the GHC manual for more details.
sequentPass :: ([SeqCoreBind] -> CoreM [SeqCoreBind])
            -- ^ A processing function. May assume that there are no shadowed
            -- identifiers in the given binders (this is ensured by a call to
            -- 'deShadowBinds').
            -> (ModGuts -> CoreM ModGuts)
sequentPass process =
  bindsOnlyPass (fmap bindsToCore . process . fromCoreModule . deShadowBinds)

-- | Similar to 'sequentPass', but takes a 'SeqFlags' for use by the
-- translation.
sequentPassWithFlags :: SeqFlags
                     -> ([SeqCoreBind] -> CoreM [SeqCoreBind])
                     -> (ModGuts -> CoreM ModGuts)
sequentPassWithFlags sflags process =
  bindsOnlyPass $ \binds -> do
    term  <- fromCoreModuleM sflags (deShadowBinds binds)
    term' <- process term
    return $ bindsToCore term'

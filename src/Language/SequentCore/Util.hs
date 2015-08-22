-- | 
-- Module      : Language.SequentCore.Util
-- Description : Utilities used by the Sequent Core library
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental

module Language.SequentCore.Util (
  Maybes.orElse, consMaybe, mapWhileJust, pprTraceShort
) where

import DynFlags
import Maybes
import Outputable
import StaticFlags

infixr 5 `consMaybe`

consMaybe :: Maybe a -> [a] -> [a]
Just x  `consMaybe` xs = x : xs
Nothing `consMaybe` xs = xs

mapWhileJust :: (a -> Maybe b) -> [a] -> ([b], [a])
mapWhileJust f (x : xs) | Just y <- f x = (y : ys, xs')
  where (ys, xs') = mapWhileJust f xs
mapWhileJust _ xs = ([], xs)

pprTraceShort :: String -> SDoc -> a -> a
-- ^ If debug output is on, show some 'SDoc' on the screen
pprTraceShort str doc x
   | opt_NoDebugOutput = x
   | otherwise         = pprAndThen unsafeGlobalDynFlags trace str
                          (withPprStyle shortStyle doc) x
   where
     shortStyle = mkUserStyle neverQualify (PartWay 3)
   
pprAndThen :: DynFlags -> (String -> a) -> String -> SDoc -> a
pprAndThen dflags kont heading pretty_msg
  = kont (showSDoc dflags doc)
    where
        doc = sep [text heading, nest 4 pretty_msg]

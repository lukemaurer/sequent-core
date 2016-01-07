module Language.SequentCore.Simpl.Util (
  ArgInfo, tracing, traceTicks
) where

import Outputable

data ArgInfo

instance Outputable ArgInfo

tracing, traceTicks :: Bool

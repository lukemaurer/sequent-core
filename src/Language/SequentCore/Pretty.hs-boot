{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.SequentCore.Pretty () where

import {-# SOURCE #-} Language.SequentCore.Syntax

import Outputable

instance OutputableBndr b => Outputable (Bind b)
instance OutputableBndr b => Outputable (Term b)
instance OutputableBndr b => Outputable (Command b)
instance OutputableBndr b => Outputable (Frame b)
instance OutputableBndr b => Outputable (End b)
instance OutputableBndr b => Outputable (Alt b)

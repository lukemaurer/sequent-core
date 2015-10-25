module Language.SequentCore.Pretty where

import {-# SOURCE #-} Language.SequentCore.Syntax

import Outputable

pprTerm     :: OutputableBndr b => Term b     -> SDoc
pprCommand  :: OutputableBndr b => Command b  -> SDoc
pprFrame    :: OutputableBndr b => Frame b    -> SDoc
pprEnd      :: OutputableBndr b => End b      -> SDoc
pprAlt      :: OutputableBndr b => Alt b      -> SDoc
pprJoin     :: OutputableBndr b => Join b     -> SDoc
pprBind     :: OutputableBndr b => Bind b     -> SDoc
pprBindPair :: OutputableBndr b => BindPair b -> SDoc

module Language.SequentCore.Translate where

import Language.SequentCore.Syntax

import BasicTypes ( RecFlag )
import CoreSyn    ( CoreExpr )
import Type       ( Type )

termFromCoreExpr :: CoreExpr -> SeqCoreTerm
termToCoreExpr   :: SeqCoreTerm -> CoreExpr
joinToCoreExpr   :: Type -> SeqCoreJoin -> CoreExpr
joinToCoreExpr'  :: RecFlag -> Type -> SeqCoreJoin -> CoreExpr
onCoreExpr       :: (SeqCoreTerm -> SeqCoreTerm) -> (CoreExpr -> CoreExpr)
{-# LANGUAGE FunctionalDependencies, TypeSynonymInstances, FlexibleInstances #-}

-- |
-- Module      : Language.SequentCore.FVs
-- Description : Free variable analysis for Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Routines for calculating the free variables of Sequent Core expressions.
-- FV sets can be returned directly, or the AST can be annotated with the
-- free variables at each node.

module Language.SequentCore.FVs (
  module Language.SequentCore.Annot,
  FreeVars(..), InterestingVarFun,

  SeqCoreTermWithFVs, SeqCoreArgWithFVs, SeqCoreFrameWithFVs, SeqCoreEndWithFVs,
  SeqCoreCommandWithFVs, SeqCoreJoinWithFVs, SeqCoreBindPairWithFVs,
  SeqCoreBindWithFVs, SeqCoreAltWithFVs, SeqCoreKontWithFVs,
  SeqCoreProgramWithFVs
) where

import Language.SequentCore.Annot
import Language.SequentCore.Syntax

import qualified CoreFVs
import CoreSyn  ( Tickish(..) )
import Coercion
import Id
import Type
import Var
import VarSet

import Control.Applicative ( (<$>) )

-- | Predicate on possible free variables: returns @True@ iff the variable is interesting
type InterestingVarFun = Var -> Bool

class FreeVars a a' | a -> a', a' -> a where
  -- | Find all locally-defined free Ids or type variables in an expression
  freeVars     :: a -> VarSet
  -- | Find all locally-defined free Ids in an expression
  freeIds      :: a -> IdSet
  -- | Finds free variables in an expression selected by a predicate
  someFreeVars :: InterestingVarFun -> a -> VarSet

  -- For simplicity, we implement everything in terms of the annotated AST. If
  -- needed, we could implement the single-expression case separately (as
  -- CoreFVs does).
  freeVars = getFreeVars . withFreeVars
  freeIds = someFreeVars isId
  someFreeVars fv_cand = filterVarSet fv_cand . freeVars

  -- | Every node in an expression annotated with its
  -- (non-global) free variables, both Ids and TyVars
  withFreeVars :: a -> a'
  -- | Read free variables from annotation
  getFreeVars  :: a' -> VarSet

type SeqCoreTermWithFVs     = AnnTerm     Var VarSet
type SeqCoreArgWithFVs      = AnnArg      Var VarSet
type SeqCoreFrameWithFVs    = AnnFrame    Var VarSet
type SeqCoreEndWithFVs      = AnnEnd      Var VarSet
type SeqCoreCommandWithFVs  = AnnCommand  Var VarSet
type SeqCoreJoinWithFVs     = AnnJoin     Var VarSet
type SeqCoreBindPairWithFVs = AnnBindPair Var VarSet
type SeqCoreBindWithFVs     = AnnBind     Var VarSet
type SeqCoreAltWithFVs      = AnnAlt      Var VarSet
type SeqCoreKontWithFVs     = AnnKont     Var VarSet
type SeqCoreProgramWithFVs  = AnnProgram  Var VarSet

--------------------
-- Implementation --
--------------------

noFVs :: VarSet
noFVs    = emptyVarSet

aFreeVar :: Var -> VarSet
aFreeVar = unitVarSet

someFVs :: [Var] -> VarSet
someFVs  = mkVarSet

unionFVs :: VarSet -> VarSet -> VarSet
unionFVs = unionVarSet

unionsFVs :: [VarSet] -> VarSet
unionsFVs = unionVarSets

delBindersFV :: [Var] -> VarSet -> VarSet
delBindersFV bs fvs = foldr delBinderFV fvs bs

delBinderFV :: Var -> VarSet -> VarSet
delBinderFV b s = (s `delVarSet` b) `unionFVs` tyVarsOfType (varType b)
  -- See commant in CoreFVs on adding type variables

instance FreeVars SeqCoreTerm SeqCoreTermWithFVs where
  getFreeVars (fvs, _) = fvs

  withFreeVars term
    = case term of Lit literal     -> (noFVs, AnnLit literal)
                   Var id          -> (fvs, AnnVar id)
                     where
                       fvs | isLocalVar id = aFreeVar id
                           | otherwise     = noFVs
                   Lam b body      -> (b `delBinderFV` getFreeVars body',
                                       AnnLam b body')
                     where
                       body' = withFreeVars body
                   Compute ty comm -> (getFreeVars comm', AnnCompute ty comm')
                     where
                       comm' = withFreeVars comm
                   Type ty         -> (tyVarsOfType ty, AnnType ty)
                   Coercion co     -> (tyCoVarsOfCo co, AnnCoercion co)

instance FreeVars SeqCoreFrame SeqCoreFrameWithFVs where
  getFreeVars (fvs, _) = fvs

  withFreeVars frame
    = case frame of App arg -> (getFreeVars arg', AnnApp arg')
                      where
                        arg' = withFreeVars arg
                    Cast co -> (tyCoVarsOfCo co, AnnCast co)
                    Tick ti -> (fvs, AnnTick ti)
                      where
                        fvs = case ti of Breakpoint _ ids -> someFVs ids
                                         _                -> noFVs

instance FreeVars SeqCoreEnd SeqCoreEndWithFVs where
  getFreeVars (fvs, _) = fvs

  withFreeVars end
    = case end of Return         -> (noFVs, AnnReturn)
                  Case bndr alts -> (bndr `delBinderFV` fvs_alts,
                                     AnnCase bndr alts')
                    where
                      alts' = map withFreeVars alts
                      fvs_alts = unionsFVs (map getFreeVars alts')

instance FreeVars SeqCoreCommand SeqCoreCommandWithFVs where
  getFreeVars (fvs, _) = fvs

  withFreeVars comm
    = case comm of Let bind body        -> (fvs, AnnLet bind' body')
                     where
                       bind'   = withFreeVars bind
                       body'   = withFreeVars body
                       bndrs   = bindersOfBinds [bind]
                       fvs     = (bndrs `delBindersFV` getFreeVars body')
                                   `unionFVs` getFreeVars bind'
                   Eval term frames end -> (fvs, AnnEval term' frames' end')
                     where
                       term'   = withFreeVars term
                       frames' = withFreeVars <$> frames
                       end'    = withFreeVars end
                       fvs     = getFreeVars term' `unionFVs` getFreeVars end'
                                   `unionFVs` unionsFVs (getFreeVars <$> frames')
                   Jump args j          -> (fvs, AnnJump args' j)
                     where
                       args'   = withFreeVars <$> args
                       fvs     = unionsFVs (getFreeVars <$> args')
                                   `unionFVs` aFreeVar j

instance FreeVars SeqCoreJoin SeqCoreJoinWithFVs where
  getFreeVars (fvs, _) = fvs

  withFreeVars join
    = case join of Join bndrs comm -> (bndrs `delBindersFV` getFreeVars comm',
                                       AnnJoin bndrs comm')
                     where
                       comm' = withFreeVars comm

instance FreeVars SeqCoreBindPair SeqCoreBindPairWithFVs where
  getFreeVars (fvs, _) = fvs

  withFreeVars pair
    = case pair of BindTerm bndr term -> (bndrRuleAndUnfoldingVars bndr
                                            `unionFVs` getFreeVars term',
                                          AnnBindTerm bndr term')
                     where
                       term' = withFreeVars term
                   BindJoin bndr join -> (bndrRuleAndUnfoldingVars bndr
                                            `unionFVs` getFreeVars join',
                                          AnnBindJoin bndr join')
                     where
                       join' = withFreeVars join

instance FreeVars SeqCoreBind SeqCoreBindWithFVs where
  getFreeVars (fvs, _) = fvs

  withFreeVars bind
    = case bind of NonRec pair -> (getFreeVars pair', AnnNonRec pair')
                     where
                       pair' = withFreeVars pair
                   Rec pairs   -> (bndrs `delBindersFV` fvs_all, AnnRec pairs')
                     where
                       pairs' = withFreeVars <$> pairs
                       bndrs = binderOfPair <$> pairs
                       fvs_all = unionsFVs (getFreeVars <$> pairs')

instance FreeVars SeqCoreAlt SeqCoreAltWithFVs where
  getFreeVars (fvs, _) = fvs

  withFreeVars alt
    = case alt of Alt con bndrs rhs -> (bndrs `delBindersFV` getFreeVars rhs',
                                        AnnAlt con bndrs rhs')
                    where
                      rhs' = withFreeVars rhs

bndrRuleAndUnfoldingVars :: Var -> VarSet
bndrRuleAndUnfoldingVars var | isId var  = CoreFVs.idRuleAndUnfoldingVars var
                             | otherwise = emptyVarSet

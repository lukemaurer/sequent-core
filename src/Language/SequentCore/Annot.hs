-- |
-- Module      : Language.SequentCore.Annot
-- Description : Annotated Sequent Core syntax
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Annotated AST types for Sequent Core.

module Language.SequentCore.Annot (
  -- * Annotated AST Types
  AnnTerm, AnnTerm'(..), AnnArg, AnnFrame, AnnFrame'(..), AnnEnd, AnnEnd'(..),
  AnnCommand, AnnCommand'(..), AnnJoin, AnnJoin'(..),
  AnnBindPair, AnnBindPair'(..), AnnBind, AnnBind'(..), AnnAlt, AnnAlt'(..),
  AnnKont, AnnProgram,

  -- * Removing Annotations
  deAnnotateTerm, deAnnotateTerm', deAnnotateFrame, deAnnotateFrame',
  deAnnotateEnd, deAnnotateEnd', deAnnotateCommand, deAnnotateCommand',
  deAnnotateJoin, deAnnotateJoin', deAnnotateBindPair, deAnnotateBindPair',
  deAnnotateBind, deAnnotateAlt,

  -- * Operations on Annotated AST
  binderOfAnnPair, bindersOfAnnBind, bindersOfAnnBinds,
  collectAnnBinders, collectAnnArgs
) where

import Language.SequentCore.Syntax
import Language.SequentCore.Util

import Coercion
import CoreSyn  ( Tickish )
import Id
import Literal
import Type

import Control.Applicative ( (<$>) )

type AnnTerm b a      = (a, AnnTerm' b a)

data AnnTerm' b a     = AnnLit Literal
                      | AnnVar Id
                      | AnnLam b (AnnTerm b a)
                      | AnnCompute Type (AnnCommand b a)
                      | AnnType Type
                      | AnnCoercion Coercion

type AnnArg b a       = AnnTerm b a

type AnnFrame b a     = (a, AnnFrame' b a)
data AnnFrame' b a    = AnnApp (AnnArg b a)
                      | AnnCast Coercion
                      | AnnTick (Tickish Id)

type AnnEnd b a       = (a, AnnEnd' b a)
data AnnEnd' b a      = AnnReturn
                      | AnnCase b [AnnAlt b a]

type AnnCommand b a   = (a, AnnCommand' b a)
data AnnCommand' b a  = AnnLet (AnnBind b a) (AnnCommand b a)
                      | AnnEval (AnnTerm b a) [AnnFrame b a] (AnnEnd b a)
                      | AnnJump [AnnArg b a] JoinId

type AnnJoin b a      = (a, AnnJoin' b a)
data AnnJoin' b a     = AnnJoin [b] (AnnCommand b a)

type AnnBindPair b a  = (a, AnnBindPair' b a)
data AnnBindPair' b a = AnnBindTerm b (AnnTerm b a)
                      | AnnBindJoin b (AnnJoin b a)

type AnnBind  b a     = (a, AnnBind' b a)
data AnnBind' b a     = AnnNonRec (AnnBindPair b a)
                      | AnnRec [AnnBindPair b a]

type AnnAlt b a       = (a, AnnAlt' b a)
data AnnAlt' b a      = AnnAlt AltCon [b] (AnnCommand b a)

type AnnKont b a      = ([AnnFrame b a], AnnEnd b a)

type AnnProgram b a   = [AnnBind b a]

deAnnotateTerm      :: AnnTerm b a      -> Term b
deAnnotateFrame     :: AnnFrame b a     -> Frame b
deAnnotateEnd       :: AnnEnd b a       -> End b
deAnnotateCommand   :: AnnCommand b a   -> Command b
deAnnotateJoin      :: AnnJoin b a      -> Join b
deAnnotateBindPair  :: AnnBindPair b a  -> BindPair b
deAnnotateBind      :: AnnBind b a      -> Bind b
deAnnotateAlt       :: AnnAlt b a       -> Alt b

deAnnotateTerm'     :: AnnTerm' b a     -> Term b
deAnnotateFrame'    :: AnnFrame' b a    -> Frame b
deAnnotateEnd'      :: AnnEnd' b a      -> End b
deAnnotateCommand'  :: AnnCommand' b a  -> Command b
deAnnotateJoin'     :: AnnJoin' b a     -> Join b
deAnnotateBindPair' :: AnnBindPair' b a -> BindPair b
deAnnotateBind'     :: AnnBind' b a     -> Bind b
deAnnotateAlt'      :: AnnAlt' b a      -> Alt b

deAnnotateTerm     (_, term)  = deAnnotateTerm' term
deAnnotateFrame    (_, frame) = deAnnotateFrame' frame
deAnnotateEnd      (_, end)   = deAnnotateEnd' end
deAnnotateCommand  (_, comm)  = deAnnotateCommand' comm
deAnnotateJoin     (_, join)  = deAnnotateJoin' join
deAnnotateBindPair (_, pair)  = deAnnotateBindPair' pair
deAnnotateBind     (_, bind)  = deAnnotateBind' bind
deAnnotateAlt      (_, alt)   = deAnnotateAlt' alt

deAnnotateTerm' term
  = case term of  AnnLit lit            -> Lit lit
                  AnnVar id             -> Var id
                  AnnLam bndr body      -> Lam bndr (deAnnotateTerm body)
                  AnnCompute ty comm    -> Compute ty (deAnnotateCommand comm)
                  AnnType ty            -> Type ty
                  AnnCoercion co        -> Coercion co

deAnnotateFrame' frame
  = case frame of AnnApp arg            -> App (deAnnotateTerm arg)
                  AnnCast co            -> Cast co
                  AnnTick ti            -> Tick ti

deAnnotateEnd' end
  = case end of   AnnReturn             -> Return
                  AnnCase b alts        -> Case b (deAnnotateAlt <$> alts)

deAnnotateCommand' comm
  = case comm of  AnnLet bind comm'     -> Let (deAnnotateBind bind)
                                               (deAnnotateCommand comm')
                  AnnEval term fs end   -> Eval (deAnnotateTerm term)
                                                (deAnnotateFrame <$> fs)
                                                (deAnnotateEnd end)
                  AnnJump args j        -> Jump (deAnnotateTerm <$> args) j

deAnnotateJoin'  (AnnJoin bndrs comm)    = Join bndrs (deAnnotateCommand comm)

deAnnotateBindPair' pair
  = case pair of  AnnBindTerm bndr term -> BindTerm bndr (deAnnotateTerm term)
                  AnnBindJoin bndr join -> BindJoin bndr (deAnnotateJoin join)

deAnnotateBind' bind
  = case bind of  AnnNonRec pair        -> NonRec (deAnnotateBindPair pair)
                  AnnRec pairs          -> Rec (deAnnotateBindPair <$> pairs)

deAnnotateAlt'   (AnnAlt ac bndrs rhs)   = Alt ac bndrs (deAnnotateCommand rhs)

collectAnnBinders :: AnnTerm b a -> ([b], AnnTerm b a)
collectAnnBinders (_, AnnLam bndr body) = (bndr : bndrs, body')
  where (bndrs, body') = collectAnnBinders body
collectAnnBinders term                  = ([], term)

collectAnnArgs :: [AnnFrame b a] -> ([AnnTerm b a], [AnnFrame b a])
collectAnnArgs = mapWhileJust $ \f -> case f of (_, AnnApp arg) -> Just arg
                                                _               -> Nothing

binderOfAnnPair :: AnnBindPair b a -> b
binderOfAnnPair (_, AnnBindTerm bndr _) = bndr
binderOfAnnPair (_, AnnBindJoin bndr _) = bndr

bindersOfAnnBind :: AnnBind b a -> [b]
bindersOfAnnBind (_, AnnNonRec pair) = [binderOfAnnPair pair]
bindersOfAnnBind (_, AnnRec pairs)   = binderOfAnnPair <$> pairs

bindersOfAnnBinds :: [AnnBind b a] -> [b]
bindersOfAnnBinds = concatMap bindersOfAnnBind
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
  binderOfAnnPair, flattenAnnBind, bindersOfAnnBind, bindersOfAnnBinds,
  collectAnnBinders, collectAnnBindersWithAnns, collectAnnArgs, flattenAnnCommand,
  
  -- * Output
  pprTopLevelAnnBinds
) where

import Language.SequentCore.Syntax
import Language.SequentCore.Util

import Coercion
import Id
import Literal
import Outputable
import Type

import Control.Applicative ( (<$>) )
import Data.List

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

flattenAnnCommand :: AnnCommand b a
                  -> ([AnnBind b a], Either (AnnTerm b a, [AnnFrame b a], AnnEnd b a)
                                            ([AnnArg b a], Var))
flattenAnnCommand
  = go []
  where
    go acc (_, AnnLet bind comm)    = go (bind:acc) comm
    go acc (_, AnnEval term fs end) = done acc (Left (term, fs, end))
    go acc (_, AnnJump args j)      = done acc (Right (args, j))
    
    done acc cut = (reverse acc, cut)

collectAnnBinders :: AnnTerm b a -> ([b], AnnTerm b a)
collectAnnBinders (_, AnnLam bndr body) = (bndr : bndrs, body')
  where (bndrs, body') = collectAnnBinders body
collectAnnBinders term                  = ([], term)

collectAnnBindersWithAnns :: AnnTerm b a -> ([(a, b)], AnnTerm b a)
collectAnnBindersWithAnns (a, AnnLam bndr body) = ((a, bndr) : bndrs, body')
  where (bndrs, body') = collectAnnBindersWithAnns body
collectAnnBindersWithAnns term                  = ([], term)

collectAnnArgs :: [AnnFrame b a] -> ([AnnTerm b a], [AnnFrame b a])
collectAnnArgs = mapWhileJust $ \f -> case f of (_, AnnApp arg) -> Just arg
                                                _               -> Nothing

binderOfAnnPair :: AnnBindPair b a -> b
binderOfAnnPair (_, AnnBindTerm bndr _) = bndr
binderOfAnnPair (_, AnnBindJoin bndr _) = bndr

flattenAnnBind :: AnnBind b a -> [AnnBindPair b a]
flattenAnnBind (_, AnnNonRec pair) = [pair]
flattenAnnBind (_, AnnRec pairs)   = pairs

bindersOfAnnBind :: AnnBind b a -> [b]
bindersOfAnnBind bind = binderOfAnnPair <$> flattenAnnBind bind

bindersOfAnnBinds :: [AnnBind b a] -> [b]
bindersOfAnnBinds = concatMap bindersOfAnnBind

-- Output --

instance (OutputableBndr b, Outputable a) => Outputable (AnnTerm' b a)     where ppr = pprAnnTerm'
instance (OutputableBndr b, Outputable a) => Outputable (AnnCommand' b a)  where ppr = pprAnnCommand'
instance (OutputableBndr b, Outputable a) => Outputable (AnnFrame' b a)    where ppr = pprAnnFrame'
instance (OutputableBndr b, Outputable a) => Outputable (AnnEnd' b a)      where ppr = pprAnnEnd'
instance (OutputableBndr b, Outputable a) => Outputable (AnnAlt' b a)      where ppr = pprAnnAlt'
instance (OutputableBndr b, Outputable a) => Outputable (AnnJoin' b a)     where ppr = pprAnnJoin'
instance (OutputableBndr b, Outputable a) => Outputable (AnnBind' b a)     where ppr = pprAnnBind'
instance (OutputableBndr b, Outputable a) => Outputable (AnnBindPair' b a) where ppr = pprAnnBindPair' 

pprAnnTerm' :: (OutputableBndr b, Outputable a) => AnnTerm' b a -> SDoc
pprAnnTerm' = ppr_term noParens

pprAnnCommand' :: (OutputableBndr b, Outputable a) => AnnCommand' b a -> SDoc
pprAnnCommand' = ppr_comm noParens

pprAnnFrame' :: (OutputableBndr b, Outputable a) => AnnFrame' b a -> SDoc
pprAnnFrame' = ppr_frame

pprAnnEnd' :: (OutputableBndr b, Outputable a) => AnnEnd' b a -> SDoc
pprAnnEnd' = ppr_end

pprAnnAlt' :: (OutputableBndr b, Outputable a) => AnnAlt' b a -> SDoc
pprAnnAlt' = ppr_alt

pprAnnJoin' :: (OutputableBndr b, Outputable a) => AnnJoin' b a -> SDoc
pprAnnJoin' = ppr_join noParens

pprAnnBind' :: (OutputableBndr b, Outputable a) => AnnBind' b a -> SDoc
pprAnnBind' = ppr_bind

pprAnnBindPair' :: (OutputableBndr b, Outputable a) => AnnBindPair' b a -> SDoc
pprAnnBindPair' = ppr_binding

--------------------
-- Implementation --
--------------------

ppr_bind :: (OutputableBndr b, Outputable a) => AnnBind' b a -> SDoc
ppr_bind (AnnNonRec pair) = ppr pair
ppr_bind (AnnRec binds)   = hang (text "rec") 2 (vcat $ intersperse space $
                                                  ppr_block (char '{') (char ';') (char '}') (map ppr binds))

ppr_binds_top :: (OutputableBndr b, Outputable a) => [AnnBind b a] -> SDoc
ppr_binds_top binds = ppr_binds_with empty empty empty binds

-- | Print the given bindings as a sequence of top-level bindings.
pprTopLevelAnnBinds :: (OutputableBndr b, Outputable a) => [AnnBind b a] -> SDoc
pprTopLevelAnnBinds = ppr_binds_top

ppr_block :: SDoc -> SDoc -> SDoc -> [SDoc] -> [SDoc]
ppr_block open _ close [] = [open <> close]
ppr_block open mid close (first : rest)
  = open <+> first : map (mid <+>) rest ++ [close]

ppr_binds :: (OutputableBndr b, Outputable a) => [AnnBind b a] -> SDoc
ppr_binds binds = ppr_binds_with (char '{') (char ';') (char '}') binds

ppr_binds_with :: (OutputableBndr b, Outputable a) => SDoc -> SDoc -> SDoc -> [AnnBind b a] -> SDoc
ppr_binds_with open mid close binds = vcat $ intersperse space $ ppr_block open mid close (map ppr binds)

ppr_binding :: (OutputableBndr b, Outputable a) => AnnBindPair' b a -> SDoc
ppr_binding pair
  = prefix <+> pprBndr LetBind val_bdr $$
    hang (ppr val_bdr <+> equals) 2 (pprDeeper body)
  where
    (val_bdr, body, prefix)
      = case pair of AnnBindTerm bndr term -> (bndr, ppr term, empty)
                     AnnBindJoin bndr join -> (bndr, ppr join, text "join")

ppr_comm :: (OutputableBndr b, Outputable a) => (SDoc -> SDoc) -> AnnCommand' b a -> SDoc
ppr_comm add_par comm
  = maybe_add_par $ ppr_let <+> ppr_cut
  where
    (binds, cut) = flattenAnnCommand (undefined, comm)
    ppr_let
      | null binds = empty
      | otherwise  = hang (text "let") 2 (ppr_binds binds) $$ text "in"
    maybe_add_par = if null binds then noParens else add_par
    ppr_cut
      = case cut of
          Left (term, fs, end) 
            -> sep [char '<' <> ppr term,
                    cat $ ppr_block (char '|') (char ';') (char '>') $ (ppr_kont_frames fs ++ [ppr end])]
          Right (args, j)
            -> text "jump" <+> prefix <+> ppr j <+> parens (pprDeeper $ pprWithCommas ppr args)
            where prefix | isTyVar j     = text "TYVAR"
                         | isCoVar j     = text "COVAR"
                         | not (isJoinId j)  = text "IDVAR"
                         | otherwise         = empty

ppr_term :: (OutputableBndr b, Outputable a) => (SDoc -> SDoc) -> AnnTerm' b a -> SDoc
ppr_term _ (AnnVar name) = prefix <+> ppr name
  where prefix | isTyVar name = text "TYVAR"
               | isJoinId name = text "PKVAR"
               | otherwise = empty
  -- Something is quite wrong if it's a type variable!
ppr_term add_par (AnnType ty) = add_par $ text "TYPE" <+> ppr ty
ppr_term add_par (AnnCoercion co) = add_par $ text "CO" <+> ppr co
ppr_term add_par (AnnLit lit) = pprLiteral add_par lit
ppr_term add_par term@(AnnLam {})
  | (k, AnnCompute ty comm) <- body
  = add_par $
      hang (char '\\' <+> fsep (pprBndr LambdaBind fstBndr :
                                map (\(a, b) -> parens (sep [ppr a <> comma, pprBndr LambdaBind b])) annBndrs ++
                                [char '|', parens (sep [ppr k <> comma, ppr_kont_bndr ty])]) <+> arrow)
        2 (pprDeeper $ ppr comm)
  | otherwise
  = add_par $
      hang (char '\\' <+> fsep (pprBndr LambdaBind fstBndr :
                                map (\(a, b) -> parens (sep [ppr a <> comma, pprBndr LambdaBind b])) annBndrs) <+> arrow)
        2 (pprDeeper $ ppr body)
  where
    ((_, fstBndr) : annBndrs, body) = collectAnnBindersWithAnns (undefined, term)
ppr_term add_par (AnnCompute ty comm)
  = add_par $
      hang (text "compute" <+> parens (ppr_kont_bndr ty))
        2 (ppr comm)

ppr_kont_frames :: (OutputableBndr b, Outputable a) => [AnnFrame b a] -> [SDoc]
ppr_kont_frames = map ppr

ppr_frame :: (OutputableBndr b, Outputable a) => AnnFrame' b a -> SDoc
ppr_frame (AnnApp (_, AnnType ty))
  = char '@' <+> ppr ty
ppr_frame (AnnApp v)
  = char '$' <+> pprDeeper (ppr v)
ppr_frame (AnnCast co)
  = text "cast" <+> pprDeeper (ppr co)
ppr_frame (AnnTick _)
  = text "tick" <+> text "..."

ppr_end :: (OutputableBndr b, Outputable a) => AnnEnd' b a -> SDoc
ppr_end AnnReturn
  = text "ret"
ppr_end (AnnCase var alts)
  = hang (text "case as" <+> pprBndr LetBind var <+> text "of") 2 $ pprDeeper $
      vcat $ ppr_block (char '{') (char ';') (char '}') (map ppr alts)

ppr_join :: (OutputableBndr b, Outputable a) => (SDoc -> SDoc) -> AnnJoin' b a -> SDoc
ppr_join add_par (AnnJoin bndrs body)
  = add_par $
      hang (char '\\' <+> argTuple <+> arrow)
        2 (ppr body)
  where
    argTuple
      = case bndrs of
          [bndr] -> pprBndr LambdaBind bndr
          _      -> parens (pprWithCommas (pprBndr LambdaBind) bndrs)

ppr_kont_bndr :: Type -> SDoc
ppr_kont_bndr ty =
  text "ret" <+> dcolon <+> ppr ty

ppr_alt :: (OutputableBndr b, Outputable a) => AnnAlt' b a -> SDoc
ppr_alt (AnnAlt con args rhs)
 = hang (ppr_case_pat con args <+> arrow) 2 (ppr rhs)

ppr_case_pat :: OutputableBndr b => AltCon -> [b] -> SDoc
ppr_case_pat con args
  = ppr con <+> fsep (map ppr_bndr args)
  where
    ppr_bndr = pprBndr CaseBind

noParens :: SDoc -> SDoc
noParens pp = pp

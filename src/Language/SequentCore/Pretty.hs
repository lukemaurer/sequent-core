{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      : Language.SequentCore.Pretty
-- Description : Pretty printing of Sequent Core terms
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Instances and functions for pretty-printing Sequent Core terms using GHC's
-- built-in pretty printer.
  
module Language.SequentCore.Pretty (
  pprTopLevelBinds, pprParendTerm, pprCoreKont
) where

import Language.SequentCore.Syntax

import qualified GhcPlugins as GHC
import Outputable
import PprCore ()

import Data.List

ppr_bind :: OutputableBndr b => Bind b -> SDoc
ppr_bind (NonRec pair) = ppr_binding pair
ppr_bind (Rec binds)   = hang (text "rec") 2 (vcat $ intersperse space $
                                                ppr_block (char '{') (char ';') (char '}') (map ppr_binding binds))

ppr_binds_top :: OutputableBndr b => [Bind b] -> SDoc
ppr_binds_top binds = ppr_binds_with empty empty empty binds

-- | Print the given bindings as a sequence of top-level bindings.
pprTopLevelBinds :: OutputableBndr b => [Bind b] -> SDoc
pprTopLevelBinds = ppr_binds_top

ppr_block :: SDoc -> SDoc -> SDoc -> [SDoc] -> [SDoc]
ppr_block open _ close [] = [open <> close]
ppr_block open mid close (first : rest)
  = open <+> first : map (mid <+>) rest ++ [close]

ppr_binds :: OutputableBndr b => [Bind b] -> SDoc
ppr_binds binds = ppr_binds_with (char '{') (char ';') (char '}') binds

ppr_binds_with :: OutputableBndr b => SDoc -> SDoc -> SDoc -> [Bind b] -> SDoc
ppr_binds_with open mid close binds = vcat $ intersperse space $ ppr_block open mid close (map ppr_bind binds)

ppr_binding :: OutputableBndr b => BindPair b -> SDoc
ppr_binding pair
  = prefix <+> pprBndr LetBind val_bdr $$
    hang (ppr val_bdr <+> equals) 2 (pprDeeper $ body pair)
  where
    val_bdr = binderOfPair pair
    body (BindTerm _ term) = ppr term
    body (BindJoin _ join) = ppr join
    prefix | bindsJoin pair = text "join"
           | otherwise = empty

ppr_comm :: OutputableBndr b => (SDoc -> SDoc) -> Command b -> SDoc
ppr_comm add_par comm
  = maybe_add_par $ ppr_let <+> ppr_cut
  where
    (binds, cut) = flattenCommand comm
    ppr_let
      | null binds = empty
      | otherwise  = hang (text "let") 2 (ppr_binds binds) $$ text "in"
    maybe_add_par = if null binds then noParens else add_par
    ppr_cut
      = case cut of
          Left (term, fs, end) 
            -> sep [char '<' <> pprCoreTerm term,
                    cat $ ppr_block (char '|') (char ';') (char '>') $ (ppr_kont_frames fs ++ [ppr_end end])]
          Right (args, j)
            -> text "jump" <+> prefix <+> ppr j <+> parens (pprDeeper $ pprWithCommas pprCoreTerm args)
            where prefix | GHC.isTyVar j     = text "TYVAR"
                         | GHC.isCoVar j     = text "COVAR"
                         | not (isJoinId j)  = text "IDVAR"
                         | otherwise         = empty

ppr_term :: OutputableBndr b => (SDoc -> SDoc) -> Term b -> SDoc
ppr_term _ (Var name) = prefix <+> ppr name
  where prefix | GHC.isTyVar name = text "TYVAR"
               | isJoinId name = text "PKVAR"
               | otherwise = empty
  -- Something is quite wrong if it's a type variable!
ppr_term add_par (Type ty) = add_par $ text "TYPE" <+> ppr ty
ppr_term add_par (Coercion co) = add_par $ text "CO" <+> ppr co
ppr_term add_par (Lit lit) = GHC.pprLiteral add_par lit
ppr_term add_par term@(Lam {})
  | Compute ty comm <- body
  = add_par $
      hang (char '\\' <+> fsep (map (pprBndr LambdaBind) bndrs ++
                                [char '|', parens (ppr_kont_bndr ty)]) <+> arrow)
        2 (pprDeeper $ pprCoreComm comm)
  | otherwise
  = add_par $
      hang (char '\\' <+> fsep (map (pprBndr LambdaBind) bndrs) <+> arrow)
        2 (pprDeeper $ pprCoreTerm body)
  where
    (bndrs, body) = collectBinders term
ppr_term add_par (Compute ty comm)
  = add_par $
      hang (text "compute" <+> parens (ppr_kont_bndr ty))
        2 (pprCoreComm comm)

ppr_kont_frames :: OutputableBndr b => [Frame b] -> [SDoc]
ppr_kont_frames = map ppr_frame

ppr_frame :: OutputableBndr b => Frame b -> SDoc
ppr_frame (App (Type ty))
  = char '@' <+> ppr ty
ppr_frame (App v)
  = char '$' <+> pprDeeper (ppr_term noParens v)
ppr_frame (Cast co)
  = text "cast" <+> pprDeeper (ppr co)
ppr_frame (Tick _)
  = text "tick" <+> text "..."

ppr_end :: OutputableBndr b => End b -> SDoc
ppr_end Return
  = text "ret"
ppr_end (Case var alts)
  = hang (text "case as" <+> pprBndr LetBind var <+> text "of") 2 $ pprDeeper $
      vcat $ ppr_block (char '{') (char ';') (char '}') (map pprCoreAlt alts)

ppr_kont :: OutputableBndr b => (SDoc -> SDoc) -> Kont b -> SDoc
ppr_kont add_par (frames, end)
  = add_par $ sep $ punctuate semi (ppr_kont_frames frames ++ [ppr_end end])

ppr_join :: OutputableBndr b => (SDoc -> SDoc) -> Join b -> SDoc
ppr_join add_par (Join bndrs body)
  = add_par $
      hang (char '\\' <+> argTuple <+> arrow)
        2 (pprCoreComm body)
  where
    argTuple
      = case bndrs of
          [bndr] -> pprBndr LambdaBind bndr
          _      -> parens (pprWithCommas (pprBndr LambdaBind) bndrs)

ppr_kont_bndr :: GHC.Type -> SDoc
ppr_kont_bndr ty =
  text "ret" <+> dcolon <+> ppr ty

pprCoreAlt :: OutputableBndr b => Alt b -> SDoc
pprCoreAlt (Alt con args rhs)
 = hang (ppr_case_pat con args <+> arrow) 2 (pprCoreComm rhs)

ppr_case_pat :: OutputableBndr a => GHC.AltCon -> [a] -> SDoc
ppr_case_pat con args
  = ppr con <+> fsep (map ppr_bndr args)
  where
    ppr_bndr = pprBndr CaseBind

pprCoreComm :: OutputableBndr b => Command b -> SDoc
pprCoreComm comm = ppr_comm noParens comm

pprCoreTerm :: OutputableBndr b => Term b -> SDoc
pprCoreTerm val = ppr_term noParens val

pprCoreKont :: OutputableBndr b => Kont b -> SDoc
pprCoreKont kont = ppr_kont noParens kont

pprParendTerm :: OutputableBndr b => Term b -> SDoc
pprParendTerm term = ppr_term parens term

noParens :: SDoc -> SDoc
noParens pp = pp

instance OutputableBndr b => Outputable (Bind b) where
  ppr = ppr_bind

instance OutputableBndr b => Outputable (BindPair b) where
  ppr = ppr_binding

instance OutputableBndr b => Outputable (Term b) where
  ppr = ppr_term noParens

instance OutputableBndr b => Outputable (Command b) where
  ppr = ppr_comm noParens

instance OutputableBndr b => Outputable (Frame b) where
  ppr = ppr_frame

instance OutputableBndr b => Outputable (End b) where
  ppr = ppr_end

instance OutputableBndr b => Outputable (Join b) where
  ppr = ppr_join noParens

instance OutputableBndr b => Outputable (Alt b) where
  ppr = pprCoreAlt

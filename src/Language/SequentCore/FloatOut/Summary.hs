module Language.SequentCore.FloatOut.Summary (
  -- * Main entry
  summarizeProgram,

  -- * Summary data types
  Summary(..), BindSummary(..), VarUses, VarUseSummary(..), Skeleton(..),
  
  emptySumm, summFromFVs, unionSumm, unionSumms,
  
  -- * ASTs with summary annotations
  SummBndr, SummTerm, SummArg, SummFrame, SummEnd, SummCommand, SummJoin,
  SummBind, SummBindPair, SummAlt, SummKont, SummProgram,
  
  getSummary, getVarUses, getFreeVarsSumm, fvsFromSumm, lookupVarUses
) where
  
import Language.SequentCore.Annot
import Language.SequentCore.Syntax

import qualified CoreFVs
import CoreSyn  ( Tickish(..) )
import Coercion
import Id
import Maybes
import Outputable
import Type
import Util     ( count )
import Var
import VarEnv
import VarSet

import Control.Applicative ( (<$>) )
import Control.Exception   ( assert )

data Summary 
  = Summary { sm_varsUsed :: VarUses    -- All vars used in scope/expression and how
            , sm_skeleton :: Skeleton } -- Approximation used to calculate
                                        -- impact of lambda-lifting

data BindSummary
  = NoSummary           -- not let-bound
  | BindSummary Summary -- summary of scope (including RHS if recursive)

type VarUses = VarEnv (Var, VarUseSummary)
data VarUseSummary = VU { vu_unapplied :: !Bool
                        , vu_undersat  :: !Bool
                        , vu_saturated :: !Bool
                        , vu_oversat   :: !Bool }

data Skeleton -- an abstraction of a term or scope, retaining only information
              -- relevant to estimating lambda lifting's effect on the heap
              -- footprints of closures
  = NilSk
  | CloSk Id IdSet Skeleton
     -- a closure's free (non-sat) ids and its rhs
  | BothSk Skeleton Skeleton
  | LamSk !Bool Skeleton -- we treat oneshot lambdas specially
  | AltSk Skeleton Skeleton -- case alternatives

type SummBndr     = TaggedBndr BindSummary
type SummTerm     = AnnTerm     SummBndr Summary
type SummArg      = AnnArg      SummBndr Summary
type SummFrame    = AnnFrame    SummBndr Summary
type SummEnd      = AnnEnd      SummBndr Summary
type SummCommand  = AnnCommand  SummBndr Summary
type SummJoin     = AnnJoin     SummBndr Summary
type SummBindPair = AnnBindPair SummBndr Summary
type SummBind     = AnnBind     SummBndr Summary
type SummAlt      = AnnAlt      SummBndr Summary
type SummKont     = AnnKont     SummBndr Summary
type SummProgram  = AnnProgram  SummBndr Summary

getSummary :: (Summary, a) -> Summary
getSummary = fst

getVarUses :: (Summary, a) -> VarUses
getVarUses = sm_varsUsed . getSummary

getFreeVarsSumm :: (Summary, a) -> VarSet
getFreeVarsSumm = mapVarEnv fst . getVarUses

fvsFromSumm :: Summary -> VarSet
fvsFromSumm = mapVarEnv fst . sm_varsUsed

--------------------
-- Implementation --
--------------------

type TopVars = VarSet -- remember top-level vars to avoid counting them as free

summarizeProgram :: SeqCoreProgram -> SummProgram
summarizeProgram pgm = map (summTopBind tops) pgm
  where
    tops = mkVarSet (bindersOfBinds pgm)

summTopBind :: TopVars -> SeqCoreBind -> SummBind
summTopBind tops bind
  -- We don't need summaries of the scopes of top-level bindings, so just leave
  -- them empty
  = case bind of
      NonRec pair -> (emptySumm, AnnNonRec (doPair pair))
      Rec pairs   -> (emptySumm, AnnRec    (doPair <$> pairs))
  where
    doPair (BindTerm bndr term)
      = (emptySumm, AnnBindTerm (TB bndr NoSummary) (summRhsTerm tops term))
    doPair pair@(BindJoin {})
      = pprPanic "summTopBind" (text "Top-level join" $$ ppr pair)

summBindPair :: TopVars
             -> Summary -- Summary of scope
             -> SeqCoreBindPair -> SummBindPair
-- Note that, if this port of a recursive binding, the summary covers the RHS,
-- so we're tying the knot
summBindPair tops scopeSumm (BindTerm bndr rhs)
  = (summ', AnnBindTerm (TB bndr (BindSummary scopeSumm)) rhs')
  where
    rhs'  = summRhsTerm tops rhs
    summ  = getSummary rhs'
    skel  = sm_skeleton summ
    skel' | isId bndr = cloSk bndr (getFreeVarsSumm rhs') skel
          | otherwise = assert (isNilSk skel) nilSk
    summ' = (summ `unionSumm` bndrSumm tops bndr) { sm_skeleton = skel' }
summBindPair tops scopeSumm (BindJoin bndr rhs)
  = (summ', AnnBindJoin (TB bndr (BindSummary scopeSumm)) rhs')
  where
    rhs'  = summJoin tops rhs
    summ  = getSummary rhs'
    summ' = summ `unionSumm` bndrSumm tops bndr
              -- No need to update skeleton because no closure is created

summJoin :: TopVars -> SeqCoreJoin -> SummJoin
summJoin tops (Join bndrs comm)
  = case summCommand tops comm of
      comm'@(summ, _) -> (summ', AnnJoin bndrs' comm')
        where
          bndrs' = [TB bndr NoSummary | bndr <- bndrs]
          summ'  = bndrs `delBindersSumm` summ

summRhsTerm :: TopVars -> SeqCoreTerm -> SummTerm
summRhsTerm tops term = summTerm tops term 0

summTerm :: TopVars
         -> SeqCoreTerm
         -> Int -- Number of value arguments
         -> SummTerm
summTerm _    (Lit lit)     _ = (emptySumm, AnnLit lit)
summTerm _    (Type ty)     _ = (summFromFVs (tyVarsOfType ty), AnnType ty)
summTerm _    (Coercion co) _ = (summFromFVs (coVarsOfCo co), AnnCoercion co)
summTerm tops (Var id)      n = (varSumm tops id n, AnnVar id)

summTerm tops (Lam bndr body) _
  = (summ', AnnLam (TB bndr NoSummary) body')
  where
    body' = summRhsTerm tops body
    summ  = getSummary body'
    skel  = lamSk (isOneShotBndr bndr) (sm_skeleton summ)
    summ' = bndr `delBinderSumm` summ { sm_skeleton = skel }

summTerm tops (Compute ty comm) _
  = (getSummary comm', AnnCompute ty comm')
  where
    comm' = summCommand tops comm

summCommand :: TopVars -> SeqCoreCommand -> SummCommand
summCommand tops (Let (NonRec pair) body)
  = (summ, AnnLet (bindSumm, AnnNonRec pair') body')
  where
    body'     = summCommand tops body
    bodySumm  = getSummary body'
    scopeSumm = bodySumm -- binder scopes over the body only
    pair'     = summBindPair tops scopeSumm pair
    bindSumm  = getSummary pair'
    bndr      = binderOfPair pair
    summ      = bindSumm `unionSumm` (bndr `delBinderSumm` scopeSumm)
summCommand tops (Let (Rec pairs) body)
  = (summ, AnnLet (bindSumm, AnnRec pairs') body')
  where
    body'     = summCommand tops body
    bodySumm  = getSummary body'
    scopeSumm = bodySumm `unionSumm` bindSumm -- binder scopes over bind and body
    pairs'    = map (summBindPair tops scopeSumm) pairs
    bindSumm  = bndrs `delBindersSumm` unionSumms (map getSummary pairs')
                  -- knotted with scopeSumm
    bndrs     = map binderOfPair pairs
    summ      = bndrs `delBindersSumm` scopeSumm
summCommand tops (Eval term frames end)
  = (summ', AnnEval term' frames' end')
  where
    term'   = summTerm tops term (count isValueAppFrame frames)
    frames' = map (summFrame tops) frames
    end'    = summEnd tops end
    
    termSumm  = getSummary term'
    frameSumm = unionSumms (map getSummary frames')
    endSumm   = getSummary end'
    summ'     = termSumm `unionSumm` frameSumm `unionSumm` endSumm
summCommand tops (Jump args j)
  = (summ', AnnJump args' j)
  where
    args' = map (summRhsTerm tops) args
    summ' = varSumm tops j (length (filter isValueArg args)) `unionSumm` unionSumms (map getSummary args')

summFrame :: TopVars -> SeqCoreFrame -> SummFrame
summFrame tops (App arg) = (getSummary arg', AnnApp arg')
  where
    arg' = summRhsTerm tops arg
summFrame _    (Cast co) = (summFromFVs (coVarsOfCo co), AnnCast co)
summFrame _    (Tick ti) = (summ, AnnTick ti)
  where
    summ | Breakpoint _ ids <- ti = summFromFVs (mkVarSet ids)
         | otherwise              = emptySumm

summEnd :: TopVars -> SeqCoreEnd -> SummEnd
summEnd _    Return = (emptySumm, AnnReturn)
summEnd tops (Case bndr alts)
  = (summ', AnnCase (TB bndr NoSummary) alts')
  where
    alts' = map (summAlt tops) alts
    summs = map getSummary alts'
    summ' = bndr `delBinderSumm` unionAltSumms summs

summAlt :: TopVars -> SeqCoreAlt -> SummAlt
summAlt tops (Alt con bndrs rhs)
  = (bndrs `delBindersSumm` getSummary rhs', AnnAlt con bndrs' rhs')
  where
    rhs'   = summCommand tops rhs
    bndrs' = [ TB bndr NoSummary | bndr <- bndrs ]

---------------
-- Summaries --
---------------

emptySumm :: Summary
emptySumm = Summary { sm_varsUsed = noFVs, sm_skeleton = nilSk }

unionSumm :: Summary -> Summary -> Summary
unionSumm (Summary { sm_varsUsed = vu1, sm_skeleton = sk1 })
          (Summary { sm_varsUsed = vu2, sm_skeleton = sk2 })
  = Summary { sm_varsUsed = vu1 `unionVUs` vu2
            , sm_skeleton = sk1 `bothSk`   sk2 }

unionAltSumm :: Summary -> Summary -> Summary
unionAltSumm (Summary { sm_varsUsed = vu1, sm_skeleton = sk1 })
             (Summary { sm_varsUsed = vu2, sm_skeleton = sk2 })
  = Summary { sm_varsUsed = vu1 `unionVUs` vu2
            , sm_skeleton = sk1 `altSk` sk2 }

unionSumms :: [Summary] -> Summary
unionSumms = foldr unionSumm emptySumm

unionAltSumms :: [Summary] -> Summary
unionAltSumms = foldr unionAltSumm emptySumm

summFromFVs :: VarSet -> Summary
summFromFVs fvs = Summary { sm_varsUsed = tagVarSet fvs, sm_skeleton = nilSk }

-- | Free variables from type, rules, and unfolding
bndrSumm :: TopVars -> Var -> Summary
  -- We just get free variables, not usage data, from the rules and unfolding.
  -- The unfolding should be redundant and the rules don't matter much for
  -- non-top-level functions.
bndrSumm tops var | isId var  = summFromFVs (filterVarSet notTop
                                              (CoreFVs.idFreeVars var))
                  | otherwise = summFromFVs (CoreFVs.varTypeTyVars var)
  where
    notTop v = not (v `elemVarSet` tops)

varSumm :: TopVars -> Var -> Int -> Summary
varSumm tops var nValArgs
  | isLocalVar var, not (var `elemVarSet` tops)
  = emptySumm { sm_varsUsed = aFreeVar var nValArgs }
  | otherwise
  = emptySumm

delBinderSumm :: Var -> Summary -> Summary
delBinderSumm var summ = summ { sm_varsUsed = var `delBinderVU` sm_varsUsed summ }

delBindersSumm :: [Var] -> Summary -> Summary
delBindersSumm vars summ = foldr delBinderSumm summ vars

-------------------
-- Variable uses --
-------------------

unusedSummary, unappSummary, unsatSummary, satSummary, oversatSummary
  :: VarUseSummary
unusedSummary  = VU False False False False
unappSummary   = VU True  False False False
unsatSummary   = VU False True  False False
satSummary     = VU False False True  False
oversatSummary = VU False False False True

noFVs :: VarUses
noFVs = emptyVarEnv

aFreeVar :: Var -> Int -> VarUses
aFreeVar var nValArgs = unitVarEnv var (var, use)
  where
    use | nValArgs == 0
        , not (isJoinId var)
        = unappSummary
        | otherwise
        = case nValArgs `compare` arity of
            LT          -> unsatSummary
            EQ          -> satSummary
            GT          -> oversatSummary
        
    arity = idArity var

combineVU :: VarUseSummary -> VarUseSummary -> VarUseSummary
combineVU (VU z1 l1 e1 g1) (VU z2 l2 e2 g2)
  = VU (z1 || z2) (l1 || l2) (e1 || e2) (g1 || g2) 

unionVUs :: VarUses -> VarUses -> VarUses
unionVUs = plusVarEnv_C combine
  where
    combine (var, u1) (var', u2) = assert (var == var') $
                                   (var, u1 `combineVU` u2)

delBinderVU :: Var -> VarUses -> VarUses
delBinderVU b s = (s `delVarEnv` b) `unionVUs` tagVarSet (tyVarsOfType (varType b))
  -- See commant in CoreFVs on adding type variables

tagVarSet :: VarSet -> VarUses
-- For tyvars, etc.
tagVarSet = mapVarEnv (\var -> (var, unusedSummary))
              -- note that VarSet = VarEnv Var

lookupVarUses :: VarUses -> Var -> VarUseSummary
lookupVarUses uses var = (snd <$> lookupVarEnv uses var) `orElse` unusedSummary

---------------
-- Skeletons --
---------------

nilSk :: Skeleton
nilSk = NilSk

isNilSk :: Skeleton -> Bool
isNilSk NilSk = True
isNilSk _     = False

cloSk :: Var -> VarSet -> Skeleton -> Skeleton
cloSk var fvs sk | isId var  = CloSk var fvs sk
                 | otherwise = assert (isEmptyVarSet fvs && isNilSk sk)
                               NilSk

bothSk :: Skeleton -> Skeleton -> Skeleton
bothSk NilSk r = r
bothSk l NilSk = l
bothSk l r = BothSk l r

lamSk :: Bool -> Skeleton -> Skeleton
lamSk oneshot sk = case sk of
  NilSk -> sk
  LamSk oneshot' sk' | oneshot && oneshot' -> sk
                     | otherwise -> LamSk False sk'
  _ -> LamSk oneshot sk

altSk :: Skeleton -> Skeleton -> Skeleton
altSk NilSk r = r
altSk l NilSk = l
altSk l r = AltSk l r

----------
instance Outputable BindSummary where
  ppr NoSummary = text "n/a"
  ppr (BindSummary summ) = ppr summ

instance Outputable VarUseSummary where
  ppr (VU z l e g) = hcat [flag z '0', flag l '<', flag e '=', flag g '>']
    where
      flag b c = ppWhen b (char c)

instance Outputable Summary where
  ppr (Summary { sm_varsUsed = vu, sm_skeleton = sk })
    = sep [usesPart, skelPart]
    where
      usesPart = text "Uses:" <+> brackets (pprWithCommas pprEntry (varEnvElts vu))
      skelPart = text "Skel:" <+> if isNilSk sk then text "(empty)" else ppr sk
      
      pprEntry (var, uses) = ppr var <+> ppr uses

instance Outputable Skeleton where
  ppr NilSk = text ""
  ppr (CloSk id ids sk) = hang (nm <+> ppr (varSetElems ids)) 2 (parens $ ppr sk)
    where nm = text "CLO" <+> ppr id
  ppr (BothSk sk1 sk2) = ppr sk1 $$ ppr sk2
  ppr (LamSk oneshot sk) = char '\\' <> (if oneshot then char '1' else empty) <+> ppr sk
  ppr (AltSk sk1 sk2) = vcat [ text "{ " <+> ppr sk1
                             , text "ALT"
                             , text "  " <+> ppr sk2
                             , text "}" ]

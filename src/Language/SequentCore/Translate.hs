{-# LANGUAGE TupleSections, MultiWayIf, LambdaCase, CPP #-}

-- | 
-- Module      : Language.SequentCore.Translate
-- Description : Core \<-\> Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Translation between Sequent Core and native GHC Core.

module Language.SequentCore.Translate (
  -- $txn
  fromCoreModule, termFromCoreExpr,
  bindsToCore,
  commandToCoreExpr, termToCoreExpr, joinToCoreExpr, joinToCoreExpr', joinIdToCore,
  CoreContext, kontToCoreExpr,
  onCoreExpr, onSequentCoreTerm
) where

import {-# SOURCE #-} Language.SequentCore.Contify
import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import BasicTypes ( RecFlag(..), isNonRec )
import qualified CoreSyn as Core
import qualified CoreUtils as Core
import Id
import IdInfo
import Maybes
import qualified MkCore as Core
import MkId
import Outputable  hiding ( (<>) )
import Type        hiding ( substTy )
import TysPrim
import Util       ( lengthExceeds )

-- $txn
-- The translations to and from Sequent Core are /not/ guaranteed to be perfect
-- inverses. However, any differences between @e@ and @commandToCoreExpr
-- (fromCoreExpr e)@ should be operationally insignificant, such as a @let@
-- floating out from a function being applied. A more precise characterization
-- of the indended invariants of these functions would entail some sort of
-- /bisimulation/, but it should suffice to know that the translations are
-- "faithful enough."

------------------------------------------------
-- Public interface for Core --> Sequent Core --
------------------------------------------------

-- | Translates a list of Core bindings into Sequent Core.
fromCoreModule :: [Core.CoreBind] -> [SeqCoreBind]
fromCoreModule = runContify . fromCoreTopLevelBinds

-- | Translates a single Core expression as a Sequent Core term.
termFromCoreExpr :: Core.CoreExpr -> SeqCoreTerm
termFromCoreExpr = contifyInTerm . fromCoreExprAsTerm

fromCoreExpr :: Core.CoreExpr -> SeqCoreKont -> SeqCoreCommand
fromCoreExpr expr (fs, end) = go [] expr fs end
  where
    go :: [SeqCoreBind] -> Core.CoreExpr
       -> [SeqCoreFrame] -> SeqCoreEnd -> SeqCoreCommand
    go binds expr fs end = case expr of
      Core.Var x         -> goApp x []
      Core.Lit l         -> done $ Lit l
      Core.App {}         | (Core.Var x, args) <- Core.collectArgs expr
                         -> goApp x args
      Core.App e1 e2     ->
        let e2' = fromCoreExprAsTerm e2
        in go binds e1 (App e2' : fs) end
      Core.Lam x e       -> done $ fromCoreLams x e
      Core.Let bs e      ->
        let bs' = fromCoreBind bs
            ty = Core.exprType e
        in case (fs, end) of
             ([], Return) -> go (bs' : binds) e fs end
             _            -> done $ Compute ty (Let bs' (
                               fromCoreExpr e ([], Return)))
                               -- wrap let-binding in continuation
      Core.Case e x retTy as
        -- Copy the continuation into the branches if safe.
        | copy_kont -> go binds e [] copying_end
        -- Otherwise be more careful. In the simplifier, we get clever and
        -- split the continuation into a duplicable part and a non-duplicable
        -- part (see mkDupableKont); for now just share the whole thing by
        -- translating e with the empty continuation and wrapping around it.
        | otherwise -> done inner_term
        where
          copy_kont | isTrivialKont (fs, end)    = True  -- copy trivial
                    | not (as `lengthExceeds` 1) = True  -- "copy" into < 2 branches
                    | otherwise                  = False -- would duplicate code

          copying_end = Case x $ map (fromCoreAlt (fs, end)) as

          inner_term = Compute retTy $ fromCoreExpr e ([], joined_end)
          joined_end = Case x $ map (fromCoreAlt ([], Return)) as
      Core.Coercion co   -> done $ Coercion co
      Core.Cast e co     -> go binds e (Cast co : fs) end
      Core.Tick ti e     -> go binds e (Tick ti : fs) end
      Core.Type t        -> done $ Type t
      where
        done term = addLets (reverse binds) $ Eval term fs end
        
        goApp x args = doneEval (Var x) (map App args' ++ fs) end
          where
            args' = map fromCoreExprAsTerm args
            
            doneEval v fs e = addLets (reverse binds) $ Eval v fs e

fromCoreLams :: Var -> Core.CoreExpr -> SeqCoreTerm
fromCoreLams x expr
  = mkLambdas (x : xs) body'
  where
    (xs, body) = Core.collectBinders expr
    bodyComm   = fromCoreExpr body ([], Return)
    body'      = mkCompute (Core.exprType body) bodyComm

fromCoreExprAsTerm :: Core.CoreExpr -> SeqCoreTerm
fromCoreExprAsTerm expr
  = mkCompute ty body
  where
    body = fromCoreExpr expr ([], Return)
    ty = Core.exprType expr

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: SeqCoreKont -> Core.CoreAlt -> SeqCoreAlt
fromCoreAlt kont (ac, bs, e)
  = Alt ac bs $ fromCoreExpr e kont

fromCoreBind :: Core.CoreBind -> SeqCoreBind
fromCoreBind bind =
  case bind of
    Core.NonRec x rhs -> NonRec $ fromCoreBindPair x rhs
    Core.Rec pairs -> Rec $ map (uncurry fromCoreBindPair) pairs

fromCoreBindPair :: Var -> Core.CoreExpr -> SeqCoreBindPair
fromCoreBindPair x rhs = BindTerm x $ fromCoreExprAsTerm rhs

fromCoreTopLevelBinds :: [Core.CoreBind] -> [SeqCoreBind]
fromCoreTopLevelBinds = map fromCoreBind

------------------------------------------------
-- Public interface for Sequent Core --> Core --
------------------------------------------------
    
-- | Translates a command into Core.
commandToCoreExpr :: Type -> SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr retTy comm
  = case comm of
      Let bind comm'   -> Core.mkCoreLet (bindToCore (Just retTy) bind)
                                         (commandToCoreExpr retTy comm')
      Eval term fs end -> kontToCoreExpr retTy (fs, end) (termToCoreExpr term)
      Jump args j      -> Core.mkCoreApps (Core.Var (joinIdToCore retTy j))
                                          (map termToCoreExpr args ++ extraArgs)
        where
          extraArgs | all isTypeArg args = [ Core.Var voidPrimId ]
                    | otherwise          = []

-- | Translates a term into Core.
termToCoreExpr :: SeqCoreTerm -> Core.CoreExpr
termToCoreExpr val =
  case val of
    Lit l        -> Core.Lit l
    Var x        -> Core.Var x
    Lam x t      -> Core.Lam x (termToCoreExpr t)
    Type t       -> Core.Type t
    Coercion co  -> Core.Coercion co
    Compute kb c -> commandToCoreExpr kb c

-- | Translates a join point into Core. Does not change any one-shot flags. 
joinToCoreExpr :: Type -> SeqCoreJoin -> Core.CoreExpr
joinToCoreExpr = joinToCoreExpr' Recursive

-- | Translates a join point into Core. If the flag is NonRecursive, the
-- one-shot flags will be set on all value binders.
joinToCoreExpr' :: RecFlag -> Type -> SeqCoreJoin -> Core.CoreExpr
joinToCoreExpr' recFlag retTy (Join xs comm)
  = Core.mkCoreLams (maybeOneShots xs') (commandToCoreExpr retTy comm)
  where
    xs'   | null xs   = [ voidArgId ]
          | otherwise = xs
    maybeOneShots xs | isNonRec recFlag = map setOneShotLambdaIfId xs
                     | otherwise        = xs
    setOneShotLambdaIfId x | isId x = setOneShotLambda x
                           | otherwise = x

-- | Functional representation of expression contexts in Core.
type CoreContext = Core.CoreExpr -> Core.CoreExpr

-- | Translates a continuation into a function that will wrap a Core expression
-- with a fragment of context (an argument to apply to, a case expression to
-- run, etc.).
kontToCoreExpr :: Type -> SeqCoreKont -> CoreContext
kontToCoreExpr retTy (fs, end) =
  foldr (flip (.)) (endToCoreExpr retTy end) (map frameToCoreExpr fs)

frameToCoreExpr :: SeqCoreFrame -> CoreContext
frameToCoreExpr k =
  case k of
    App  {- expr -} v   -> \e -> Core.mkCoreApp e (termToCoreExpr v)
    Cast {- expr -} co  -> \e -> Core.Cast e co
    Tick ti {- expr -}  -> \e -> Core.Tick ti e

endToCoreExpr :: Type -> SeqCoreEnd -> CoreContext
endToCoreExpr retTy k =
  case k of
    Case {- expr -} b as -> \e -> Core.Case e b retTy (map (altToCore retTy) as)
    Return               -> \e -> e

-- | Convert a join id to its Core form. For instance, given a return type of 
--   String,
--     @j :: Cont# (exists# a. (# a, Int, Char #))
--   becomes
--     @j :: forall a. a -> Int -> Char -> String
joinIdToCore :: Type -> JoinId -> Id
joinIdToCore retTy j = maybeAddArity $ j `setIdType` kontTyToCoreTy argTy retTy
  where
    argTy = isKontTy_maybe (idType j) `orElse` pprPanic "joinIdToCore" (pprBndr LetBind j)
    maybeAddArity j' | idArity j' == 0 = j' `setIdInfo` (idInfo j' `setArityInfo` 1)
                     | otherwise       = j'

kontTyToCoreTy :: Type -> Type -> Type
kontTyToCoreTy ty retTy
  | Just (a, body) <- isUbxExistsTy_maybe ty
  = mkForAllTy a (kontTyToCoreTy body retTy)
  | isUnboxedTupleType ty
  = let (_, args) = splitTyConApp ty
    in if | null args -> mkFunTy voidPrimTy retTy
          | Just (a, ty') <- isUbxExistsTy_maybe (last args)
                      -> mkFunTys (init args) 
                                  (mkForAllTy a (kontTyToCoreTy ty' retTy))
          | otherwise -> mkFunTys args retTy
  | otherwise
  = pprPanic "kontArgsTyToCoreTy" (ppr ty)

-- | Translates a binding into Core.
bindToCore :: Maybe Type -> SeqCoreBind -> Core.CoreBind
bindToCore retTy_maybe bind =
  case bind of
    NonRec pair -> Core.NonRec b v
      where (b, v) = bindPairToCore retTy_maybe NonRecursive pair
    Rec pairs   -> Core.Rec (map (bindPairToCore retTy_maybe Recursive) pairs)

bindPairToCore :: Maybe Type -> RecFlag -> SeqCoreBindPair
               -> (Core.CoreBndr, Core.CoreExpr)
bindPairToCore retTy_maybe recFlag pair =
  case pair of
    BindTerm b v -> (b, termToCoreExpr v)
    BindJoin b pk -> (joinIdToCore retTy b, joinToCoreExpr' recFlag retTy pk)
      where
        retTy = retTy_maybe `orElse` panic "bindPairToCore: top-level cont"

-- | Translates a list of top-level bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore binds = map (bindToCore Nothing) binds

altToCore :: Type -> SeqCoreAlt -> Core.CoreAlt
altToCore retTy (Alt ac bs c) = (ac, bs, commandToCoreExpr retTy c)

--------------------------------------------------------------
-- Public interface for operations going in both directions --
--------------------------------------------------------------

-- | Take an operation on Sequent Core terms and perform it on Core expressions
onCoreExpr :: (SeqCoreTerm -> SeqCoreTerm) -> (Core.CoreExpr -> Core.CoreExpr)
onCoreExpr f = termToCoreExpr . f . termFromCoreExpr

-- | Take an operation on Core expressions and perform it on Sequent Core terms
onSequentCoreTerm :: (Core.CoreExpr -> Core.CoreExpr) -> (SeqCoreTerm -> SeqCoreTerm)
onSequentCoreTerm f = termFromCoreExpr . f . termToCoreExpr

module Language.SequentCore.WiredIn (
  contKindTyCon, contTyCon, contFunTyCon,
  
  contKind, mkContTy, isContTy, isContTy_maybe,
  mkContFunTy, isContFunTy, splitContFunTy_maybe,
  sequentCoreTag, sequentCoreWiredInTag,
  
  mkLamContId, mkLetContId, mkArgContId, mkContArgId
) where

import FastString
import Id
import Kind
import Name
import PrelNames
import TyCon
import Type
import TypeRep     ( Type(TyConApp) ) -- for seeing type synonyms
import TysPrim
import Unique

sequentCoreTag, sequentCoreWiredInTag :: Char
-- Must be different from any other unique tag!! See the Unique module
sequentCoreTag        = 'Q'
sequentCoreWiredInTag = 'q'

contKindKey, contTypeKey, contFunTypeKey,
  lamContKey, argContKey, letContKey, contArgKey :: Unique
[ contKindKey, contTypeKey, contFunTypeKey,
  lamContKey, argContKey, letContKey, contArgKey ]
  = map (mkUnique sequentCoreWiredInTag) [1..7]

lamContName, argContName, letContName, contArgName :: Name
[lamContName, argContName, letContName, contArgName] =
  zipWith mkSystemVarName
    [lamContKey,    argContKey,    letContKey,    contArgKey]
    [fsLit "*lamk", fsLit "*argk", fsLit "*letk", fsLit "*karg"]

contKindTyConName, contTyConName, contFunTyConName :: Name
contKindTyConName = mkPrimTyConName (fsLit "ContKind") contKindKey    contKindTyCon
contTyConName     = mkPrimTyConName (fsLit "Cont#")    contTypeKey    contTyCon
contFunTyConName  = mkPrimTyConName (fsLit "ContFun")  contFunTypeKey contFunTyCon

mkLamContId, mkArgContId, mkLetContId :: Type -> Var
[mkLamContId, mkArgContId, mkLetContId]
  = map (\name ty -> mkLocalId name (mkContTy ty))
      [lamContName, argContName, letContName]

mkContArgId :: Type -> Id
mkContArgId ty = mkLocalId contArgName ty

contKindTyCon, contTyCon, contFunTyCon :: TyCon
contKindTyCon = mkKindTyCon contKindTyConName superKind

-- TODO VoidRep isn't really right, but does it matter? This type should never
-- appear in Core anyway.
contTyCon = mkPrimTyCon contTyConName (mkArrowKind openTypeKind contKind) [Representational] VoidRep

contFunTyCon = mkSynonymTyCon contFunTyConName kind vars roles rhs
  where
    kind = mkArrowKinds [openTypeKind, openTypeKind] liftedTypeKind
    vars = [openAlphaTyVar, openBetaTyVar]
    roles = [Representational, Representational]
    rhs = mkFunTy openAlphaTy openBetaTy

contKind :: Kind
contKind = mkTyConApp contKindTyCon []

mkContTy :: Type -> Type
mkContTy ty = mkTyConApp contTyCon [ty]

isContTy :: Type -> Bool
isContTy ty | Just (con, _) <- splitTyConApp_maybe ty
            = con == contTyCon
            | otherwise
            = False

isContTy_maybe :: Type -> Maybe Type
isContTy_maybe ty | Just (con, [arg]) <- splitTyConApp_maybe ty
                  , con == contTyCon
                  = Just arg
                  | otherwise
                  = Nothing

mkContFunTy :: Type -> Type -> Type
mkContFunTy inTy outTy = mkTyConApp contFunTyCon [inTy, outTy]

-- Note that we *don't* use splitTyConApp_maybe here because the whole point is
-- to check for a type synonym ...

isContFunTy :: Type -> Bool
isContFunTy (TyConApp con _) = con == contFunTyCon
isContFunTy _                = False

splitContFunTy_maybe :: Type -> Maybe (Type, Type)
splitContFunTy_maybe (TyConApp con [inTy, outTy]) | con == contFunTyCon
  = Just (inTy, outTy)
splitContFunTy_maybe _
  = Nothing
module Language.SequentCore.WiredIn (
  kontKindTyCon, kontTyCon, ubxExistsTyCon,
  
  mkKontKind, mkKontTy, mkUbxExistsTy,
  isKontKind, isKontKind_maybe, isKontTy, isKontTy_maybe,
  isUbxExistsTy, isUbxExistsTy_maybe,
  applyUbxExists, applyUbxExists_maybe, applysUbxExists_maybe,
  
  sequentCoreTag, sequentCoreWiredInTag,
  
  mkKontId, mkKontArgId, mkTranslatedJoinBinder
) where

import FastString
import Id
import Kind
import Maybes
import Name
import Outputable
import PrelNames
import TyCon
import Type
import TysPrim
import Unique

import Control.Monad

sequentCoreTag, sequentCoreWiredInTag :: Char
-- Must be different from any other unique tag!! See the Unique module
sequentCoreTag        = 'Q'
sequentCoreWiredInTag = 'q'

kontKindKey, kontTypeKey, ubxExistsTypeKey, kontIdKey, kontArgKey, translatedJoinBndrKey :: Unique
kontKindKey: kontTypeKey: ubxExistsTypeKey: kontIdKey: kontArgKey: translatedJoinBndrKey: _
  = map (mkUnique sequentCoreWiredInTag) [1..]

kontArgName, kontIdName, translatedJoinBinderName :: Name
[kontArgName, kontIdName, translatedJoinBinderName] = zipWith mkSystemVarName
  [kontArgKey,   kontIdKey,    translatedJoinBndrKey]
  [fsLit "karg", fsLit "*ret", fsLit "*tx"]

kontKindTyConName, kontTyConName, ubxExistsTyConName :: Name
kontKindTyConName     = mkPrimTyConName (fsLit "ContKind")     kontKindKey      kontKindTyCon
kontTyConName         = mkPrimTyConName (fsLit "Cont#")        kontTypeKey      kontTyCon
ubxExistsTyConName    = mkPrimTyConName (fsLit "Exists#")      ubxExistsTypeKey ubxExistsTyCon

mkKontArgId :: Type -> Id
mkKontArgId ty = mkLocalId kontArgName ty

mkKontId :: Type -> Var
mkKontId ty = mkLocalId kontIdName ty

mkTranslatedJoinBinder :: Type -> Var
mkTranslatedJoinBinder ty = mkLocalId translatedJoinBinderName ty

kontKindTyCon, kontTyCon, ubxExistsTyCon :: TyCon
kontKindTyCon = mkKindTyCon kontKindTyConName (superKind `mkArrowKind` superKind)

-- TODO VoidRep isn't really right, but does it matter? This type should never
-- appear in Core anyway.
kontTyCon = mkPrimTyCon kontTyConName kind roles VoidRep
  where
    kKi   = mkTyVarTy kKiVar
    kind  = mkPiTypes [kKiVar] (mkFunTy kKi (mkKontKind kKi))
    roles = [Representational, Representational]

-- TODO We might be able to finagle unboxed existentials by calling mkTupleTyCon
-- with a special DataCon
ubxExistsTyCon = mkPrimTyCon ubxExistsTyConName kind [Representational] VoidRep
  where
    kind  = openTypeKind `mkArrowKind` unliftedTypeKind

mkKontKind :: Kind -> Kind
mkKontKind kind = mkTyConApp kontKindTyCon [kind]

-- | Form the type of a continuation accepting a value of the given type.
mkKontTy :: Type -> Type
mkKontTy ty = mkTyConApp kontTyCon [typeKind ty, ty]

mkUbxExistsTy :: TyVar -> Type -> Type
mkUbxExistsTy a ty = mkTyConApp ubxExistsTyCon [mkForAllTy a ty]

isKontKind :: Kind -> Bool
isKontKind = isJust . isKontKind_maybe

isKontKind_maybe :: Kind -> Maybe Kind
isKontKind_maybe ki = do [arg] <- matchTyConApp ki kontKindTyCon
                         return arg

isKontTy, isUbxExistsTy :: Type -> Bool
isKontTy      = isJust . isKontTy_maybe
isUbxExistsTy = isJust . isUbxExistsTy_maybe

isKontTy_maybe :: Type -> Maybe Type
isKontTy_maybe ty = do [_, arg] <- matchTyConApp ty kontTyCon
                       return arg

isUbxExistsTy_maybe :: Type -> Maybe (TyVar, Type)
isUbxExistsTy_maybe ty = do [arg] <- matchTyConApp ty ubxExistsTyCon
                            splitForAllTy_maybe arg

applyUbxExists :: Type -> Type -> Type
applyUbxExists ty tyArg
  = applyUbxExists_maybe ty tyArg `orElse` pprPanic "applyUbxExists" (ppr ty <+> ppr tyArg)

applyUbxExists_maybe :: Type -> Type -> Maybe Type
applyUbxExists_maybe ty tyArg
  = do
    (a, body) <- isUbxExistsTy_maybe ty
    return $ substTyWith [a] [tyArg] body

applysUbxExists_maybe :: Type -> [Type] -> Maybe Type
applysUbxExists_maybe = foldM applyUbxExists_maybe
  
matchTyConApp :: Type -> TyCon -> Maybe [Type]
matchTyConApp ty con = do (con', args) <- splitTyConApp_maybe ty
                          guard (con == con')
                          return args

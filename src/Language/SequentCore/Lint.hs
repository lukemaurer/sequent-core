{-# LANGUAGE MultiWayIf #-}

-- | 
-- Module      : Language.SequentCore.Lint
-- Description : Type checker for Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Provides a sanity check for Sequent Core transformations in the tradition of
-- CoreLint.

module Language.SequentCore.Lint (
  lintCoreBindings, lintTerm, assertLintProgram
) where

import Language.SequentCore.Pretty
import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import Coercion     ( coercionKind, coercionType )
import Id
import Kind
import Literal
import Outputable
import Pair
import Type
import VarEnv

import Control.Monad
import Data.List

{-
Note [Scope of continuation variables]
--------------------------------------

Terms should always produce a unique result to their given continuation
(i.e. evaluation context). It would be unfortunate if evaluating a term caused
control flow to jump someplace else entirely instead of returning a
result. Maintaining a certain discipline on the scope of continuation variables
prevents unwanted, anamolous jumps of control flow outside of the return path of
a term. More specifically: a term cannot have any reference to a free
continuation variable.

In addition to checking types, we also ensure that terms do not depend on any
continuation variables in their scope. This scoping check is implemented in lint
by maintaining two separate environments: one for continuation variables only,
and another for all other variables. Continuations and commands are type checked
with respect to both environments. When it comes time for checking terms, the
environment of continuation variables is dropped entirely. Going the other way,
checking a compute term introduces a new continuation variable environment for
checking its underlying command, which contains only the continuation
environment introduced by the compute abstraction itself. This restriction means
that every command inside of a compute term *must* exit out of the continuation
it names.
-}

type LintM = Either SDoc
type TermEnv = TvSubst
type KontEnv = TvSubst
type LintEnv = (TermEnv, KontEnv, OutType)

type OutType = Type
type OutVar = Var

termEnv :: LintEnv -> TermEnv
termEnv (env, _enk, _retTy) = env

kontEnv :: LintEnv -> KontEnv
kontEnv (_env, enk, _retTy) = enk

retTy :: LintEnv -> OutType
retTy (_env, _enk, retTy) = retTy

mkLintEnv :: TermEnv -> KontEnv -> OutType -> LintEnv
mkLintEnv env enk ty = (env, enk, ty)

emptyTermEnv :: TermEnv
emptyTermEnv = emptyTvSubst

extendTermEnv :: TermEnv -> Var -> Term Var -> TermEnv
extendTermEnv ent bndr _term
  = extendTvInScope ent bndr -- FIXME Should substitute in type!

extendTermEnvList :: TermEnv -> [BindPair Var] -> TermEnv
extendTermEnvList ent pairs
  = foldr (\(BindTerm x rhs) ent -> extendTermEnv ent x rhs) ent pairs

extendLintEnv :: LintEnv -> BindPair Var -> LintEnv
extendLintEnv (ent, enk, retTy) (BindTerm bndr _term)
  = (extendTvInScope ent bndr, enk, retTy)
extendLintEnv (ent, enk, retTy) (BindJoin bndr _pk)
  = (ent, extendTvInScope enk bndr, retTy)

extendLintEnvList :: LintEnv -> [BindPair Var] -> LintEnv
extendLintEnvList = foldr (flip extendLintEnv)

mapTermLintEnv :: (TermEnv -> TermEnv) -> LintEnv -> LintEnv
mapTermLintEnv f env = mkLintEnv (f (termEnv env)) (kontEnv env) (retTy env)

eitherToMaybe :: Either a b -> Maybe a
eitherToMaybe (Left a)  = Just a
eitherToMaybe (Right _) = Nothing

lintCoreBindings :: [SeqCoreBind] -> Maybe SDoc
lintCoreBindings binds = eitherToMaybe $ foldM lintCoreTopBind initEnv binds
  where
    -- All top-level bindings are considered visible (see CoreLint.lintCoreBindings)
    initEnv = extendTermEnvList emptyTermEnv (flattenBinds binds)

assertLintProgram :: String -> SDoc -> [SeqCoreBind] -> [SeqCoreBind]
assertLintProgram msg extraDoc binds
  | not debugIsOn = binds
  | otherwise
  = case lintCoreBindings binds of
      Nothing   -> binds
      Just errs -> pprPanic msg (errs $$ pprTopLevelBinds binds $$ extraDoc)

lintTerm :: TvSubst -> SeqCoreTerm -> Maybe SDoc
lintTerm env term = eitherToMaybe $ lintCoreTerm env term 

lintCoreTopBind :: TermEnv -> SeqCoreBind -> LintM TermEnv
lintCoreTopBind ent (NonRec (BindTerm bndr rhs))
  = do
    termTy <- lintCoreTerm ent rhs
    bndr' <- lintBndr ent bndr
    checkRhsType bndr' (idType bndr') termTy
      -- Can't have top-level tyvars, so no need to substitute
    return $ extendTermEnv ent bndr' rhs
lintCoreTopBind ent (Rec pairs)
  | all bindsTerm pairs
  = do
    bndrs' <- mapM (lintBndr ent . binderOfPair) pairs
    let pairs' = zipWith setPairBinder pairs bndrs'
        ent'   = extendTermEnvList ent pairs
    forM_ pairs' $ \(BindTerm bndr rhs) -> do
      termTy <- lintCoreTerm ent' rhs
      checkRhsType bndr (idType bndr) termTy
        -- Can't have top-level tyvars, so no need to substitute
    return ent'
lintCoreTopBind _ bind
  = Left $ text "Continuation binding at top level:" <+> ppr bind

lintCoreBind :: LintEnv -> SeqCoreBind -> LintM LintEnv
lintCoreBind env (NonRec pair)
  = do
    bndr' <- lintBndr (termEnv env) (binderOfPair pair)
    let pair' = pair `setPairBinder` bndr'
    lintCoreBindPair env pair'
    return $ extendLintEnv env pair'
lintCoreBind env (Rec pairs)
  = do
    bndrs' <- mapM (lintBndr (termEnv env) . binderOfPair) pairs
    let pairs'  = zipWith setPairBinder pairs bndrs'
        env'    = extendLintEnvList env pairs'
    mapM_ (lintCoreBindPair env') pairs'
    return env'

lintBndr :: TermEnv -> SeqCoreBndr -> LintM OutVar
lintBndr ent bndr
  = do
    -- Could do more, but currently just checks for free tyvars
    bndrTy <- lintType (text "binder:" <+> ppr bndr) ent (idType bndr)
    return $ bndr `setIdType` bndrTy

{-
Note [Checking terms vs. continuations]
---------------------------------------

Checking a term can be done straightforwardly: As usual, we check that it has a
consistent type, and return that type if so. But in the face of polymorphism, we
can't do the same with continuations. Consider:

  $ @ Int; $ 3; $ 4; ret p

What is this continuation's type? Supposing p has type Bool, the most general
type would be forall a. a -> a -> Bool, but it could also be forall a. Int -> a
-> Bool or forall a. Int -> a -> Bool or even conceivably forall a. Int -> Int
-> Bool. Fortunately, we always *expect* a continuation to have a particular
type: If it occurs in a command, it must have the same type as the term, and if
it's bound by a let, it must have the identifier's type.

Hence the asymmetry between lintCoreTerm and lintCoreKont, where the former
returns LintM Type and the latter takes an extra Type parameter but returns
LintM ().
-}

lintCoreBindPair :: LintEnv -> SeqCoreBindPair -> LintM ()
lintCoreBindPair env (BindTerm bndr term)
  = do
    termTy <- lintCoreTerm (termEnv env) term
    checkRhsType bndr (idType bndr) termTy
lintCoreBindPair env (BindJoin bndr (Join xs comm))
  = do
    lintKontBndrTypes (termEnv env) bndr xs
    let (ent, _) = mapAccumL lintBindInTermEnv (termEnv env) xs
    lintCoreCommand (mkLintEnv ent (kontEnv env) (retTy env)) comm

lintKontBndrTypes :: TermEnv -> SeqCoreBndr -> [SeqCoreBndr] -> LintM ()
lintKontBndrTypes env bndr argBndrs
  = do
    bndrTy <- kontIdTyOrError env bndr
    go bndrTy argBndrs
  where
    go ty bndrs
      | isUbxExistsTy ty
      = case bndrs of
          [] -> Left $ text "not enough binders for existential:" <+> pprBndr LetBind bndr
                    $$ text "binders:" <+> sep (map (pprBndr LambdaBind) argBndrs)
          bndr:bndrs' -> go (applyUbxExists ty (substTy env (mkTyVarTy bndr))) bndrs'
      | isUnboxedTupleType ty
      , Just (_, argTys) <- splitTyConApp_maybe ty
      = goTup argTys bndrs
      | otherwise
      = complain
    
    goTup []             []           = return ()
    goTup [lastArgTy]    bndrs        | isUbxExistsTy lastArgTy
                                      = go lastArgTy bndrs
    goTup (argTy:argTys) (bndr:bndrs) | argTy `eqType` substTy env (idType bndr)
                                      = goTup argTys bndrs
    goTup _              _            = complain
      
    complain  
      = Left $ text "wrong binder types for continuation binder:" <+> pprBndr LetBind bndr
            $$ text "binders:" <+> sep (map (pprBndr LambdaBind) argBndrs)

lintCoreTerm :: TermEnv -> SeqCoreTerm -> LintM OutType
lintCoreTerm env (Var x)
  | not (isLocalId x)
  = return (idType x)
  | Just x' <- lookupInScope (getTvInScope env) x
  = if | not (substTy env (idType x) `eqType` idType x') ->
           Left $ text "variable" <+> pprBndr LetBind x <+> text "bound as"
                                  <+> pprBndr LetBind x'
       | isDeadBinder x' ->
           Left $ text "occurrence of dead id" <+> pprBndr LetBind x'
       | otherwise -> return $ idType x'
  | otherwise
  = Left $ text "not found in context:" <+> pprBndr LetBind x

lintCoreTerm env (Lam x body)
  = do
    let (env', x') = lintBindInTermEnv env x
    retTy <- lintCoreTerm env' body
    return $ mkPiType x' retTy

lintCoreTerm env (Compute ty comm)
  = do
    let ty' = substTy env ty
    lintCoreCommand (mkLintEnv env emptyTvSubst ty') comm
    return ty'

lintCoreTerm _env (Lit lit)
  = return $ literalType lit

lintCoreTerm env (Type ty)
  = return $ typeKind (substTy env ty)

lintCoreTerm env (Coercion co)
  = return $ substTy env (coercionType co)

lintBindInTermEnv :: TermEnv -> Var -> (TermEnv, Var)
lintBindInTermEnv env x
  | isTyVar x
  = substTyVarBndr env x
  | otherwise
  = (env', x')
  where
    x' = substTyInId env x
    env' = extendTvInScope env x'

lintCoreCommand :: LintEnv -> SeqCoreCommand -> LintM ()
lintCoreCommand env (Let bind comm)
  = do
    env' <- lintCoreBind env bind
    lintCoreCommand env' comm
lintCoreCommand env (Eval term frames end)
  = lintCoreCut env term (frames, end)
lintCoreCommand env (Jump args j)
  = lintCoreJump env args j

lintCoreCut :: LintEnv -> SeqCoreTerm -> SeqCoreKont -> LintM ()
lintCoreCut env term kont
  = do
    ty <- lintCoreTerm (termEnv env) term
    lintCoreKont (text "in continuation of" <+> ppr term) env ty kont

lintCoreJump :: LintEnv -> [SeqCoreArg] -> JoinId -> LintM ()
lintCoreJump env args j
  | Just j' <- lookupInScope (getTvInScope (kontEnv env)) j
  = if | not (substTy (termEnv env) (idType j) `eqType` idType j') ->
           Left $ text "join variable" <+> pprBndr LetBind j <+> text "bound as"
                                       <+> pprBndr LetBind j'
       | isDeadBinder j' ->
           Left $ text "occurrence of dead id" <+> pprBndr LetBind j'
       | otherwise -> do
           ty <- kontIdTyOrError (kontEnv env) j
           go ty args
  | otherwise
  = Left $ text "not found in context:" <+> pprBndr LetBind j
  where
    topArgs = args
    
    go ty (Type argTy : args)
      = case applyUbxExists_maybe ty (substTy (termEnv env) argTy) of
          Just ty' -> go ty' args
          Nothing  -> mkError (text "type of polymorphic jump")
                              (text "existential type") (ppr ty)
    go ty args
      | isUnboxedTupleType ty
      , Just (_, argTys) <- splitTyConApp_maybe ty
      = goTup 1 argTys args
    go _ _
      = complain
      
    goTup _ [] [] = return ()
    goTup _ [ty] args@(Type _ : _)
      | isUbxExistsTy ty
      = go ty args
    goTup n (argTy:argTys) (arg:args)
      = do
        void $ checkingType (speakNth n <+> text "argument:" <+> ppr arg $$
                             text "of jump to:" <+> pprBndr LetBind j)
                            (substTy (termEnv env) argTy) $
          lintCoreTerm (termEnv env) arg
        goTup (n+1) argTys args
    goTup _ _ _
      = complain
    
    complain
      = Left $ text "bad parameterized continuation type in binder:" <+> pprBndr LetBind j
            $$ text "for args:" <+> ppr topArgs

lintCoreKont :: SDoc -> LintEnv -> OutType -> SeqCoreKont -> LintM ()
lintCoreKont desc env ty (frames, end)
  = do
    (env', ty') <- foldM (uncurry (lintCoreFrame desc)) (env, ty) frames
    lintCoreEnd desc env' ty' end

lintCoreFrame :: SDoc -> LintEnv -> OutType -> SeqCoreFrame -> LintM (LintEnv, OutType)
lintCoreFrame desc env ty (App (Type tyArg))
  | Just (tyVar, resTy) <- splitForAllTy_maybe ty
  = do
    let tyArg' = substTy (termEnv env) tyArg
    if typeKind tyArg' `isSubKind` idType tyVar
      then do
           let env' = mapTermLintEnv (\ent -> extendTvSubst ent tyVar tyArg') env
               resTy' = substTyWith [tyVar] [tyArg'] resTy
           return (env', resTy')
      else mkError (desc <> colon <+> text "type argument" <+> ppr tyArg)
             (ppr (typeKind tyArg')) (ppr (idType tyVar))
  | otherwise
  = Left $ desc <> colon <+> text "not a forall type:" <+> ppr ty
lintCoreFrame desc env ty (App arg)
  | Just (argTy, resTy) <- splitFunTy_maybe (substTy (termEnv env) ty)
  = do
    void $ checkingType (desc <> colon <+> ppr arg) argTy $ lintCoreTerm (termEnv env) arg
    return (env, resTy)
  | otherwise
  = Left $ desc <> colon <+> text "not a function type:" <+> ppr ty
lintCoreFrame desc env ty (Cast co)
  = do
    let Pair fromTy toTy = coercionKind co
        fromTy' = substTy (termEnv env) fromTy
        toTy'   = substTy (termEnv env) toTy
    void $ checkingType (desc <> colon <+> text "incoming type of" <+> ppr co) ty $ return fromTy'
    return (env, toTy')
lintCoreFrame _ env ty (Tick _)
  = return (env, ty)

lintCoreEnd :: SDoc -> LintEnv -> OutType -> SeqCoreEnd -> LintM ()
lintCoreEnd desc env ty Return
  = let expTy = retTy env
    in unless (expTy `eqType` ty) $
      mkError (desc <> colon <+> text "return type") (ppr expTy) (ppr ty)
lintCoreEnd desc env ty (Case bndr alts)
  = do
    let env' = mapTermLintEnv (\ent -> extendTvInScopeSubsted ent bndr) env
    forM_ alts $ \(Alt _ bndrs rhs) ->
      lintCoreCommand (mapTermLintEnv (\ent' -> extendTvInScopeListSubsted ent' bndrs) env') rhs
    void $ checkingType (desc <> colon <+> text "type of case binder" <+> ppr bndr) ty $
      return $ substTy (termEnv env) (idType bndr)

extendTvInScopeSubsted :: TvSubst -> Var -> TvSubst
extendTvInScopeSubsted tvs var
  = extendTvInScope tvs (substTyInId tvs var)

substTyInId :: TvSubst -> Var -> Var
substTyInId tvs var = var `setIdType` substTy tvs (idType var)

extendTvInScopeListSubsted :: TvSubst -> [Var] -> TvSubst
extendTvInScopeListSubsted tvs vars
  = foldr (flip extendTvInScopeSubsted) tvs vars

lintType :: SDoc -> TermEnv -> Type -> LintM OutType
lintType desc ent ty
  | null unknown
  = return ty'
  | otherwise
  = Left $ desc <> colon <+> text "type:" <+> ppr ty $$
           text "Type variable" <> plural unknown <+> text "not found in scope:" <+>
             pprWithCommas ppr unknown
  where
    ty'     = substTy ent ty
    known   = getInScopeVars (getTvInScope ent)
    unknown = varEnvElts $ tyVarsOfType ty' `minusVarEnv` known

mkError :: SDoc -> SDoc -> SDoc -> LintM a
mkError desc ex act = Left (desc $$ text "expected:" <+> ex
                                 $$ text "actual:" <+> act)
  
checkRhsType :: Var -> OutType -> OutType -> LintM ()
checkRhsType bndr bndrTy rhsTy
  = do unless (bndrTy `eqType` rhsTy) $
         mkError (text "type of RHS of" <+> ppr bndr) (ppr bndrTy) (ppr rhsTy)
       let bndrKi = typeKind bndrTy
       unless (isSubOpenTypeKind bndrKi) $
         mkError (text "kind of RHS of" <+> ppr bndr) (ppr openTypeKind) (ppr bndrKi)

checkingType :: SDoc -> OutType -> LintM OutType -> LintM OutType
checkingType desc ex go
  = do
    act <- go
    unless (ex `eqType` act) $ mkError desc (ppr ex) (ppr act)
    return act

kontIdTyOrError :: KontEnv -> JoinId -> LintM OutType
kontIdTyOrError env k
  = case isKontTy_maybe (substTy env (idType k)) of
      Just arg -> return arg
      _        -> Left (text "bad cont type:" <+> pprBndr LetBind k)

{-# LANGUAGE CPP #-}

module Language.SequentCore.LiftLambdas (liftLambdas, plugin) where

import Language.SequentCore.FVs
import Language.SequentCore.Plugin
import Language.SequentCore.Syntax
import Language.SequentCore.Syntax.Util

import CoreMonad
import qualified CoreSubst
import qualified CoreSyn as Core
import CoreUnfold
import Id
import IdInfo
import Maybes
import MkCore     ( sortQuantVars )
import OrdList
import Outputable
import Type
import Util       ( lengthExceeds )
import Var
import VarEnv
import VarSet

import Control.Applicative
import Control.Exception   ( assert )
import Control.Monad
import qualified Control.Monad.Trans.Reader   as Reader
import qualified Control.Monad.Trans.RWS.Lazy as RWS
import Data.Monoid

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = \_ todos -> do
    reinitializeGlobals
    return $ todos ++ [lambdaLiftPass]
} where
  lambdaLiftPass = CoreDoPluginPass "late-lambda-lift" (sequentPass runPass)

runPass :: SeqCoreProgram -> CoreM SeqCoreProgram
runPass binds = liftLambdas binds

tHRESHOLD :: Int
tHRESHOLD = 10

liftLambdas :: SeqCoreProgram -> CoreM SeqCoreProgram
liftLambdas binds
  = do
    -- Prep: Uniquify program, then add FV annotations
    let binds_ann = map withFreeVars (uniquifyProgram binds)
    -- Phase 1: Select variables to lift by annotating their binders
    let binds_with_decisions = decide binds_ann
    -- Phase 2: Perform selected lifts
    let binds_final = doLifts binds_with_decisions
    return binds_final

---------------------------
-- Phase 1: Select Lifts --
---------------------------

data Decision = NoLift | Lift LiftInfo

isLift :: Decision -> Bool
isLift (Lift _) = True
isLift NoLift   = False

newtype LiftInfo = LiftInfo { li_addedArgs :: [Var] }
data DecVar = DecVar { dv_var :: Var, dv_dec :: Decision }

decide :: SeqCoreProgramWithFVs -> Program DecVar
decide binds = runDecM initVarEnv (mapM doTopBind binds)
  where
    doTopBind (_, AnnNonRec pair)
      = NonRec <$> doTopPair pair
    doTopBind (_, AnnRec pairs)
      = Rec <$> mapM doTopPair pairs
    
    doTopPair (_, AnnBindJoin bndr _) = pprPanic "doTopPair" (ppr bndr)
    doTopPair (_, AnnBindTerm bndr term)
      = BindTerm (DecVar bndr NoLift) <$> decT term
    
    initVarEnv
      = mkVarEnv [(var, (var, topLevelLift)) | var <- bindersOfAnnBinds binds]
    
    topLevelLift = LiftInfo [] -- Pretend we're lifting top-level bindings
                               -- (see localFreeVarsAfterLifts)

type DecEnv = VarEnv (Var, LiftInfo)

type DecM = Reader.Reader DecEnv

runDecM :: DecEnv -> DecM a -> a
runDecM env m = Reader.runReader m env

underBinder :: DecVar -> DecM a -> DecM a
underBinder (DecVar _bndr NoLift)     m
  = m
underBinder (DecVar bndr (Lift info)) m
  = Reader.local (\env -> extendVarEnv env bndr (bndr, info)) m

underRecBinders :: [DecVar] -> DecM a -> DecM a
  -- INVARIANT: All are NoLift or none are
underRecBinders (DecVar _ NoLift : _) m 
  = m
underRecBinders bndrs m
  = Reader.local (\env -> extendVarEnvList env entries) m
  where
    entries = map (\(DecVar bndr (Lift info)) -> (bndr, (bndr, info))) bndrs

localFreeVarsAfterLifts :: VarSet -> DecM [Var]
localFreeVarsAfterLifts fvs
  = do
    env <- Reader.ask
    let afterLifts var = case lookupVarEnv env var of
                           Just (_, info) -> li_addedArgs info
                             -- If the var is lifted, its new parameters will be
                             -- free and it won't be local
                           Nothing        -> [var]
    return $ concatMap afterLifts (varSetElems fvs)

decT :: SeqCoreTermWithFVs -> DecM (Term DecVar)
decT (_, AnnLit lit)         = return $ Lit lit
decT (_, AnnVar id)          = return $ Var id
decT (_, AnnLam bndr body)   = Lam (DecVar bndr NoLift) <$> decT body
decT (_, AnnCompute ty comm) = Compute ty <$> decC comm
decT (_, AnnType ty)         = return $ Type ty
decT (_, AnnCoercion co)     = return $ Coercion co

decC :: SeqCoreCommandWithFVs -> DecM (Command DecVar)
decC (_, AnnLet bind comm)    = decB bind $ \bind' -> Let bind' <$> decC comm
decC (_, AnnEval term fs end) = Eval <$> decT term <*> mapM decF fs <*> decE end
decC (_, AnnJump args j)      = Jump <$> mapM decT args <*> pure j

decF :: SeqCoreFrameWithFVs -> DecM (Frame DecVar)
decF (_, AnnApp arg) = App <$> decT arg
decF (_, AnnCast co) = return $ Cast co
decF (_, AnnTick ti) = return $ Tick ti

decE :: SeqCoreEndWithFVs -> DecM (End DecVar)
decE (_, AnnReturn)         = return Return
decE (_, AnnCase bndr alts) = Case (DecVar bndr NoLift) <$> mapM decA alts

decA :: SeqCoreAltWithFVs -> DecM (Alt DecVar)
decA (_, AnnAlt con bndrs rhs) = Alt con [DecVar bndr NoLift | bndr <- bndrs] <$> decC rhs

decB :: SeqCoreBindWithFVs -> (Bind DecVar -> DecM a) -> DecM a
decB (_, AnnNonRec pair) k
  = do
    lifting <- shouldLift [] pair
    decVar <- mkDecVar lifting [] pair
    pair' <- decP (dv_dec decVar) pair
    underBinder decVar $ k (NonRec pair')
decB (_, AnnRec pairs)   k
  = do
    let recVars = map binderOfAnnPair pairs
    lifting <- and <$> mapM (shouldLift recVars) pairs
    decVars <- mapM (mkDecVar lifting recVars) pairs
    underRecBinders decVars $ do
      pairs' <- zipWithM (decP . dv_dec) decVars pairs
      k $ Rec pairs'

mkDecVar :: Bool -> [Var] -> SeqCoreBindPairWithFVs -> DecM DecVar
mkDecVar lifting recVars pair@(fvs, _)
  = do
    fvs_real <- localFreeVarsAfterLifts (fvs `delVarSetList` recVars)
    let bndr = binderOfAnnPair pair
        vars = sortQuantVars fvs_real
        dec  | lifting   = Lift (LiftInfo { li_addedArgs = vars })
             | otherwise = NoLift
    return $ DecVar bndr dec
  
decP :: Decision -> SeqCoreBindPairWithFVs -> DecM (BindPair DecVar)
decP dec (_, AnnBindJoin j join)
  = assert (not (isLift dec)) $ -- Can't lift join
    BindJoin (DecVar j NoLift) <$> decJ join
decP dec (_, AnnBindTerm bndr term)
  = BindTerm (DecVar bndr dec) <$> decT term

decJ :: SeqCoreJoinWithFVs -> DecM (Join DecVar)
decJ (_, AnnJoin bndrs comm) = Join [DecVar bndr NoLift | bndr <- bndrs] <$> decC comm

shouldLift :: [Var] -> SeqCoreBindPairWithFVs -> DecM Bool
shouldLift _ (_, AnnBindJoin {}) = return False -- Can't float a join point
                                                -- (and wouldn't want to!)
shouldLift recVars (fvs, AnnBindTerm bndr term)
  = do
    fids <- filter isId <$> localFreeVarsAfterLifts (fvs `delVarSetList` recVars)
    return $ shouldLift' fids bndr term
    
shouldLift' :: [Id] -> SeqCoreBndr -> SeqCoreTermWithFVs -> Bool
shouldLift' fids _bndr term
  = {- pprTrace "shouldLift" (ppr _bndr $$ text "Free ids:" <+> ppr fids
                                     $$ text "Binders:" <+> ppr bndrs
                                     $$ text "Verdict:" <+> text 
                                         (if answer then "YES" else "NO")) $ -}
    answer
  where
    (bndrs, _) = collectAnnBinders term
    valBndrs = filter isId bndrs
    
    answer
      | null valBndrs, not (null fids) = False -- Definitely don't unshare a thunk!
      | (valBndrs ++ fids) `lengthExceeds` tHRESHOLD = False
          -- Too many value lambdas if we float
      | otherwise = True

----------------------------
-- Phase 2: Perform Lifts --
----------------------------

{-
The lifts are performed in an RWS monad, where:

  * Passed *downward* is an in-scope set whose values carry updated IdInfos.
    Local variables simply have their unfoldings and rules zapped, since we run
    just before CorePrep, which zaps them anyway. Global variables have a
    substitution applied to them from all the floats. Note the knot-tying---
    these IdInfos must not be touched!
  * Passed *upward* is an OrdList containing the binds being floated.
  * An environment containing the Decision for each floated variable is updated
    downward, but kept as state so that, once the pass is complete, we have a
    full list of floated lambdas and any parameters added to them. Crucially,
    we've already uniquified all local binders, so collisions are not a concern.
-}

type LiftM = RWS.RWS InScopeSet Lifts DecEnv

runLiftM :: InScopeSet -> DecEnv -> LiftM a -> (a, DecEnv, Lifts)
runLiftM ins env m = RWS.runRWS m ins env

newtype Lifts = Lifts { li_lifts :: OrdList SeqCoreBind }

instance Monoid Lifts where
  mempty = Lifts nilOL
  Lifts l1 `mappend` Lifts l2 = Lifts (l1 `appOL` l2)

liftedBinds :: Lifts -> [SeqCoreBind]
liftedBinds = fromOL . li_lifts

getDecEnv :: LiftM DecEnv
getDecEnv = RWS.get

getInScopeSet :: LiftM InScopeSet
getInScopeSet = RWS.ask

findDecision :: Var -> LiftM Decision
findDecision var = do env <- getDecEnv
                      case lookupVarEnv env var of
                        Just (_, info) -> return $ Lift info
                        Nothing        -> return NoLift

findInScope :: Var -> LiftM Var
findInScope var = do ins <- getInScopeSet
                     return $ lookupInScopeOrWarn __FILE__ __LINE__ ins var

underLamBndr :: DecVar -> (Var -> LiftM a) -> LiftM a
underLamBndr (DecVar var dec) m
  = assert (case dec of { NoLift -> True; _ -> False }) $
    RWS.local (\ins -> extendInScopeSet ins var') $ m var'
  where
    var' = zapUnfoldingAndRules var
             -- Unfolding and rules may be invalidated by floats, and CorePrep
             -- is about to zap them anyway (for all locals)

underLamBndrs :: [DecVar] -> ([Var] -> LiftM a) -> LiftM a
underLamBndrs bndrs m
  = go bndrs []
  where
    go []           acc = m (reverse acc)
    go (bndr:bndrs) acc = underLamBndr bndr $ \bndr' -> go bndrs (bndr':acc)

underFloatingBndr :: DecVar -> (Var -> LiftM a) -> LiftM a
underFloatingBndr (DecVar var NoLift) _ = pprPanic "underFloatingBndr" (ppr var)
underFloatingBndr (DecVar var (Lift info@(LiftInfo extraArgVars))) m
  = do
    let ty' = mkPiTypes extraArgVars (varType var)
        var' = zapUnfoldingAndRules var `setVarType` ty'
    RWS.local (\ins -> extendInScopeSet ins var') $ do
      RWS.modify $ \env -> extendVarEnv env var' (var', info)
      m var'

underFloatingBndrs :: [DecVar] -> ([Var] -> LiftM a) -> LiftM a
underFloatingBndrs vars m
  = go vars []
  where
    go []         acc = m (reverse acc)
    go (var:vars) acc = underFloatingBndr var $ \var' -> go vars (var':acc)

liftBinding :: SeqCoreBind -> LiftM ()
liftBinding bind = RWS.tell $ Lifts (unitOL bind)

capturingLifts :: LiftM a -> LiftM (a, Lifts)
capturingLifts m = RWS.censor (const mempty) $ RWS.listen m

doLifts :: Program DecVar -> SeqCoreProgram
doLifts binds
  = binds_final
  where
    -- Heavy knot-tying: All the variables in this in-scope set have their
    -- IdInfo run through the substitution built from the floats
    ins = mkInScopeSet (mkVarEnv [(bndr, substUnfoldingAndRules subst bndr)
                                 | DecVar { dv_var = bndr } <- bndrs ])
    bndrs = bindersOfBinds binds
    (binds'_lifts, decEnv, _) = runLiftM ins emptyVarEnv $
      forM binds $ \bind ->
        case bind of
          NonRec pair -> do
                         (pair', lifts) <- capturingLifts $ doLiftsP pair
                         return (NonRec pair', lifts)
          Rec pairs   -> do
                         (pairs', lifts) <- capturingLifts $ mapM doLiftsP pairs
                         return (Rec pairs', lifts)
    subst = CoreSubst.mkOpenSubst emptyInScopeSet
                                  (map mkSubstPair (varEnvElts decEnv))
    binds_final = map (uncurry attachLifts) binds'_lifts
    attachLifts bind lifts
      = attach (mapBindersOfBind refineBndr bind) (liftedBinds lifts)
      where
        -- Being a bit paranoid here, assuming the occurrence analyzer will sort
        -- things out shortly
        attach bind          []    = bind
        attach (NonRec pair) binds = Rec (pair : flattenBinds binds)
        attach (Rec pairs)   binds = Rec (pairs ++ flattenBinds binds)
    
    refineBndr bndr = lookupInScopeOrWarn __FILE__ __LINE__ ins bndr
    
    mkSubstPair (var, LiftInfo vars) = (var, Core.mkVarApps (Core.Var var) vars)

doLiftsT :: Term DecVar -> LiftM SeqCoreTerm
doLiftsT (Lit lit)     = return $ Lit lit
doLiftsT (Type ty)     = return $ Type ty
doLiftsT (Coercion co) = return $ Coercion co
doLiftsT (Var id)
  = do dec <- findDecision id
       id' <- findInScope id
       case dec of
         NoLift    -> return $ Var id'
         Lift info -> do
                      vars <- mapM findInScope (li_addedArgs info)
                      return $ mkAppTerm (Var id') (map mkVarArg vars)
doLiftsT (Lam bndr body)
  = underLamBndr bndr $ \bndr' -> Lam bndr' <$> doLiftsT body
doLiftsT (Compute ty comm) = Compute ty <$> doLiftsC comm

doLiftsC :: Command DecVar -> LiftM SeqCoreCommand
doLiftsC (Let bind body)
  = doLiftsB bind $ \bind'_maybe -> do
      body' <- doLiftsC body
      case bind'_maybe of
        Just bind' -> return $ Let bind' body'
        Nothing    -> return body'
doLiftsC (Eval term frames end)
  = Eval <$> doLiftsT term <*> mapM doLiftsF frames <*> doLiftsE end
doLiftsC (Jump args j)
  = Jump <$> mapM doLiftsT args <*> findInScope j

doLiftsF :: Frame DecVar -> LiftM SeqCoreFrame
doLiftsF (App arg) = App <$> doLiftsT arg
doLiftsF (Cast co) = return $ Cast co
doLiftsF (Tick ti) = return $ Tick ti -- FIXME Need to substitute somehow!

doLiftsE :: End DecVar -> LiftM SeqCoreEnd
doLiftsE Return = return Return
doLiftsE (Case bndr alts)
  = underLamBndr bndr $ \bndr' -> Case bndr' <$> mapM doLiftsA alts

doLiftsA :: Alt DecVar -> LiftM SeqCoreAlt
doLiftsA (Alt con bndrs comm)
  = underLamBndrs bndrs $ \bndrs' -> Alt con bndrs' <$> doLiftsC comm

doLiftsB :: Bind DecVar -> (Maybe SeqCoreBind -> LiftM a) -> LiftM a
doLiftsB (NonRec pair) k
  = do
    pair' <- doLiftsP pair
    let bndr = binderOfPair pair
    case bndr of
      DecVar _ NoLift
        -> underLamBndr bndr $ \var' ->
             k $ Just (NonRec (pair' `setPairBinder` var'))
      DecVar _ (Lift (LiftInfo vars))
        -> underFloatingBndr bndr $ \var' -> do
             let pair'' = addArgsToRhs vars pair' `setPairBinder` var'
             liftBinding (NonRec pair'')
             k Nothing
doLiftsB (Rec pairs) k
  = case binderOfPair (head pairs) of
      -- Either all bindings are being lifted or none are, so just check head
      DecVar _ NoLift
        -> underLamBndrs (map binderOfPair pairs) $ \bndrs' -> do
             pairs' <- mapM doLiftsP pairs
             k $ Just (Rec (zipWith setPairBinder pairs' bndrs'))
      DecVar _ (Lift _)
        -> underFloatingBndrs (map binderOfPair pairs) $ \bndrs' -> do
             pairs' <- mapM doLiftsP pairs
             let alterPair _ (DecVar var NoLift) _ = pprPanic "alterPair" (ppr var)
                 alterPair pair (DecVar _ (Lift (LiftInfo vars))) bndr'
                   = addArgsToRhs vars pair `setPairBinder` bndr'
                 pairs'' = zipWith3 alterPair pairs' (map binderOfPair pairs) bndrs'
             liftBinding (Rec pairs'')
             k Nothing

addArgsToRhs :: [Var] -> BindPair Var -> SeqCoreBindPair
addArgsToRhs _    (BindJoin j _) = pprPanic "addArgsToRhs" (ppr j)
addArgsToRhs vars (BindTerm bndr term)
  = BindTerm bndr (mkLambdas vars term)

doLiftsP :: BindPair DecVar -> LiftM SeqCoreBindPair
doLiftsP (BindTerm (DecVar var _) term) = BindTerm var <$> doLiftsT term
doLiftsP (BindJoin (DecVar var _) join) = BindJoin var <$> doLiftsJ join

doLiftsJ :: Join DecVar -> LiftM SeqCoreJoin
doLiftsJ (Join bndrs body) = underLamBndrs bndrs $ \bndrs' ->
                               Join bndrs' <$> doLiftsC body

---------
lookupInScopeOrWarn :: String -> Int -> InScopeSet -> Var -> Var
lookupInScopeOrWarn file line ins var
  = lookupInScope ins var `orElse`
      warnPprTrace True file line
        (text "Not found in scope:" <+> ppr var) var
                     
zapUnfoldingAndRules :: Var -> Var
zapUnfoldingAndRules var
  | isId var  = var `setIdUnfolding` noUnfolding
                    `setIdSpecialisation` emptySpecInfo
  | otherwise = var

substUnfoldingAndRules :: CoreSubst.Subst -> Var -> Var
substUnfoldingAndRules subst var
  | isId var  = var `setIdUnfoldingLazily` CoreSubst.substUnfolding subst (realIdUnfolding var)
                    `setIdSpecialisation` CoreSubst.substSpec subst var (idSpecialisation var)
  | otherwise = var

-------------------
instance Outputable DecVar where
  ppr (DecVar var dec) = ppr var <+> parens (ppr dec)

instance OutputableBndr DecVar where
  pprBndr site (DecVar var dec) = pprBndr site var <+> parens (ppr dec)
  pprPrefixOcc (DecVar var _) = pprPrefixOcc var
  pprInfixOcc  (DecVar var _) = pprInfixOcc  var

instance Outputable Decision where
  ppr NoLift = text "no lift"
  ppr (Lift (LiftInfo { li_addedArgs = vars }))
    | null vars = text "lift"
    | otherwise = text "lift; add" <+> pprWithCommas ppr vars
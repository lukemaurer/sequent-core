{-# LANGUAGE CPP #-}

module Language.SequentCore.Simpl.Env (
  SimplEnv(..), StaticEnv, SimplIdSubst, SubstAns(..), IdDefEnv, Definition(..),
  Guidance(..),

  InCommand, InTerm, InArg, InKont, InPKont, InAlt, InBind, InBindPair, InRhs, InValue,
  InId, InKontId, InPKontId, InVar, InTyVar, InCoVar,
  OutCommand, OutTerm, OutArg, OutKont, OutPKont, OutAlt, OutBind, OutBindPair, OutRhs, OutValue,
  OutId, OutKontId, OutPKontId, OutVar, OutTyVar, OutCoVar,
  
  mkBoundTo, mkBoundToPKont, findDef, setDef,
  initialEnv, getMode, activeRule, enterScope, enterScopes, mkFreshVar, mkFreshKontId,
  substId, substPv, substKv, substTy, substTyVar, substCo, substCoVar,
  extendIdSubst, extendPvSubst, zapSubstEnvs, staticPart, setStaticPart, mkSuspension,
  inDynamicScope, zapSubstEnvsStatic, retType,
  
  Floats, emptyFloats, addNonRecFloat, addRecFloats, zapFloats, zapKontFloats,
  mapFloats, extendFloats, addFloats, wrapFloats, wrapKontFloats,
  isEmptyFloats, hasNoKontFloats,
  doFloatFromRhs, getFloatBinds, getFloats,
  
  termIsHNF, commandIsHNF
) where

import Language.SequentCore.Pretty ()
import Language.SequentCore.Simpl.ExprSize
import Language.SequentCore.Syntax
import Language.SequentCore.Translate
import Language.SequentCore.WiredIn

import BasicTypes ( Activation, TopLevelFlag(..), RecFlag(..)
                  , isActive, isTopLevel, isNotTopLevel, isNonRec )
import Coercion   ( Coercion, CvSubstEnv, CvSubst(..), isCoVar )
import qualified Coercion
import CoreMonad  ( SimplifierMode(..) )
import CoreSyn    ( Unfolding(..), UnfoldingGuidance(..), UnfoldingSource(..)
                  , mkOtherCon )
import CoreUnfold ( mkCoreUnfolding, mkDFunUnfolding  )
import DataCon    ( DataCon )
import DynFlags   ( DynFlags, ufCreationThreshold )
import FastString ( FastString )
import Id
import IdInfo
import Maybes
import OrdList
import Outputable
import Type       ( Type, TvSubstEnv, TvSubst, mkTvSubst, tyVarsOfType )
import qualified Type
import UniqSupply
import Var
import VarEnv
import VarSet

import Control.Applicative ( (<$>), (<|>) )
import Control.Exception   ( assert )
import Control.Monad       ( guard, liftM )

infixl 1 `setStaticPart`

data SimplEnv
  = SimplEnv    { se_idSubst :: SimplIdSubst   -- InId      |--> TermSubstAns (in/out)
                , se_pvSubst :: SimplPvSubst   -- InPKontId |--> PKontSubstAns (in/out)
                , se_tvSubst :: TvSubstEnv     -- InTyVar   |--> OutType
                , se_cvSubst :: CvSubstEnv     -- InCoVar   |--> OutCoercion
                , se_retId   :: Maybe KontId
                , se_retKont :: Maybe KontSubstAns
                --  ^^^ static part ^^^  --
                , se_inScope :: InScopeSet     -- OutVar    |--> OutVar
                , se_defs    :: IdDefEnv       -- OutId     |--> Definition (out)
                , se_floats  :: Floats
                , se_dflags  :: DynFlags
                , se_mode    :: SimplifierMode }

newtype StaticEnv = StaticEnv SimplEnv -- Ignore se_inScope, etc.

type SimplSubst a = IdEnv (SubstAns a) -- InId |--> SubstAns a
data SubstAns a
  = Done (Out a)
  | DoneId OutId
  | Susp StaticEnv (In a)

type SimplIdSubst  = SimplSubst SeqCoreTerm
type SimplPvSubst  = SimplSubst SeqCorePKont
type TermSubstAns  = SubstAns SeqCoreTerm
type PKontSubstAns = SubstAns SeqCorePKont
type KontSubstAns  = SubstAns SeqCoreKont

-- The original simplifier uses the IdDetails stored in a Var to store unfolding
-- info. We store similar data externally instead. (This is based on the Secrets
-- paper, section 6.3.)
type IdDefEnv = IdEnv Definition
data Definition
  = BoundTo { defTerm :: OutTerm
            , defLevel :: TopLevelFlag
            , defGuidance :: Guidance
            }
  | BoundToPKont { defPKont :: OutPKont
                 , defGuidance :: Guidance }
  | BoundToDFun { dfunBndrs :: [Var]
                , dfunDataCon :: DataCon
                , dfunArgs :: [OutTerm] }
  | NotAmong [AltCon]

data Guidance
  = Never
  | Usually   { guEvenIfUnsat :: Bool
              , guEvenIfBoring :: Bool } -- currently only used when translated
                                         -- from a Core unfolding
  | Sometimes { guSize :: Int
              , guArgDiscounts :: [Int]
              , guResultDiscount :: Int }

mkBoundTo :: DynFlags -> OutTerm -> TopLevelFlag -> Definition
mkBoundTo dflags term level = BoundTo term level (mkGuidance dflags term)

mkBoundToPKont :: DynFlags -> OutPKont -> Definition
mkBoundToPKont dflags pkont = BoundToPKont pkont (mkPKontGuidance dflags pkont)

mkGuidance :: DynFlags -> OutTerm -> Guidance
mkGuidance dflags term
  = let cap = ufCreationThreshold dflags
    in case termSize dflags cap term of
       Nothing -> Never
       Just (ExprSize base args res) ->
         Sometimes base args res

mkPKontGuidance :: DynFlags -> OutPKont -> Guidance
mkPKontGuidance dflags pkont
  = let cap = ufCreationThreshold dflags
    in case pKontSize dflags cap pkont of
       Nothing -> Never
       Just (ExprSize base args res) ->
         Sometimes base args res

type In a       = a
type InCommand  = SeqCoreCommand
type InTerm     = SeqCoreTerm
type InArg      = SeqCoreArg
type InKont     = SeqCoreKont
type InPKont    = SeqCorePKont
type InAlt      = SeqCoreAlt
type InBind     = SeqCoreBind
type InBindPair = SeqCoreBindPair
type InRhs      = SeqCoreRhs
type InValue    = SeqCoreValue
type InId       = Id
type InKontId   = KontId
type InPKontId  = PKontId
type InVar      = Var
type InTyVar    = TyVar
type InCoVar    = CoVar

type Out a      = a
type OutCommand = SeqCoreCommand
type OutTerm    = SeqCoreTerm
type OutArg     = SeqCoreArg
type OutKont    = SeqCoreKont
type OutPKont   = SeqCorePKont
type OutAlt     = SeqCoreAlt
type OutBind    = SeqCoreBind
type OutBindPair = SeqCoreBindPair
type OutRhs     = SeqCoreRhs
type OutValue   = SeqCoreValue
type OutId      = Id
type OutKontId  = KontId
type OutPKontId = PKontId
type OutVar     = Var
type OutTyVar   = TyVar
type OutCoVar   = CoVar

initialEnv :: DynFlags -> SimplifierMode -> SimplEnv
initialEnv dflags mode
  = SimplEnv { se_idSubst = emptyVarEnv
             , se_pvSubst = emptyVarEnv
             , se_tvSubst = emptyVarEnv
             , se_cvSubst = emptyVarEnv
             , se_retId   = Nothing
             , se_retKont = Nothing
             , se_inScope = emptyInScopeSet
             , se_defs    = emptyVarEnv
             , se_floats  = emptyFloats
             , se_dflags  = dflags
             , se_mode    = mode }

getMode :: SimplEnv -> SimplifierMode
getMode = se_mode

activeRule :: SimplEnv -> Activation -> Bool
-- Nothing => No rules at all
activeRule env
  | not (sm_rules mode) = \_ -> False     -- Rewriting is off
  | otherwise           = isActive (sm_phase mode)
  where
    mode = getMode env

mkSuspension :: StaticEnv -> In a -> SubstAns a
mkSuspension = Susp

enterScope :: SimplEnv -> InVar -> (SimplEnv, OutVar)
enterScope env x
  = (env', x')
  where
    SimplEnv { se_idSubst = ids, se_pvSubst = pvs
             , se_tvSubst = tvs, se_cvSubst = cvs
             , se_inScope = ins, se_defs    = defs } = env
    x1    = uniqAway ins x
    x'    = substIdType env x1
    env'  | isTyVar x   = env { se_tvSubst = tvs', se_inScope = ins', se_defs = defs' }
          | isCoVar x   = env { se_cvSubst = cvs', se_inScope = ins', se_defs = defs' }
          | isPKontId x = env { se_pvSubst = pvs', se_inScope = ins', se_defs = defs' }
          | isKontId x  = env { se_pvSubst = emptyVarEnv, se_retId = Just x
                              , se_retKont = rk',  se_inScope = ins', se_defs = defs' }
          | otherwise   = env { se_idSubst = ids', se_inScope = ins', se_defs = defs' }
    ids'  | x' /= x     = extendVarEnv ids x (DoneId x')
          | otherwise   = delVarEnv ids x
    pvs'  | x' /= x     = extendVarEnv pvs x (DoneId x')
          | otherwise   = delVarEnv pvs x
    rk'   | x' /= x     = Just (DoneId x')
          | otherwise   = Nothing
    tvs'  | x' /= x     = extendVarEnv tvs x (Type.mkTyVarTy x')
          | otherwise   = delVarEnv tvs x
    cvs'  | x' /= x     = extendVarEnv cvs x (Coercion.mkCoVarCo x')
          | otherwise   = delVarEnv cvs x
    ins'  = extendInScopeSet ins x'
    defs' = delVarEnv defs x'

enterScopes :: SimplEnv -> [InVar] -> (SimplEnv, [OutVar])
enterScopes env []
  = (env, [])
enterScopes env (x : xs)
  = (env'', x' : xs')
  where
    (env', x') = enterScope env x
    (env'', xs') = enterScopes env' xs

mkFreshVar :: MonadUnique m => SimplEnv -> FastString -> Type -> m (SimplEnv, Var)
mkFreshVar env name ty
  = do
    x <- mkSysLocalM name ty
    let x'   = uniqAway (se_inScope env) x
        env' = env { se_inScope = extendInScopeSet (se_inScope env) x' }
    return (env', x')

mkFreshKontId :: MonadUnique m => SimplEnv -> FastString -> Type -> m (SimplEnv, KontId)
mkFreshKontId env name inTy
  = do
    p <- (uniqAway (se_inScope env) . asKontId) `liftM` mkSysLocalM name inTy
    let env' = env { se_inScope = extendInScopeSet (se_inScope env) p
                   , se_pvSubst = emptyVarEnv
                   , se_retId   = Just p
                   , se_retKont = Nothing }
    return (env', p)

substId :: SimplEnv -> InId -> TermSubstAns
substId (SimplEnv { se_idSubst = ids, se_inScope = ins }) x
  = case lookupVarEnv ids x of
      -- See comments in GHC's SimplEnv.substId for explanations
      Nothing              -> DoneId (refine ins x)
      Just (DoneId x')     -> DoneId (refine ins x')
      Just (Done (Var x')) -> DoneId (refine ins x')
      Just ans             -> ans

substPv :: SimplEnv -> InId -> PKontSubstAns
substPv (SimplEnv { se_pvSubst = pvs, se_inScope = ins }) j
  = case lookupVarEnv pvs j of
      Nothing                 -> DoneId (refine ins j)
      Just (DoneId j')        -> DoneId (refine ins j')
      Just ans                -> ans

substKv :: SimplEnv -> KontId -> KontSubstAns
substKv (SimplEnv { se_retId = q, se_retKont = rk, se_inScope = ins }) p
  = case guard (Just p == q) >> rk of
      Nothing                 -> warnPprTrace True __FILE__ __LINE__
                                 (text "Unexpected cotinuation variable:" <+> pprBndr LetBind p $$
                                  text "Expected:" <+> ((pprBndr LetBind <$> q) `orElse` text "<nothing>"))
                                 DoneId (refine ins p)
      Just (DoneId p')        -> DoneId (refine ins p')
      Just (Done (Return p')) -> DoneId (refine ins p')
      Just ans                -> ans

refine :: InScopeSet -> OutVar -> OutVar
refine ins x
  | isLocalId x
  = case lookupInScope ins x of
      Just x' -> x'
      Nothing -> pprTrace "refine" (text "variable not in scope:" <+> ppr x) x
  | otherwise
  = x

getTvSubst :: SimplEnv -> TvSubst
getTvSubst env = mkTvSubst (se_inScope env) (se_tvSubst env)

substTy :: SimplEnv -> Type -> Type
substTy env t = Type.substTy (getTvSubst env) t

substTyVar :: SimplEnv -> TyVar -> Type
substTyVar env tv = Type.substTyVar (getTvSubst env) tv

substIdType :: SimplEnv -> Var -> Var
substIdType env x
  | isEmptyVarEnv tvs || isEmptyVarSet (tyVarsOfType ty)
  = x
  | otherwise
  = x `setIdType` substTy env ty
  where
    tvs = se_tvSubst env
    ty = idType x

getCvSubst :: SimplEnv -> CvSubst
getCvSubst env = CvSubst (se_inScope env) (se_tvSubst env) (se_cvSubst env)

substCo :: SimplEnv -> Coercion -> Coercion
substCo env co = Coercion.substCo (getCvSubst env) co

substCoVar :: SimplEnv -> CoVar -> Coercion
substCoVar env co = Coercion.substCoVar (getCvSubst env) co

extendIdSubst :: SimplEnv -> InVar -> TermSubstAns -> SimplEnv
extendIdSubst env x rhs
  = env { se_idSubst = extendVarEnv (se_idSubst env) x rhs }

extendPvSubst :: SimplEnv -> InVar -> PKontSubstAns -> SimplEnv
extendPvSubst env x rhs
  = env { se_pvSubst = extendVarEnv (se_pvSubst env) x rhs }

zapSubstEnvs :: SimplEnv -> SimplEnv
zapSubstEnvs env
  = env { se_idSubst = emptyVarEnv
        , se_pvSubst = emptyVarEnv
        , se_tvSubst = emptyVarEnv
        , se_cvSubst = emptyVarEnv
        , se_retKont = Nothing }

retType :: SimplEnv -> Type
retType env
  | Just k <- se_retId env
  = case isKontTy_maybe (idType k) of
      Just argTy -> substTy env argTy
      Nothing    -> pprPanic "retType" (pprBndr LetBind k)
  | otherwise
  = panic "retType at top level"

staticPart :: SimplEnv -> StaticEnv
staticPart = StaticEnv

setStaticPart :: SimplEnv -> StaticEnv -> SimplEnv
setStaticPart dest (StaticEnv src)
  = dest { se_idSubst = se_idSubst src
         , se_pvSubst = se_pvSubst src
         , se_tvSubst = se_tvSubst src
         , se_cvSubst = se_cvSubst src
         , se_retId   = se_retId   src
         , se_retKont = se_retKont src }

inDynamicScope :: StaticEnv -> SimplEnv -> SimplEnv
inDynamicScope = flip setStaticPart

-- This effectively clears everything but the retId, since it's the only static
-- part that won't get zapped
zapSubstEnvsStatic :: StaticEnv -> StaticEnv
zapSubstEnvsStatic (StaticEnv env)
  = StaticEnv $ zapSubstEnvs env

-- See [Simplifier floats] in SimplEnv

data Floats = Floats (OrdList OutBind) FloatFlag

data FloatFlag
  = FltLifted   -- All bindings are lifted and lazy
                --  Hence ok to float to top level, or recursive

  | FltOkSpec   -- All bindings are FltLifted *or*
                --      strict (perhaps because unlifted,
                --      perhaps because of a strict binder),
                --        *and* ok-for-speculation
                --  Hence ok to float out of the RHS
                --  of a lazy non-recursive let binding
                --  (but not to top level, or into a rec group)

  | FltCareful  -- At least one binding is strict (or unlifted)
                --      and not guaranteed cheap
                --      Do not float these bindings out of a lazy let

andFF :: FloatFlag -> FloatFlag -> FloatFlag
andFF FltCareful _          = FltCareful
andFF FltOkSpec  FltCareful = FltCareful
andFF FltOkSpec  _          = FltOkSpec
andFF FltLifted  flt        = flt

classifyFF :: SeqCoreBind -> FloatFlag
classifyFF (NonRec (BindTerm bndr rhs))
  | not (isStrictId bndr)    = FltLifted
  | termOkForSpeculation rhs = FltOkSpec
  | otherwise                = FltCareful
classifyFF _ = FltLifted

doFloatFromRhs :: TopLevelFlag -> RecFlag -> Bool -> OutTerm -> SimplEnv -> Bool
-- If you change this function look also at FloatIn.noFloatFromRhs
doFloatFromRhs lvl rc str rhs (SimplEnv {se_floats = Floats fs ff})
  =  not (isNilOL fs) && want_to_float && can_float
  where
     want_to_float = isTopLevel lvl || termIsCheap rhs || termIsExpandable rhs 
                     -- See Note [Float when cheap or expandable]
     can_float = case ff of
                   FltLifted  -> True
                   FltOkSpec  -> isNotTopLevel lvl && isNonRec rc
                   FltCareful -> isNotTopLevel lvl && isNonRec rc && str

emptyFloats :: Floats
emptyFloats = Floats nilOL FltLifted

unitFloat :: OutBind -> Floats
unitFloat bind = Floats (unitOL bind) (classifyFF bind)

addNonRecFloat :: SimplEnv -> OutBindPair -> SimplEnv
addNonRecFloat env pair
  = id `seq`   -- This seq forces the Id, and hence its IdInfo,
               -- and hence any inner substitutions
    env { se_floats = se_floats env `addFlts` unitFloat (NonRec pair),
          se_inScope = extendInScopeSet (se_inScope env) id }
  where
    id = binderOfPair pair

mapBinds :: Functor f => (BindPair b -> BindPair b) -> f (Bind b) -> f (Bind b)
mapBinds f pairs = fmap app pairs
  where 
    app (NonRec pair) = NonRec (f pair)
    app (Rec pair)    = Rec (map f pair)

mapFloats :: SimplEnv -> (OutBindPair -> OutBindPair) -> SimplEnv
mapFloats env@SimplEnv { se_floats = Floats fs ff } fun
   = env { se_floats = Floats (mapBinds fun fs) ff }

extendFloats :: SimplEnv -> OutBind -> SimplEnv
-- Add these bindings to the floats, and extend the in-scope env too
extendFloats env bind
  = env { se_floats  = se_floats env `addFlts` unitFloat bind,
          se_inScope = extendInScopeSetList (se_inScope env) bndrs,
          se_defs    = extendVarEnvList (se_defs env) defs}
  where
    bndrs = bindersOf bind
    defs = map asDef (flattenBind bind)
    -- FIXME The NotTopLevel flag might wind up being wrong!
    asDef (BindTerm x term) = (x, mkBoundTo (se_dflags env) term NotTopLevel)
    asDef (BindPKont p pk)  = (p, mkBoundToPKont (se_dflags env) pk)

addFloats :: SimplEnv -> SimplEnv -> SimplEnv
-- Add the floats for env2 to env1;
-- *plus* the in-scope set for env2, which is bigger
-- than that for env1
addFloats env1 env2
  = env1 {se_floats = se_floats env1 `addFlts` se_floats env2,
          se_inScope = se_inScope env2,
          se_defs = se_defs env2 }

wrapBind :: SeqCoreBind -> SeqCoreCommand -> SeqCoreCommand
wrapBind bind@(Rec {}) cmd = Let bind cmd
wrapBind (NonRec pair) cmd = addNonRec pair cmd

wrapFloats, wrapKontFloats :: SimplEnv -> OutCommand -> OutCommand
wrapFloats env cmd = foldrOL wrapBind cmd (floatBinds (se_floats env))

wrapKontFloats env cmd
  = foldr wrapBind cmd (mapMaybe onlyKonts binds)
  where
    binds = fromOL (floatBinds (se_floats env))
    onlyKonts bind@(NonRec pair) | bindsKont pair = Just bind
                                 | otherwise      = Nothing
    onlyKonts (Rec pairs)        | let pairs' = filter bindsKont pairs
                                 , not (null pairs')
                                 = Just (Rec pairs')
                                 | otherwise
                                 = Nothing

addFlts :: Floats -> Floats -> Floats
addFlts (Floats bs1 l1) (Floats bs2 l2)
  = Floats (bs1 `appOL` bs2) (l1 `andFF` l2)

zapFloats :: SimplEnv -> SimplEnv
zapFloats  env = env { se_floats  = emptyFloats  }

zapKontFloats :: SimplEnv -> SimplEnv
zapKontFloats env@(SimplEnv { se_floats = Floats fs ff })
  = env { se_floats = Floats fs' ff }
  where
    fs' = toOL . mapMaybe removeKonts . fromOL $ fs
    removeKonts (Rec pairs) | not (null pairs') = Just (Rec pairs')
                            where pairs'        = filter bindsTerm pairs
    removeKonts bind@(NonRec (BindTerm {}))     = Just bind
    removeKonts _                               = Nothing

addRecFloats :: SimplEnv -> SimplEnv -> SimplEnv
-- Flattens the floats from env2 into a single Rec group,
-- prepends the floats from env1, and puts the result back in env2
-- This is all very specific to the way recursive bindings are
-- handled; see Simpl.simplRecBind
addRecFloats env1 env2@(SimplEnv {se_floats = Floats bs ff})
  = assert (case ff of { FltLifted -> True; _ -> False })
  $ env2 {se_floats = se_floats env1 `addFlts` unitFloat (Rec (flattenBinds (fromOL bs)))}

getFloatBinds :: Floats -> [OutBind]
getFloatBinds = fromOL . floatBinds

floatBinds :: Floats -> OrdList OutBind
floatBinds (Floats bs _) = bs

getFloats :: SimplEnv -> Floats
getFloats = se_floats

isEmptyFloats :: SimplEnv -> Bool
isEmptyFloats = isNilOL . floatBinds . se_floats

-- XXX Should we cache this?
hasNoKontFloats :: SimplEnv -> Bool
hasNoKontFloats = foldrOL (&&) True . mapOL (all bindsTerm . flattenBind)
                                    . floatBinds . se_floats

findDef :: SimplEnv -> OutId -> Maybe Definition
findDef env var
  = lookupVarEnv (se_defs env) var <|> unfoldingToDef (unfoldingInfo (idInfo var))

unfoldingToDef :: Unfolding -> Maybe Definition
unfoldingToDef NoUnfolding     = Nothing
unfoldingToDef (OtherCon cons) = Just (NotAmong cons)
unfoldingToDef unf@(CoreUnfolding {})
  = Just $ BoundTo { defTerm     = termFromCoreExpr (uf_tmpl unf)
                   , defLevel    = if uf_is_top unf then TopLevel else NotTopLevel
                   , defGuidance = unfGuidanceToGuidance (uf_guidance unf) }
unfoldingToDef unf@(DFunUnfolding {})
  = Just $ BoundToDFun { dfunBndrs    = df_bndrs unf
                       , dfunDataCon  = df_con unf
                       , dfunArgs     = map termFromCoreExpr (df_args unf) }

unfGuidanceToGuidance :: UnfoldingGuidance -> Guidance
unfGuidanceToGuidance UnfNever = Never
unfGuidanceToGuidance (UnfWhen { ug_unsat_ok = unsat , ug_boring_ok = boring })
  = Usually { guEvenIfUnsat = unsat , guEvenIfBoring = boring }
unfGuidanceToGuidance (UnfIfGoodArgs { ug_args = args, ug_size = size, ug_res = res })
  = Sometimes { guSize = size, guArgDiscounts = args, guResultDiscount = res }

setDef :: SimplEnv -> OutId -> Definition -> (SimplEnv, OutId)
setDef env x def
  = (env', x')
  where
    env' = env { se_inScope = extendInScopeSet (se_inScope env) x'
               , se_defs    = extendVarEnv (se_defs env) x' def }
    x'   | DFunUnfolding {} <- idUnfolding x = x -- don't mess with these since
                                                 -- we don't generate them
         | otherwise = x `setIdUnfolding` defToUnfolding def

defToUnfolding :: Definition -> Unfolding
defToUnfolding (NotAmong cons) = mkOtherCon cons
defToUnfolding (BoundToPKont {})
  = NoUnfolding -- TODO Can we do better? Translating requires knowing the outer linear cont.
defToUnfolding (BoundTo { defTerm = term, defLevel = lev, defGuidance = guid })
  = mkCoreUnfolding InlineRhs (isTopLevel lev) (termToCoreExpr term)
      (termArity term) (guidanceToUnfGuidance guid)
defToUnfolding (BoundToDFun { dfunBndrs = bndrs, dfunDataCon = con, dfunArgs = args})
  = mkDFunUnfolding bndrs con (map termToCoreExpr args)

guidanceToUnfGuidance :: Guidance -> UnfoldingGuidance
guidanceToUnfGuidance Never = UnfNever
guidanceToUnfGuidance (Usually { guEvenIfUnsat = unsat, guEvenIfBoring = boring })
  = UnfWhen { ug_unsat_ok = unsat, ug_boring_ok = boring }
guidanceToUnfGuidance (Sometimes { guSize = size, guArgDiscounts = args, guResultDiscount = res})
  = UnfIfGoodArgs { ug_size = size, ug_args = args, ug_res = res }

-- TODO This might be in Syntax, but since we're not storing our "unfoldings" in
-- ids, we rely on the environment to tell us whether a variable has been
-- evaluated.

termIsHNF :: SimplEnv -> SeqCoreTerm -> Bool
termIsHNF _   (Lit {})  = True
termIsHNF env (Var id)
  = case lookupVarEnv (se_defs env) id of
      Just (NotAmong {})      -> True
      Just (BoundTo term _ _) -> termIsHNF env term
      _                       -> False
termIsHNF env (Compute _ comm) = commandIsHNF env comm
termIsHNF _   _        = False

commandIsHNF :: SimplEnv -> SeqCoreCommand -> Bool
commandIsHNF _env (Eval (Var fid) kont)
  | let (args, _) = collectArgs kont
  , let nargs = length (filter isValueArg args)
  , isDataConWorkId fid && nargs <= idArity fid
  || nargs < idArity fid
  = True
commandIsHNF _env (Eval (Compute {}) _)
  = False
commandIsHNF env (Eval term (Return _))
  = termIsHNF env term
commandIsHNF _ _
  = False

instance Outputable SimplEnv where
  ppr env
    =  text "<InScope =" <+> braces (fsep (map ppr (varEnvElts (getInScopeVars (se_inScope env)))))
--    $$ text " Defs      =" <+> ppr defs
    $$ text " IdSubst   =" <+> ppr (se_idSubst env)
    $$ text " PvSubst   =" <+> ppr (se_pvSubst env)
    $$ text " TvSubst   =" <+> ppr (se_tvSubst env)
    $$ text " CvSubst   =" <+> ppr (se_cvSubst env)
    $$ text " RetId     =" <+> ppr (se_retId env)
    $$ text " RetKont   =" <+> ppr (se_retKont env)
    $$ text " Floats    =" <+> ppr floatBndrs
     <> char '>'
    where
      floatBndrs  = bindersOfBinds (getFloatBinds (se_floats env))

instance Outputable StaticEnv where
  ppr (StaticEnv env)
    =  text "<IdSubst   =" <+> ppr (se_idSubst env)
    $$ text " KvSubst   =" <+> ppr (se_pvSubst env)
    $$ text " TvSubst   =" <+> ppr (se_tvSubst env)
    $$ text " CvSubst   =" <+> ppr (se_cvSubst env)
    $$ text " RetId     =" <+> ppr (se_retId env)
    $$ text " RetKont   =" <+> ppr (se_retKont env)
     <> char '>'

instance Outputable a => Outputable (SubstAns a) where
  ppr (Done v) = brackets (text "Done:" <+> ppr v)
  ppr (DoneId x) = brackets (text "Id:" <+> ppr x)
  ppr (Susp {}) = text "Suspended"
--  ppr (Susp _env v)
--    = brackets $ hang (text "Suspended:") 2 (ppr v)

instance Outputable Definition where
  ppr (BoundTo c level guid)
    = sep [brackets (ppr level <+> ppr guid), ppr c]
  ppr (BoundToPKont pk guid)
    = sep [brackets (ppr guid), ppr pk]
  ppr (BoundToDFun bndrs con args)
    = char '\\' <+> hsep (map ppr bndrs) <+> arrow <+> ppr con <+> hsep (map (parens . ppr) args)
  ppr (NotAmong alts) = text "NotAmong" <+> ppr alts

instance Outputable Guidance where
  ppr Never = text "Never"
  ppr (Usually unsatOk boringOk)
    = text "Usually" <+> brackets (hsep $ punctuate comma $ catMaybes
                                    [if unsatOk then Just (text "even if unsat") else Nothing,
                                     if boringOk then Just (text "even if boring cxt") else Nothing])
  ppr (Sometimes base argDiscs resDisc)
    = text "Sometimes" <+> brackets (int base <+> ppr argDiscs <+> int resDisc)

instance Outputable Floats where
  ppr (Floats binds ff) = ppr ff $$ ppr (fromOL binds)

instance Outputable FloatFlag where
  ppr FltLifted = text "FltLifted"
  ppr FltOkSpec = text "FltOkSpec"
  ppr FltCareful = text "FltCareful"

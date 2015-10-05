{-# LANGUAGE LambdaCase, FlexibleInstances, TypeSynonymInstances #-}

-- | 
-- Module      : Language.SequentCore.Syntax
-- Description : Sequent Core syntax
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- The AST for Sequent Core, with basic operations.

module Language.SequentCore.Syntax (
  -- * AST Types
  Term(..), Arg, Frame(..), End(..), Join(..), Command(..),
  Bind(..), BindPair(..),
  Alt(..), AltCon(..), Program, JoinId, Kont,
  SeqCoreTerm, SeqCoreArg, SeqCoreKont, SeqCoreFrame, SeqCoreEnd, SeqCoreJoin,
    SeqCoreCommand, SeqCoreBind, SeqCoreBindPair, SeqCoreBndr,
    SeqCoreAlt, SeqCoreProgram,
  -- * Constructors
  mkCommand, mkVarArg, mkLambdas, mkCompute, mkComputeEval,
  mkAppTerm, mkConstruction, mkConstructionCommand,
  mkCast, impossibleCommand,
  addLets, addLetsToTerm, addNonRec,
  -- * Deconstructors
  lambdas, collectArgs, collectTypeArgs, collectTypeAndOtherArgs, collectArgsUpTo,
  splitCastTerm, splitCastCommand,
  spanTypes,
  flattenCommand,
  isValueArg, isTypeArg, isCoArg, isTyCoArg, isAppFrame, isValueAppFrame,
  isTrivial, isTrivialTerm, isTrivialKont, isTrivialJoin,
  isReturnKont, isReturn, isDefaultAlt,
  termIsConstruction, termAsConstruction, splitConstruction,
  commandAsSaturatedCall, asSaturatedCall, asValueCommand,
  binderOfPair, setPairBinder,
  bindsTerm, bindsJoin, flattenBind, flattenBinds, bindersOf, bindersOfBinds,
  -- * Calculations
  termType, frameType, applyTypeToArg, applyTypeToArgs, applyTypeToFrames,
  termIsBottom, commandIsBottom,
  needsCaseBinding,
  termIsWorkFree,
  termOkForSpeculation, commandOkForSpeculation,
  termOkForSideEffects, commandOkForSideEffects,
  termIsCheap, commandIsCheap,
  termIsExpandable, commandIsExpandable,
  CheapAppMeasure, isCheapApp, isExpandableApp,
  termIsCheapBy, commandIsCheapBy,
  -- * Continuation ids
  isJoinId, Language.SequentCore.WiredIn.mkKontTy, kontTyArg,
  -- * Alpha-equivalence
  cheapEqTerm, cheapEqFrame, cheapEqCommand,
  (=~=), AlphaEq(..), AlphaEnv, HasId(..)
) where

import {-# SOURCE #-} Language.SequentCore.Pretty ()
import Language.SequentCore.Util
import Language.SequentCore.WiredIn

import Coercion  ( Coercion, coercionKind, coercionType, coreEqCoercion
                 , isCoVar, isCoVarType
                 , isReflCo, mkCoCast, mkCoVarCo, mkTransCo )
import CoreSyn   ( AltCon(..), Tickish, tickishCounts, isRuntimeVar
                 , isEvaldUnfolding )
import DataCon   ( DataCon, dataConTyCon, dataConRepArity
                 , dataConUnivTyVars, dataConExTyVars, dataConWorkId )
import Id        ( Id, isDataConWorkId, isDataConWorkId_maybe, isConLikeId
                 , idArity, idType, idDetails, idUnfolding, isBottomingId )
import IdInfo    ( IdDetails(..) )
import Literal   ( Literal, isZeroLit, litIsTrivial, literalType, mkMachString )
import MkCore    ( rUNTIME_ERROR_ID, mkWildValBinder )
import Outputable
import Pair      ( Pair(..), pSnd )
import PrimOp    ( PrimOp(..), primOpOkForSpeculation, primOpOkForSideEffects
                 , primOpIsCheap )
import TyCon
import Type      ( Type, KindOrType, eqType )
import qualified Type
import TysPrim
import TysWiredIn
import Util      ( count )
import Var       ( Var, isId )
import VarEnv

import Control.Monad ( guard )

import Data.Maybe

--------------------------------------------------------------------------------
-- AST Types
--------------------------------------------------------------------------------

-- | An expression producing a value. These include literals, lambdas,
-- and variables, as well as types and coercions (see GHC's 'GHC.Expr' for the
-- reasoning). They also include computed values, which bind the current
-- continuation in the body of a command.
data Term b     = Lit Literal       -- ^ A primitive literal value.
                | Var Id            -- ^ A term variable. Must /not/ be a
                                    -- nullary constructor; use 'Cons' for this.
                | Lam b (Term b)    -- ^ A function. Binds some arguments and
                                    -- a continuation. The body is a command.
                | Compute Type (Command b)
                                    -- ^ A value produced by a computation.
                                    -- Binds a continuation.  The type is the type
                                    -- of the value returned by the computation
                | Type Type         -- ^ A type. Used to pass a type as an
                                    -- argument to a type-level lambda.
                | Coercion Coercion -- ^ A coercion. Used to pass evidence
                                    -- for the @cast@ operation to a lambda.

-- | An argument, which can be a regular term or a type or coercion.
type Arg b = Term b

-- | A piece of context for a term. So called because we can think of them as
-- as stack frames in an idealized abstract machine. Typically a list of frames
-- is simply a list of arguments, but other bits of context such as casts and
-- ticks are also frames.
--
-- In contrast to an 'End', a 'Frame' takes input and produces output. Thus a
-- 'Command' can be seen as a pipeline starting from a 'Term', passing through
-- some 'Frame's, and ending at an 'End'.
data Frame b    = App {- expr -} (Arg b)
                  -- ^ Apply the value to an argument.
                | Cast {- expr -} Coercion
                  -- ^ Cast the value using the given coercion.
                | Tick (Tickish Id) {- expr -}
                  -- ^ Annotate the enclosed frame. Used by the profiler.

-- | The end of a continuation. After arguments and casts are applied, we can
-- do two things to a value: Return it to the calling context or perform a case
-- analysis.
data End b      = Return
                  -- ^ Pass to the bound continuation.
                | Case {- expr -} b [Alt b]
                  -- ^ Perform case analysis on the value.

-- | A general computation. A command brings together a list of bindings and
-- either:
--   * A computation to perform, including a /term/ that produces a value, some
--     /frames/ that process the value, and an /end/ that may finish the
--     computation or branch as a case expression.
--   * A jump to a join point, with a list of arguments and the join id.
data Command b = Let (Bind b) (Command b)
               | Eval (Term b) [Frame b] (End b)
               | Jump [Arg b] JoinId

-- | A parameterized continuation, otherwise known as a join point. Where a
-- regular continuation represents the context of a single expression, a
-- join point is a point in the control flow that many different computations
-- might jump to.
data Join b     = Join [b] (Command b)

-- | The identifier for a join point.
type JoinId = Id

-- | The binding of one identifier to one term or continuation.
data BindPair b = BindTerm b (Term b)
                | BindJoin b (Join b)

-- | A binding. Similar to the @Bind@ datatype from GHC. Can be either a single
-- non-recursive binding or a mutually recursive block.
data Bind b     = NonRec (BindPair b) -- ^ A single non-recursive binding.
                | Rec [BindPair b]    -- ^ A block of mutually recursive bindings.

-- | A case alternative. Given by the head constructor (or literal), a list of
-- bound variables (empty for a literal), and the body as a 'Command'.
data Alt b      = Alt AltCon [b] (Command b)

-- | The frames and end from an Eval, together forming a continuation.
type Kont b     = ([Frame b], End b)
                  -- ^ A continuation is expressed as a series of frames
                  -- (usually arguments to apply), followed by a terminal
                  -- action (such as a case analysis).

-- | An entire program.
type Program a  = [Bind a]

-- | Usual binders for Sequent Core terms
type SeqCoreBndr    = Var
-- | Usual instance of 'Term', with 'Var's for binders
type SeqCoreTerm    = Term    Var
-- | Usual instance of 'Arg', with 'Var's for binders
type SeqCoreArg     = Arg     Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCoreKont    = Kont    Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCoreFrame   = Frame   Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCoreEnd     = End     Var
-- | Usual instance of 'Command', with 'Var's for binders
type SeqCoreCommand = Command Var
-- | Usual instance of 'Bind', with 'Var's for binders
type SeqCoreBind    = Bind    Var
-- | Usual instance of 'BindPair', with 'Var's for binders
type SeqCoreBindPair = BindPair Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCoreJoin    = Join    Var
-- | Usual instance of 'Alt', with 'Var's for binders
type SeqCoreAlt     = Alt     Var
-- | Usual instance of 'Term', with 'Var's for binders
type SeqCoreProgram = Program Var

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Constructs a command, given @let@ bindings, a term, and a continuation.
--
-- A smart constructor. If the term happens to be a Compute, may fold its
-- command into the result.
mkCommand :: HasId b => [Bind b] -> Term b -> [Frame b] -> End b -> Command b
mkCommand binds (Compute _ comm) frames end
  | (binds', Left (term, [], Return)) <- flattenCommand comm
  = mkCommand (binds ++ binds') term frames end

mkCommand binds term frames end
  = foldr Let (Eval term frames end) binds

-- | Makes an argument out of a variable. Type variables must be represented
-- using the 'Type' constructor and coercion variables must use the 'Coercion'
-- constructor; this function chooses as appropriate.
mkVarArg :: Var -> Arg b
mkVarArg x | Type.isTyVar x = Type (Type.mkTyVarTy x)
           | Coercion.isCoVar x = Coercion (mkCoVarCo x)
           | otherwise = Var x

-- | Wrap a term in a series of lambdas.
mkLambdas :: [b] -> Term b -> Term b
mkLambdas = flip (foldr Lam)

mkCompute :: Type -> Command b -> Term b
-- | Wraps a command that returns to the given continuation id in a term using
-- 'Compute'. If the command is a value command (see 'asValueCommand'), unwraps
-- it instead.
mkCompute ty comm
  | Just val <- asValueCommand comm
  = val
  | otherwise
  = Compute ty comm

-- | Forms a term as a computation with a given term and given frames. Helpful
-- because it works out the Type argument to Compute automatically.
mkComputeEval :: HasId b => Term b -> [Frame b] -> Term b
mkComputeEval v fs = mkCompute ty (Eval v fs Return)
  where
    ty = foldl frameType (termType v) fs

-- | Forms a term comprising the application of several arguments to a term.
mkAppTerm :: HasId b => Term b -> [Term b] -> Term b
mkAppTerm fun args = mkComputeEval fun (map App args)

-- | Forms a term that casts the given term with the given coercion. 
mkCast :: Term b -> Coercion -> Term b
mkCast term co | isReflCo co = term
mkCast (Coercion termCo) co | isCoVarType (pSnd (coercionKind co))
                            = Coercion (mkCoCast termCo co)
-- Unfortunately, our representation isn't good at finding casts at top level.
-- We would need a deep search to find anything besides this very simple case.
-- Fortunately, this should ensure that successive mkCasts accumulate nicely.
mkCast (Compute _ (Eval term [Cast co1] Return)) co2
  = mkCast term (mkTransCo co1 co2)
mkCast term co
  = Compute ty (Eval term [Cast co] Return)
  where
    ty = pSnd (coercionKind co)

-- | Builds a term that applies a constructor to some arguments.
mkConstruction :: HasId b => DataCon -> [Type] -> [Term b] -> Term b
mkConstruction dc tyArgs valArgs
  = mkAppTerm (Var (dataConWorkId dc)) (map Type tyArgs ++ valArgs)

-- | Builds a command that applies a constructor to some arguments.
mkConstructionCommand :: DataCon -> [Type] -> [Term b] -> Command b
mkConstructionCommand dc tyArgs valArgs
  = Eval (Var (dataConWorkId dc)) (map App (map Type tyArgs ++ valArgs)) Return

-- | A command that throws a runtime error indicating that an impossible case
-- alternative has been reached.
impossibleCommand :: SeqCoreCommand
impossibleCommand
  = Eval (Var rUNTIME_ERROR_ID) [App (Type unitTy), App errString] $
      Case (mkWildValBinder unitTy) []
  where
    errString = Lit (mkMachString "Impossible case alternative")

-- | Adds the given bindings outside those in the given command.
addLets :: [Bind b] -> Command b -> Command b
addLets = flip (foldr Let)

-- | Adds the given binding outside the given command, possibly using a case
-- binding rather than a let. See "CoreSyn" on the let/app invariant.
addNonRec :: HasId b => BindPair b -> Command b -> Command b
addNonRec (BindTerm bndr rhs) comm
  | needsCaseBinding (idType (identifier bndr)) rhs
  = mkCommand [] rhs [] (Case bndr [Alt DEFAULT [] comm])
addNonRec pair comm
  = addLets [NonRec pair] comm

-- | Adds the given bindings to a term. Generally this requires making it into
-- a Compute, as Let produces a command, not a term.
addLetsToTerm :: [SeqCoreBind] -> SeqCoreTerm -> SeqCoreTerm
addLetsToTerm [] term = term
addLetsToTerm binds term = mkCompute ty (mkCommand binds term [] Return)
  where
    ty = termType term

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

-- | Divide a term into a sequence of lambda-bound variables and a body. If @v@
-- is not a lambda, then @lambdas v == ([], v)@.
lambdas :: Term b -> ([b], Term b)
lambdas (Lam x body) = (x : xs, body')
  where (xs, body')  = lambdas body
lambdas term         = ([], term)

-- | Divide a list of frames into a sequence of value arguments and an outer
-- continuation. If @fs@ does not start with a value application frame, then
-- @collectArgs fs == ([], fs)@.
collectArgs :: [Frame b] -> ([Term b], [Frame b])
collectArgs frames
  = go frames
  where
    go (App arg : fs) = (arg : args, k') where (args, k') = go fs
    go fs             = ([], fs)

-- | Divide a list of frames into a sequence of type arguments and an outer
-- context. If @fs@ does not start with a type application frame, then
-- @collectTypeArgs fs == ([], fs)@.
collectTypeArgs :: [Frame b] -> ([KindOrType], [Frame b])
collectTypeArgs frames
  = go frames
  where
    go (App (Type ty) : fs) = (ty : tys, k') where (tys, k') = go fs
    go fs                   = ([], fs)

-- | Divide a list of frames into a sequence of type arguments, then a sequence
-- of non-type arguments, then the rest. If @fs@ does not start with an
-- application frame, then @collectTypeAndOtherArgs fs == ([], [], fs)@.
-- Note that, in general, type and value arguments can be arbitrarily
-- intermingled, so the remaining frames may in fact have further arguments
-- (starting with type arguments).
collectTypeAndOtherArgs :: [Frame b] -> ([KindOrType], [Term b], [Frame b])
collectTypeAndOtherArgs fs
  = let (tys, fs') = collectTypeArgs fs
        (vs, fs'') = collectArgs fs'
    in (tys, vs, fs'')

-- | Peel a sequence of up to @n@ arguments off the front of a list of frames.
-- If @fs@ does not start with an application frame, then
-- @collectArgsUpTo n fs == ([], fs)@.
collectArgsUpTo :: Int -> [Frame b] -> ([Term b], [Frame b])
collectArgsUpTo n fs
  = go n fs
  where
    go 0 fs
      = ([], fs)
    go n (App arg : fs)
      = (arg : args, k')
      where (args, k') = go (n - 1) fs
    go _ fs
      = ([], fs)

-- | Divide a list of terms into an initial sublist of types and the remaining
-- terms.
spanTypes :: [Arg b] -> ([KindOrType], [Arg b])
spanTypes = mapWhileJust $ \case { Type ty -> Just ty; _ -> Nothing }

-- | Put a command into a "flat" representation, as a list of bindings followed
-- by either ('Left') a term, some frames, and an end comprising a computation
-- to evaluate; or ('Right') some arguments and a join id to jump to.
flattenCommand :: Command b -> ([Bind b], Either (Term b, [Frame b], End b) ([Arg b], JoinId))
flattenCommand = go []
  where
    go binds (Let bind comm)        = go (bind:binds) comm
    go binds (Eval term frames end) = (reverse binds, Left (term, frames, end))
    go binds (Jump args j)          = (reverse binds, Right (args, j))

-- TODO Since this function has to look at the end of a list that could be long
-- (namely the list of frames in the continuation), we should try and find ways
-- around needing it.
-- | Given a term, see if it is a coercion wrapping another term and extract
-- the coercion and the inner term.
splitCastTerm :: Term b -> (Term b, Maybe Coercion)
splitCastTerm (Compute _ty comm)
  | (comm', Just co) <- splitCastCommand comm
  , let Pair fromTy _toTy = coercionKind co
  = (mkCompute fromTy comm', Just co)
splitCastTerm term = (term, Nothing)

-- | Given a command, see if it wraps a cast around a computation and extract
-- the coercion and the rest of the computation.
splitCastCommand :: Command b -> (Command b, Maybe Coercion)
splitCastCommand (Eval term fs Return)
  | not (null fs)
  , Cast co <- last fs
  = (Eval term (init fs) Return, Just co)
splitCastCommand (Let b comm)
  | (comm', Just co) <- splitCastCommand comm
  = (Let b comm', Just co)
splitCastCommand comm = (comm, Nothing)

-- | True if the given term constitutes a value argument rather than a type
-- argument (see 'Type').
isValueArg :: Term b -> Bool
isValueArg (Type _) = False
isValueArg _ = True

-- | True if the given term is a type. See 'Type'.
isTypeArg :: Arg b -> Bool
isTypeArg (Type _) = True
isTypeArg _ = False

-- | True if the given term is a coercion. See 'Coercion'.
isCoArg :: Arg b -> Bool
isCoArg (Coercion _) = True
isCoArg _ = False

-- | True if the given term is a type or a coercion.
isTyCoArg :: Arg b -> Bool
isTyCoArg arg = isTypeArg arg || isCoArg arg

-- | True if the given frame is an argument.
isAppFrame :: Frame b -> Bool
isAppFrame (App {}) = True
isAppFrame _        = False

-- | True if the given frame applies a value argument.
isValueAppFrame :: Frame b -> Bool
isValueAppFrame (App (Type {})) = False
isValueAppFrame (App {})        = True
isValueAppFrame _               = False

-- | True if the given command is so simple we can duplicate it freely. This
-- means it has no bindings and its term and continuation are both trivial.
isTrivial :: HasId b => Command b -> Bool
isTrivial (Let {})       = False
isTrivial (Eval term frames end) = isReturn end && isTrivialTerm term && all isTrivialFrame frames
isTrivial (Jump args _)  = all isTrivialTerm args

-- | True if the given term is so simple we can duplicate it freely. Some
-- literals are not trivial, and a lambda whose argument is not erased or whose
-- body is non-trivial is also non-trivial.
isTrivialTerm :: HasId b => Term b -> Bool
isTrivialTerm (Lit l)     = litIsTrivial l
isTrivialTerm (Lam x t)   = not (isRuntimeVar (identifier x)) && isTrivialTerm t
isTrivialTerm (Compute _ c)  = isTrivial c
isTrivialTerm _           = True

-- | True if the given continuation is so simple we can duplicate it freely.
-- This is true of casts and of applications of erased arguments (types and
-- coercions). Ticks are not considered trivial, since this would cause them to
-- be inlined.
isTrivialKont :: HasId b => Kont b -> Bool
isTrivialKont (fs, Return) = all isTrivialFrame fs
isTrivialKont _            = False

-- | True if the given frame is so simple we can duplicate it freely. This is
-- true of casts and of erased applications (types and coercions). Ticks are not
-- considered trivial, since this would cause them to be inlined.
isTrivialFrame :: HasId b => Frame b -> Bool
isTrivialFrame (App v)  = isTyCoArg v
isTrivialFrame (Cast _) = True
isTrivialFrame (Tick _) = False

-- | True if the given join point is so simple we can duplicate it freely. All
-- the arguments must be types or coercions and the body must itself be
-- trivial.
isTrivialJoin :: HasId b => Join b -> Bool
isTrivialJoin (Join xs comm) = all (not . isRuntimeVar) (identifiers xs)
                            && isTrivial comm

-- | True if the given continuation is a return continuation, @Kont [] (Return _)@.
isReturnKont :: Kont b -> Bool
isReturnKont ([], Return) = True
isReturnKont _            = False

-- | True if the given continuation end is a return, @Return@.
isReturn :: End b -> Bool
isReturn Return = True
isReturn _      = False

-- | True if the given alternative is a default alternative, @Alt DEFAULT _ _@.
isDefaultAlt :: Alt b -> Bool
isDefaultAlt (Alt DEFAULT _ _) = True
isDefaultAlt _                 = False

-- | If a command represents a saturated call to some function, splits it into
-- the function, the arguments, and the remaining continuation after the
-- arguments.
commandAsSaturatedCall :: HasId b =>
                          Command b -> Maybe (Term b, [Term b], [Frame b], End b)
commandAsSaturatedCall (Let _ comm)
  = commandAsSaturatedCall comm
commandAsSaturatedCall (Eval term frames end)
  = do
    (args, frames') <- asSaturatedCall term frames
    return (term, args, frames', end)
commandAsSaturatedCall (Jump {})
  = Nothing

-- | True if a term is simply a saturated application of a data constructor.
termIsConstruction :: HasId b => Term b -> Bool
termIsConstruction = isJust . termAsConstruction

-- | If a term is a saturated application of a data construtor, extract the
-- constructor and the type and value arguments it's applied to.
termAsConstruction :: HasId b => Term b -> Maybe (DataCon, [Type], [Term b])
termAsConstruction (Var id)      | Just dc <- isDataConWorkId_maybe id
                                 , dataConRepArity dc == 0
                                 , null (dataConUnivTyVars dc)
                                 , null (dataConExTyVars dc)
                                 = Just (dc, [], [])
termAsConstruction (Compute _ c) = commandAsConstruction c
termAsConstruction _             = Nothing

-- | If a term and a continuation comprise a saturated application of a data
-- constructor and possibly an outer context, extract the constructor, the
-- type arguments, the value arguments, and the outer context.
splitConstruction :: Term b -> Kont b -> Maybe (DataCon, [Type], [Term b], Kont b)
splitConstruction (Var fid) (frames, end)
  | Just dataCon <- isDataConWorkId_maybe fid
  , length valArgs == dataConRepArity dataCon
  = Just (dataCon, tyArgs, valArgs, (frames', end))
  where
    (tyArgs, valArgs, frames') = collectTypeAndOtherArgs frames
splitConstruction _ _
  = Nothing

-- | If a command is simply a saturated application of a data constructor,
-- extracts the constructor and its term and type arguments.
commandAsConstruction :: Command b
                      -> Maybe (DataCon, [Type], [Term b])
commandAsConstruction (Eval term fs end)
  | Just (dc, tyArgs, valArgs, ([], Return)) <- splitConstruction term (fs, end)
  = Just (dc, tyArgs, valArgs)
commandAsConstruction _
  = Nothing

-- | If the given term is a function, and the given frames would provide
-- enough arguments to saturate it, returns the arguments and the remainder of
-- the frames.
asSaturatedCall :: HasId b => Term b -> [Frame b]
                -> Maybe ([Term b], [Frame b])
asSaturatedCall term frames
  | 0 < arity, arity <= length args
  = Just (args, others)
  | otherwise
  = Nothing
  where
    arity = termArity term
    (args, others) = collectArgs frames

-- | If a command does nothing but provide a value to the given continuation id,
-- returns that value.
asValueCommand :: Command b -> Maybe (Term b)
asValueCommand (Eval term [] Return)
  = Just term
asValueCommand _
  = Nothing

-- | Get the pairs from a binding.
flattenBind :: Bind b -> [BindPair b]
flattenBind (NonRec pair) = [pair]
flattenBind (Rec pairs)   = pairs

-- | Get all the pairs from a list of bindings.
flattenBinds :: [Bind b] -> [BindPair b]
flattenBinds = concatMap flattenBind

bindsTerm, bindsJoin :: BindPair b -> Bool
-- | True if this bind pair binds a term.
bindsTerm (BindTerm {}) = True
bindsTerm (BindJoin {}) = False

-- | True if this bind pair binds a join point.
bindsJoin pair = not (bindsTerm pair)

-- | Get the binder from a binding pair.
binderOfPair :: BindPair b -> b
binderOfPair (BindTerm x _) = x
binderOfPair (BindJoin j _) = j

-- | Change the binder in a binding pair (of either kind).
setPairBinder :: BindPair b -> b -> BindPair b
setPairBinder (BindTerm _ term) x = BindTerm x term
setPairBinder (BindJoin _ pk)   j = BindJoin j pk

-- | Get the binders from a binding.
bindersOf :: Bind b -> [b]
bindersOf (NonRec pair) = [binderOfPair pair]
bindersOf (Rec pairs) = map binderOfPair pairs

-- | Get all the binders in a list of bindings.
bindersOfBinds :: [Bind b] -> [b]
bindersOfBinds = concatMap bindersOf

--------------------------------------------------------------------------------
-- Calculations
--------------------------------------------------------------------------------

-- | Compute the type of a term.
termType :: HasId b => Term b -> Type
termType (Lit l)        = literalType l
termType (Var x)        = idType x
termType (Lam x t)      = Type.mkPiType (identifier x) (termType t)
termType (Compute ty _) = ty
-- see exprType in GHC CoreUtils
termType _other         = alphaTy

-- | Compute the type of a frame's output, given the type of its input. (The
--   input type of a type application is not uniquely defined, so it must be
--   specified.)
frameType :: HasId b => Type -> Frame b -> Type
frameType ty (App (Type argTy)) = ty `Type.applyTy` argTy
frameType ty (App _)            = Type.funResultTy ty
frameType _  (Cast co)          = pSnd (coercionKind co)
frameType ty (Tick _)           = ty

-- | Compute the result type if a value of the given type (assumed to be a
-- function or forall) is applied to the given argument.
applyTypeToArg :: Type -> Arg b -> Type
applyTypeToArg ty (Type tyArg) = ty `Type.applyTy` tyArg
applyTypeToArg ty _            = Type.funResultTy ty

-- | Compute the result type if a value of the given type (assumed to be a
-- function or forall) is applied to the given arguments.
applyTypeToArgs :: Type -> [Arg b] -> Type
applyTypeToArgs ty [] = ty
applyTypeToArgs ty args@(Type _ : _)
  = applyTypeToArgs (ty `Type.applyTys` tyArgs) args'
  where
    (tyArgs, args') = spanTypes args
applyTypeToArgs ty (_ : args)
  = applyTypeToArgs (Type.funResultTy ty) args

-- | Compute the result type if the given frames are applied to the given value.
applyTypeToFrames :: Type -> [Frame b] -> Type
applyTypeToFrames ty [] = ty
applyTypeToFrames ty fs@(App (Type _) : _)
  = applyTypeToFrames (ty `Type.applyTys` tyArgs) fs'
  where
    (tyArgs, fs') = collectTypeArgs fs
applyTypeToFrames ty (App _ : fs)
  = applyTypeToFrames (Type.funResultTy ty) fs
applyTypeToFrames _  (Cast co : fs)
  = applyTypeToFrames (pSnd (coercionKind co)) fs
applyTypeToFrames ty (Tick _ : fs)
  = applyTypeToFrames ty fs

-- | Compute (a conservative estimate of) the arity of a term, in the simplest
-- manner possible: Count the value lambdas, then if the body is a variable, add
-- its advertised arity.
termArity :: HasId b => Term b -> Int
termArity (Var x)
  | isId x = idArity x
termArity (Lam x t)
  | Type.isTyVar (identifier x)
  = termArity t
  | otherwise
  = 1 + termArity t
termArity _
  = 0

-- | Find whether an expression is definitely bottom.
termIsBottom :: Term b -> Bool
termIsBottom (Var x)       = isBottomingId x && idArity x == 0
termIsBottom (Compute _ c) = commandIsBottom c
termIsBottom _             = False

-- | Find whether a command definitely evaluates to bottom.
commandIsBottom :: Command b -> Bool
commandIsBottom (Let _ comm) = commandIsBottom comm
commandIsBottom (Eval (Var x) fs _)
  = isBottomingId x && go (0 :: Int) fs
    where
      go n (App (Type _) : fs) = go n fs
      go n (App  _ : fs)   = (go $! (n+1)) fs
      go n (Tick _ : fs)   = go n fs
      go n (Cast _ : fs)   = go n fs
      go n []              = n >= idArity x
commandIsBottom (Jump _ j) = isBottomingId j
commandIsBottom _          = False

-- | Find whether a term performs no work whatsoever. Otherwise we don't want to
-- inline it. (See Note [exprIsWorkFree] in CoreUtils.)
termIsWorkFree :: HasId b => Term b -> Bool
termIsWorkFree = termWF 0

termWF :: HasId b => Int -> Term b -> Bool
  -- termWF n v == is v work-free when its continuation applies n value args?
termWF _ (Lit {})              = True
termWF _ (Type {})             = True
termWF _ (Coercion {})         = True
termWF n (Var x)               = isCheapApp x n
termWF n (Lam x v) | isRuntimeVar (identifier x)
                               = n == 0 || termWF (n-1) v
                   | otherwise = termWF n v
termWF n (Compute _ c)         = commWF n c

kontWF :: HasId b => Int -> Kont b -> Maybe Int
  -- kontWF n k == if ret is bound to a continuation that applies n value args,
  -- is k work-free, and if so, how many value args does it apply?
kontWF n (fs, end)
  = guard (endWF n end) >> Just (n + count isValueAppFrame fs)

endWF :: HasId b => Int -> End b -> Bool
  -- endWF n e == is e work-free when ret is bound to a continuation that
  -- applies n value args?
endWF _ Return        = True
endWF n (Case _ alts) = and [ commWF n c | Alt _ _ c <- alts ]

commWF :: HasId b => Int -> Command b -> Bool
  -- commWF n c == is c work-free when ret is bound to a continuation that
  -- applies n value args?
commWF _ (Let {})      = False
commWF _ (Jump {})     = False
commWF n (Eval v fs e) = case kontWF n (fs, e) of
                             Just n' -> termWF n' v
                             Nothing -> False

-- | Decide whether a term should be bound using @case@ rather than @let@.
-- See 'CoreUtils.needsCaseBinding'.
needsCaseBinding :: Type -> Term b -> Bool
needsCaseBinding ty rhs
  = Type.isUnLiftedType ty && not (termOkForSpeculation rhs)

termOkForSpeculation,    termOkForSideEffects    :: Term b    -> Bool
commandOkForSpeculation, commandOkForSideEffects :: Command b -> Bool

-- | Find whether a term is safe to evaluate eagerly. See comments on
-- exprOkForSpeculation in CoreUtils.
termOkForSpeculation = termOk primOpOkForSpeculation
-- | Find whether a term is free of side effects from primops.
termOkForSideEffects = termOk primOpOkForSideEffects

-- | Find whether a command is safe to execute eagerly. See comments on
-- exprOkForSpeculation in CoreUtils.
commandOkForSpeculation = commOk primOpOkForSpeculation
-- | Find whether a command is free of side effects from primops.
commandOkForSideEffects = commOk primOpOkForSideEffects

termOk :: (PrimOp -> Bool) -> Term b -> Bool
termOk primOpOk (Var id)         = appOk primOpOk id []
termOk primOpOk (Compute _ comm) = commOk primOpOk comm
termOk _ _                       = True

commOk :: (PrimOp -> Bool) -> Command b -> Bool
commOk primOpOk (Eval term fs end) = cutOk primOpOk term fs end
commOk _ _                         = False

cutOk :: (PrimOp -> Bool) -> Term b -> [Frame b] -> End b -> Bool
cutOk primOpOk (Var fid) frames end
  | (args, frames') <- collectArgs frames
  = appOk primOpOk fid args && kontOk primOpOk (frames', end)
cutOk primOpOk term frames end
  = termOk primOpOk term && kontOk primOpOk (frames, end)

kontOk :: (PrimOp -> Bool) -> Kont b -> Bool
kontOk primOpOk (frames, end) = all frameOk frames && endOk primOpOk end

frameOk :: Frame b -> Bool
frameOk (App (Type _)) = True
frameOk (App _)   = False
frameOk (Tick ti) = not (tickishCounts ti)
frameOk (Cast _)  = True

endOk :: (PrimOp -> Bool) -> End b -> Bool
endOk _ Return = True
endOk primOpOk (Case _bndr alts)
  =  all (\(Alt _ _ rhs) -> commOk primOpOk rhs) alts
  && altsAreExhaustive
  where
    altsAreExhaustive
      | (Alt con1 _ _ : _) <- alts
      = case con1 of
          DEFAULT    -> True
          LitAlt {}  -> False
          DataAlt dc -> length alts == tyConFamilySize (dataConTyCon dc)
      | otherwise
      = False

-- See comments in CoreUtils.app_ok
appOk :: (PrimOp -> Bool) -> Id -> [Term b] -> Bool
appOk primOpOk fid args
  = case idDetails fid of
      DFunId _ newType -> not newType
      DataConWorkId {} -> True
      PrimOpId op      | isDivOp op
                       , [arg1, Lit lit] <- args
                       -> not (isZeroLit lit) && termOk primOpOk arg1
                       | DataToTagOp <- op
                       -> True
                       | otherwise
                       -> primOpOk op && all (termOk primOpOk) args
      _                -> Type.isUnLiftedType (idType fid)
                       || idArity fid > nValArgs
                       || nValArgs == 0 && isEvaldUnfolding (idUnfolding fid)
                       where
                         nValArgs = length (filter isValueArg args)
  where
    isDivOp IntQuotOp        = True
    isDivOp IntRemOp         = True
    isDivOp WordQuotOp       = True
    isDivOp WordRemOp        = True
    isDivOp FloatDivOp       = True
    isDivOp DoubleDivOp      = True
    isDivOp _                = False

termIsCheap, termIsExpandable :: HasId b => Term b -> Bool
-- | See comments on exprIsCheap in CoreUtils.
termIsCheap      = termCheap isCheapApp
-- | See comments on exprIsExpandable in CoreUtils.
termIsExpandable = termCheap isExpandableApp

commandIsCheap, commandIsExpandable :: HasId b => Command b -> Bool
-- | See comments on exprIsCheap in CoreUtils.
commandIsCheap      = commCheap isCheapApp
-- | See comments on exprIsExpandable in CoreUtils.
commandIsExpandable = commCheap isExpandableApp

-- | A type for predicates that determine whether an application is cheap, given
-- the id of the function and the number of value arguments. See 'termIsCheapBy'
-- and 'commandIsCheapBy'.
type CheapAppMeasure = Id -> Int -> Bool

termCheap :: HasId b => CheapAppMeasure -> Term b -> Bool
termCheap _        (Lit _)      = True
termCheap _        (Var _)      = True
termCheap _        (Type _)     = True
termCheap _        (Coercion _) = True
termCheap appCheap (Lam x t)    = isRuntimeVar (identifier x)
                               || termCheap appCheap t
termCheap appCheap (Compute _ c)= commCheap appCheap c

kontCheap :: HasId b => CheapAppMeasure -> Kont b -> Bool
kontCheap appCheap (frames, end) = all frameCheap frames && endCheap appCheap end

frameCheap :: HasId b => Frame b -> Bool
frameCheap (App arg) = isTyCoArg arg
frameCheap (Cast _)  = True
frameCheap (Tick ti) = not (tickishCounts ti)

endCheap :: HasId b => CheapAppMeasure -> End b -> Bool
endCheap _        Return        = True
endCheap appCheap (Case _ alts) = and [commCheap appCheap rhs | Alt _ _ rhs <- alts]

commCheap :: HasId b => CheapAppMeasure -> Command b -> Bool
commCheap appCheap (Let bind comm)
  = all (bindPairCheap appCheap) (flattenBind bind) && commCheap appCheap comm
commCheap appCheap (Eval term fs end)
  = cutCheap appCheap term fs end
commCheap appCheap (Jump args j)
  = appCheap j (length (filter isValueArg args))
  
bindPairCheap :: HasId b => CheapAppMeasure -> BindPair b -> Bool
bindPairCheap appCheap (BindTerm _ term) = termCheap appCheap term
bindPairCheap _        (BindJoin _ _   ) = True

-- See the last clause in CoreUtils.exprIsCheap' for explanations

cutCheap :: HasId b => CheapAppMeasure -> Term b -> [Frame b] -> End b -> Bool
cutCheap appCheap term (Cast _ : fs) end
  = cutCheap appCheap term fs end
cutCheap appCheap (Var fid) fs@(App {} : _) end
  = case collectTypeAndOtherArgs fs of
      (_, [], fs')   -> kontCheap appCheap (fs', end)
      (_, args, fs')
        | appCheap fid (length args)
        -> papCheap args && kontCheap appCheap (fs', end)
        | otherwise
        -> case idDetails fid of
             RecSelId {}  -> selCheap args
             ClassOpId {} -> selCheap args
             PrimOpId op  -> primOpCheap op args
             _            | isBottomingId fid -> True
                          | otherwise         -> False
  where
    papCheap args       = all (termCheap appCheap) args
    selCheap [arg]      = termCheap appCheap arg
    selCheap _          = False
    primOpCheap op args = primOpIsCheap op && all (termCheap appCheap) args
cutCheap appCheap _ [] end = endCheap appCheap end
cutCheap _ _ _ _ = False
    
isCheapApp, isExpandableApp :: CheapAppMeasure
-- | The default cheapness predicate used by 'termIsCheap' and 'commandIsCheap'.
isCheapApp fid valArgCount = isDataConWorkId fid
                           || valArgCount == 0
                           || valArgCount < idArity fid
-- | The default cheapness predicate used by 'termIsExpandable' and
-- 'commandIsExpandable'.
isExpandableApp fid valArgCount = isConLikeId fid
                                || valArgCount < idArity fid
                                || allPreds valArgCount (idType fid)
  where
    allPreds 0 _ = True
    allPreds n ty
      | Just (_, ty') <- Type.splitForAllTy_maybe ty = allPreds n ty'
      | Just (argTy, ty') <- Type.splitFunTy_maybe ty
      , Type.isPredTy argTy = allPreds (n-1) ty'
      | otherwise = False

-- | Call 'termIsCheap' using an alternative cheapness predicate.
termIsCheapBy    :: HasId b => CheapAppMeasure -> Term b    -> Bool
-- | Call 'commandIsCheap' using an alternative cheapness predicate.
commandIsCheapBy :: HasId b => CheapAppMeasure -> Command b -> Bool

termIsCheapBy    = termCheap
commandIsCheapBy = commCheap

--------------------------------------------------------------------------------
-- Continuation ids
--------------------------------------------------------------------------------

-- | Find whether an id is a join id.
isJoinId :: Id -> Bool
isJoinId x = isKontTy (idType x)

-- | Find the type of the argument to a continuation of the given type. For a
-- join point, this will be either an unboxed tuple or an unboxed existential
-- (a fiction of Sequent Core; see "Language.SequentCore.WiredIn").
kontTyArg :: Type -> Type
kontTyArg ty = isKontTy_maybe ty `orElse` pprPanic "kontTyArg" (ppr ty)

--------------------------------------------------------------------------------
-- Alpha-Equivalence
--------------------------------------------------------------------------------

-- | Find whether two terms are obviously equal, expending minimal effort.
cheapEqTerm    :: Term b -> Term b -> Bool
-- | Find whether two frames are obviously equal, expending minimal effort.
cheapEqFrame   :: Frame b -> Frame b -> Bool
-- | Find whether two commands are obviously equal, expending minimal effort.
cheapEqCommand :: Command b -> Command b -> Bool

cheapEqTerm (Var v1)   (Var v2)   = v1==v2
cheapEqTerm (Lit lit1) (Lit lit2) = lit1 == lit2
cheapEqTerm (Type t1)  (Type t2)  = t1 `eqType` t2
cheapEqTerm (Coercion c1) (Coercion c2) = c1 `coreEqCoercion` c2
cheapEqTerm _             _             = False

cheapEqFrame (App a1) (App a2)   = a1 `cheapEqTerm` a2
cheapEqFrame (Cast t1) (Cast t2) = t1 `coreEqCoercion` t2
cheapEqFrame _ _ = False

cheapEqCommand (Eval v1 fs1 Return) (Eval v2 fs2 Return)
  = cheapEqTerm v1 v2 && and (zipWith cheapEqFrame fs1 fs2)
cheapEqCommand _                    _
  = False

-- | A class of types that contain an identifier. Useful so that we can compare,
-- say, elements of @Command b@ for any @b@ that wraps an identifier with
-- additional information.
class HasId a where
  -- | The identifier contained by the type @a@.
  identifier :: a -> Id
  
  -- | Extract the identifiers from a list of @a@.
  identifiers :: [a] -> [Id]
  identifiers = map identifier

instance HasId Var where
  identifier x = x
  identifiers xs = xs

-- | The type of the environment of an alpha-equivalence comparison. Only needed
-- by user code if two terms need to be compared under some assumed
-- correspondences between free variables. See GHC's 'VarEnv' module for
-- operations.
type AlphaEnv = RnEnv2

infix 4 =~=, `aeq`

-- | The class of types that can be compared up to alpha-equivalence.
class AlphaEq a where
  -- | True if the two given terms are the same, up to renaming of bound
  -- variables.
  aeq :: a -> a -> Bool
  -- | True if the two given terms are the same, up to renaming of bound
  -- variables and the specified equivalences between free variables.
  aeqIn :: AlphaEnv -> a -> a -> Bool

  aeq = aeqIn emptyAlphaEnv

-- | An empty context for alpha-equivalence comparisons.
emptyAlphaEnv :: AlphaEnv
emptyAlphaEnv = mkRnEnv2 emptyInScopeSet

-- | True if the two given terms are the same, up to renaming of bound
-- variables.
(=~=) :: AlphaEq a => a -> a -> Bool
(=~=) = aeq

instance HasId b => AlphaEq (Term b) where
  aeqIn _ (Lit l1) (Lit l2)
    = l1 == l2
  aeqIn env (Lam b1 t1) (Lam b2 t2)
    = aeqIn (rnBndr2 env (identifier b1) (identifier b2)) t1 t2
  aeqIn env (Type t1) (Type t2)
    = aeqIn env t1 t2
  aeqIn env (Coercion co1) (Coercion co2)
    = aeqIn env co1 co2
  aeqIn env (Var x1) (Var x2)
    = env `rnOccL` x1 == env `rnOccR` x2
  aeqIn env (Compute ty1 c1) (Compute ty2 c2)
    = ty1 `Type.eqType` ty2 && aeqIn env c1 c2
  aeqIn _ _ _
    = False

instance HasId b => AlphaEq (Frame b) where
  aeqIn env (App v1) (App v2)
    = aeqIn env v1 v2
  aeqIn env (Cast co1) (Cast co2)
    = aeqIn env co1 co2
  aeqIn _   (Tick ti1) (Tick ti2)
    = ti1 == ti2
  aeqIn _ _ _
    = False
    
instance HasId b => AlphaEq (End b) where
  aeqIn _ Return Return
    = True
  aeqIn env (Case x1 as1) (Case x2 as2) 
    = aeqIn env' as1 as2
      where env' = rnBndr2 env (identifier x1) (identifier x2)
  aeqIn _ _ _
    = False

instance HasId b => AlphaEq (Join b) where
  aeqIn env (Join xs1 c1) (Join xs2 c2)
    = aeqIn env' c1 c2
      where env' = rnBndrs2 env (identifiers xs1) (identifiers xs2)

instance HasId b => AlphaEq (Command b) where
  aeqIn env (Let bind1 comm1) (Let bind2 comm2)
    | Just env' <- aeqBindIn env bind1 bind2
    = aeqIn env' comm1 comm2
  aeqIn env (Eval v1 fs1 e1) (Eval v2 fs2 e2)
    = aeqIn env v1 v2 && aeqIn env fs1 fs2 && aeqIn env e1 e2
  aeqIn env (Jump vs1 j1) (Jump vs2 j2)
    = aeqIn env vs1 vs2 && env `rnOccL` j1 == env `rnOccR` j2
  aeqIn _ _ _
    = False


-- | If the given bindings are alpha-equivalent, returns an augmented environment
-- tracking the correspondences between the bound variables.
aeqBindIn :: HasId b => AlphaEnv -> Bind b -> Bind b -> Maybe AlphaEnv
aeqBindIn env (NonRec pair1) (NonRec pair2)
  = aeqBindPairsIn env [pair1] [pair2]
aeqBindIn env (Rec pairs1) (Rec pairs2)
  = aeqBindPairsIn env pairs1 pairs2
aeqBindIn _ _ _
  = Nothing

aeqBindPairsIn :: HasId b => AlphaEnv -> [BindPair b] -> [BindPair b]
               -> Maybe AlphaEnv
aeqBindPairsIn env pairs1 pairs2
  = if alpha pairs1 pairs2 then Just env' else Nothing
  where
    alpha (BindTerm _ term1 : pairs1) (BindTerm _ term2 : pairs2)
      = aeqIn env' term1 term2 && alpha pairs1 pairs2
    alpha (BindJoin _ join1 : pairs1) (BindJoin _ join2 : pairs2)
      = aeqIn env' join1 join2 && alpha pairs1 pairs2
    alpha [] []
      = True
    alpha _  _
      = False
    env'
      = rnBndrs2 env (identifiers (map binderOfPair pairs1))
                     (identifiers (map binderOfPair pairs2))

instance HasId b => AlphaEq (Alt b) where
  aeqIn env (Alt a1 xs1 c1) (Alt a2 xs2 c2)
    = a1 == a2 && aeqIn env' c1 c2
    where
      env' = rnBndrs2 env (map identifier xs1) (map identifier xs2)

instance AlphaEq Type where
  aeqIn env t1 t2
    | Just x1 <- Type.getTyVar_maybe t1
    , Just x2 <- Type.getTyVar_maybe t2
    = env `rnOccL` x1 == env `rnOccR` x2
    | Just (f1, a1) <- Type.splitAppTy_maybe t1
    , Just (f2, a2) <- Type.splitAppTy_maybe t2
    = f1 `alpha` f2 && a1 `alpha` a2
    | Just n1 <- Type.isNumLitTy t1
    , Just n2 <- Type.isNumLitTy t2
    = n1 == n2
    | Just s1 <- Type.isStrLitTy t1
    , Just s2 <- Type.isStrLitTy t2
    = s1 == s2
    | Just (a1, r1) <- Type.splitFunTy_maybe t1
    , Just (a2, r2) <- Type.splitFunTy_maybe t2
    = a1 `alpha` a2 && r1 `alpha` r2
    | Just (c1, as1) <- Type.splitTyConApp_maybe t1
    , Just (c2, as2) <- Type.splitTyConApp_maybe t2
    = c1 == c2 && as1 `alpha` as2
    | Just (x1, t1') <- Type.splitForAllTy_maybe t1
    , Just (x2, t2') <- Type.splitForAllTy_maybe t2
    = aeqIn (rnBndr2 env x1 x2) t1' t2'
    | otherwise
    = False
    where
      alpha a1 a2 = aeqIn env a1 a2

instance AlphaEq Coercion where
  -- Consider coercions equal if their types are equal (proof irrelevance)
  aeqIn env co1 co2 = aeqIn env (coercionType co1) (coercionType co2)
    
instance AlphaEq a => AlphaEq [a] where
  aeqIn env xs ys = and $ zipWith (aeqIn env) xs ys

instance (AlphaEq a, AlphaEq b) => AlphaEq (Either a b) where
  aeqIn env (Left x)  (Left y)  = aeqIn env x y
  aeqIn env (Right x) (Right y) = aeqIn env x y
  aeqIn _   _         _         = False

instance HasId b => AlphaEq (Bind b) where
  aeqIn env b1 b2 = isJust $ aeqBindIn env b1 b2

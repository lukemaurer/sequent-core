{-
%
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[FloatOut]{Float bindings outwards (towards the top level)}

``Long-distance'' floating of bindings towards the top level.

-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://ghc.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details
{-# LANGUAGE CPP #-}

module Language.SequentCore.FloatOut ( floatOutwards, plugin ) where

import Language.SequentCore.Arity
import Language.SequentCore.FloatOut.Flags
import Language.SequentCore.FloatOut.SetLevels
import Language.SequentCore.Plugin
import Language.SequentCore.Syntax
import Language.SequentCore.Syntax.Util

import CoreSyn          ( tickishScoped, mkNoCount )
import CoreMonad        ( FloatOutSwitches(..)
                        , CoreM, CoreToDo(..), Plugin(..)
                        , defaultPlugin, reinitializeGlobals )
import DynFlags
import HscTypes         ( ModGuts(..) )
import ErrUtils         ( dumpIfSet_dyn, errorMsg )
import Id               ( Id, idArity, isBottomingId )
import Var              ( Var )
import UniqSupply       ( UniqSupply, getUniqueSupplyM )
import Bag
import Util
import Maybes
import Outputable
import FastString
import MonadUtils       ( liftIO )

import Control.Applicative ( (<$>), (<*>), pure )
import Control.Monad
import Control.Monad.Trans.Writer.Lazy
import qualified Data.IntMap as M
import Data.Monoid

#define ASSERT(e)      if debugIsOn && not (e) then (assertPanic __FILE__ __LINE__) else
#define ASSERT2(e,msg) if debugIsOn && not (e) then (assertPprPanic __FILE__ __LINE__ (msg)) else
#define WARN( e, msg ) (warnPprTrace (e) __FILE__ __LINE__ (msg)) $

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = \cmdLine todos -> do
    reinitializeGlobals
    let cmdLine' = concatMap words cmdLine
          -- Allow -fplugin-opt=plugin:"opt1 opt2"
    (fflags, leftovers, warns) <- parseFloatFlags cmdLine'
    dflags <- getDynFlags
    unless (null leftovers) $
      liftIO $ errorMsg dflags $
        text "Leftover options to Language.SequentCore.FloatOut:" $$
        vcat (map text leftovers)
    unless (null warns) $
      liftIO $ errorMsg dflags $ vcat (map text warns)
    let todos' = replace fflags todos
    return todos'
} where
  replace fflags = go
    where
      go (CoreDoFloatOutwards switches : todos)
        = normalPass switches : go todos
      go (CoreDoPasses todos1 : todos2)
        = CoreDoPasses (go todos1) : go todos2
      go (todo : todos)
        = todo : go todos
      go []
        | fgopt Opt_LLF fflags
        = [finalPass]
        | otherwise
        = []

      normalPass switches
        = CoreDoPluginPass "Float out (Sequent Core)"
                           (runFloatOut switches fflags Nothing)

      finalPass
        = CoreDoPluginPass "Late lambda-lifting (Sequent Core)"
                           (runFloatOut switchesForFinal fflags
                                        (Just finalPassSwitches) )

      switchesForFinal = FloatOutSwitches
        { floatOutLambdas             = lateFloatNonRecLam fflags
        , floatOutConstants           = False
        , floatOutPartialApplications = False
        }

      finalPassSwitches = FinalPassSwitches
        { fps_trace          = doptDumpLateFloat          fflags
        , fps_stabilizeFirst = fgopt Opt_LLF_Stabilize    fflags
        , fps_rec            = lateFloatRecLam            fflags
        , fps_absUnsatVar    = fgopt Opt_LLF_AbsUnsat     fflags
        , fps_absSatVar      = fgopt Opt_LLF_AbsSat       fflags
        , fps_absOversatVar  = fgopt Opt_LLF_AbsOversat   fflags
        , fps_createPAPs     = fgopt Opt_LLF_CreatePAPs   fflags
        , fps_ifInClo        = lateFloatIfInClo           fflags
        , fps_cloGrowth      = lateFloatCloGrowth         fflags
        , fps_cloGrowthInLam = lateFloatCloGrowthInLam    fflags
        , fps_strictness     = fgopt Opt_LLF_UseStr       fflags
        , fps_oneShot        = fgopt Opt_LLF_OneShot      fflags
        }

runFloatOut :: FloatOutSwitches -> FloatFlags -> Maybe FinalPassSwitches
            -> ModGuts
            -> CoreM ModGuts
runFloatOut switches fflags final guts
  = do
    dflags <- getDynFlags
    us <- getUniqueSupplyM
    sequentPass (liftIO . floatOutwards switches final dflags fflags us) guts

{-
        -----------------
        Overall game plan
        -----------------

The Big Main Idea is:

        To float out sub-expressions that can thereby get outside
        a non-one-shot value lambda, and hence may be shared.


To achieve this we may need to do two thing:

   a) Let-bind the sub-expression:

        f (g x)  ==>  let lvl = f (g x) in lvl

      Now we can float the binding for 'lvl'.  

   b) More than that, we may need to abstract wrt a type variable

        \x -> ... /\a -> let v = ...a... in ....

      Here the binding for v mentions 'a' but not 'x'.  So we
      abstract wrt 'a', to give this binding for 'v':

            vp = /\a -> ...a...
            v  = vp a

      Now the binding for vp can float out unimpeded.
      I can't remember why this case seemed important enough to
      deal with, but I certainly found cases where important floats
      didn't happen if we did not abstract wrt tyvars.

With this in mind we can also achieve another goal: lambda lifting.
We can make an arbitrary (function) binding float to top level by
abstracting wrt *all* local variables, not just type variables, leaving
a binding that can be floated right to top level.  Whether or not this
happens is controlled by a flag.


Random comments
~~~~~~~~~~~~~~~

At the moment we never float a binding out to between two adjacent
lambdas.  For example:

@
        \x y -> let t = x+x in ...
===>
        \x -> let t = x+x in \y -> ...
@
Reason: this is less efficient in the case where the original lambda
is never partially applied.

But there's a case I've seen where this might not be true.  Consider:
@
elEm2 x ys
  = elem' x ys
  where
    elem' _ []  = False
    elem' x (y:ys)      = x==y || elem' x ys
@
It turns out that this generates a subexpression of the form
@
        \deq x ys -> let eq = eqFromEqDict deq in ...
@
vwhich might usefully be separated to
@
        \deq -> let eq = eqFromEqDict deq in \xy -> ...
@
Well, maybe.  We don't do this at the moment.


%************************************************************************
%*                                                                      *
\subsection[floatOutwards]{@floatOutwards@: let-floating interface function}
%*                                                                      *
%************************************************************************

-}
floatOutwards :: FloatOutSwitches
              -> Maybe FinalPassSwitches
              -> DynFlags
              -> FloatFlags
              -> UniqSupply
              -> SeqCoreProgram -> IO SeqCoreProgram

floatOutwards float_sws fps dflags fflags us pgm
  = do {
        let { annotated_w_levels = setLevels dflags fflags float_sws fps pgm us ;
              (fss, binds_s')    = unzip (map floatTopBind annotated_w_levels)
            } ;

        dumpIfSet_dyn dflags Opt_D_verbose_core2core "Levels added:"
                  (vcat (map ppr annotated_w_levels));

        let { (tlets, ntlets, lams) = get_stats (sum_stats fss) };

        dumpIfSet_dyn dflags Opt_D_dump_simpl_stats "FloatOut stats:"
            (hcat [ int tlets,  ptext (sLit " Lets floated to top level; "),
                    int ntlets, ptext (sLit " Lets floated elsewhere; from "),
                    int lams,   ptext (sLit " Lambda groups")]);

        return (bagToList (unionManyBags binds_s'))
    }

floatTopBind :: Levelled Bind -> (FloatStats, Bag SeqCoreBind)
floatTopBind bind
  = case runFloatM (floatBind bind) of { (fs, floats, bind') ->
    let float_bag = flattenTopFloats floats
    in case bind' of
      Rec prs   -> (fs, unitBag (Rec (addTopFloatPairs float_bag prs)))
      NonRec {} -> (fs, float_bag `snocBag` bind') }

{-
%************************************************************************
%*                                                                      *
\subsection[FloatOut-Bind]{Floating in a binding (the business end)}
%*                                                                      *
%************************************************************************
-}

type FloatM = Writer (FloatStats, FloatBinds)

runFloatM :: FloatM a -> (FloatStats, FloatBinds, a)
runFloatM m = case runWriter m of (a, (fs, binds)) -> (fs, binds, a)

captureFloats :: FloatM a -> FloatM (FloatBinds, a)
captureFloats m = writer $ case runWriter m of { (a, (stats, floats)) ->
                           ((floats, a), (stats, emptyFloats)) }

emitFloats :: FloatBinds -> FloatM ()
emitFloats binds = writer ((), (zeroStats, binds))

emitLetBind :: Level -> FloatLet -> FloatM ()
emitLetBind lvl bind = emitFloats (unitLetFloat lvl bind)

-- Run an action, then remove the floated bindings of at least the given level
-- and return them with the result, keeping the lesser-level bindings in the output
captureFloatsAtLevel :: Level -> FloatM a -> FloatM (Bag FloatBind, a)
captureFloatsAtLevel lvl m
  = writer $ case runWriter m of { (a, (stats, floats)) ->
             case partitionByLevel lvl floats of { (floats', heres) ->
             ((heres, a), (stats, floats')) }}

addingToStats :: FloatM a -> FloatM a
addingToStats m
  = writer $ case runWriter m of { (a, (fs, floats)) ->
             (a, (add_to_stats fs floats, floats)) }

floatBind :: Levelled Bind -> FloatM SeqCoreBind
floatBind (NonRec pair)
  = do
    let (TB var _) = binderOfPair pair
    pair' <- floatRhs pair
        -- A tiresome hack: 
        -- see Note [Bottoming floats: eta expansion] in SetLevels
    let pair'' | isBottomingId var = etaExpandRhs (idArity var) pair'
               | otherwise         = pair'

    return $ NonRec pair''

floatBind (Rec pairs)
  = mapM do_pair pairs >>= \new_pairs ->
    return $ Rec (concat new_pairs)
  where
    do_pair pair
      | isTopLvl dest_lvl  -- See Note [floatBind for top level]
      = captureFloats (floatRhs pair) >>= \(rhs_floats, pair') ->
        return $ addTopFloatPairs (flattenTopFloats rhs_floats) [pair']
      | otherwise         -- Note [Floating out of Rec rhss]
      = captureFloatsAtLevel dest_lvl (floatRhs pair) >>= \(heres, pair') ->
        case (splitRecFloats heres) of { (pairs, case_heres) -> do
        return $ installUnderLambdas case_heres pair' : pairs }
      where
        TB _name spec = binderOfPair pair
        dest_lvl = floatSpecLevel spec

splitRecFloats :: Bag FloatBind -> ([SeqCoreBindPair], Bag FloatBind)
-- The "tail" begins with a case
-- See Note [Floating out of Rec rhss]
splitRecFloats fs
  = go [] (bagToList fs)
  where
    go prs (FloatLet (NonRec pair) : fs) = go (pair:prs) fs
    go prs (FloatLet (Rec prs')    : fs) = go (prs' ++ prs) fs
    go prs fs                            = (prs, listToBag fs)

installUnderLambdas :: Bag FloatBind -> SeqCoreBindPair -> SeqCoreBindPair
-- Note [Floating out of Rec rhss]
installUnderLambdas floats pair
  | isEmptyBag floats = pair
installUnderLambdas floats (BindJoin bndr (Join bndrs comm))
  = BindJoin bndr (Join bndrs (installInCommand floats comm))
installUnderLambdas floats (BindTerm bndr term)
  = BindTerm bndr (go term)
  where
    go (Lam b e)                 = Lam b (go e)
    go e                         = installInTerm floats e

floatRhs :: Levelled BindPair -> FloatM SeqCoreBindPair
floatRhs (BindTerm (TB bndr _) term)
  = BindTerm bndr <$> floatTerm term
floatRhs (BindJoin (TB bndr _) join)
  = BindJoin bndr <$> floatJoin join

{-
Note [Floating out of Rec rhss]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider   Rec { f<1,0> = \xy. body }
From the body we may get some floats. The ones with level <1,0> must
stay here, since they may mention f.  Ideally we'd like to make them
part of the Rec block pairs -- but we can't if there are any
FloatCases involved.  

Nor is it a good idea to dump them in the rhs, but outside the lambda
    f = case x of I# y -> \xy. body
because now f's arity might get worse, which is Not Good. (And if
there's an SCC around the RHS it might not get better again.  
See Trac #5342.)

So, gruesomely, we split the floats into 
 * the outer FloatLets, which can join the Rec, and 
 * an inner batch starting in a FloatCase, which are then
   pushed *inside* the lambdas.  
This loses full-laziness the rare situation where there is a 
FloatCase and a Rec interacting.

Note [floatBind for top level]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We may have a *nested* binding whose destination level is (FloatMe tOP_LEVEL), thus
         letrec { foo <0,0> = .... (let bar<0,0> = .. in ..) .... }
The binding for bar will be in the "tops" part of the floating binds,
and thus not partioned by floatBody.  

We could perhaps get rid of the 'tops' component of the floating binds,
but this case works just as well.


%************************************************************************

\subsection[FloatOut-Expr]{Floating in expressions}
%*                                                                      *
%************************************************************************
-}

floatBodyComm :: Level
              -> Levelled Command
              -> FloatM SeqCoreCommand

floatBodyComm lvl comm      -- Used case-alternative rhss
  = captureFloatsAtLevel lvl (floatComm comm) >>= \(heres, comm') ->
    return $ installInCommand heres comm'

floatBodyTerm :: Level
             -> Levelled Term
             -> FloatM SeqCoreTerm
floatBodyTerm lvl term      -- Used rec rhss
 = captureFloatsAtLevel lvl (floatTerm term) >>= \(heres, term') ->
   return $ installInTerm heres term'

-----------------
floatTerm :: Levelled Term
          -> FloatM SeqCoreTerm
floatTerm (Var v)   = return $ Var v
floatTerm (Type ty) = return $ Type ty
floatTerm (Coercion co) = return $ Coercion co
floatTerm (Lit lit) = return $ Lit lit

floatTerm lam@(Lam (TB _ lam_spec) _)
  = do
    let (bndrs_w_lvls, body) = collectBinders lam
        bndrs                = [b | TB b _ <- bndrs_w_lvls]
        bndr_lvl             = floatSpecLevel lam_spec
        -- All the binders have the same level
        -- See SetLevels.lvlLamBndrs
    body' <- addingToStats $ floatBodyTerm bndr_lvl body
    return $ mkLambdas bndrs body'

floatTerm (Compute ty comm)
  = Compute ty <$> floatComm comm

floatComm :: Levelled Command
          -> FloatM SeqCoreCommand
floatComm (Let bind body)
  = case bind_spec of
      FloatMe dest_lvl 
        -> do
           bind' <- floatBind bind
           emitLetBind dest_lvl bind'
           body' <- floatComm body
           return body'

      StayPut bind_lvl  -- See Note [Avoiding unnecessary floating]
        -> Let <$> floatBind bind <*> floatBodyComm bind_lvl body
  where
    bind_spec = case bindersOf bind of
                     TB _ s : _  -> s
                     _           -> panic "floatTerm"

floatComm (Eval term frames end)
  = doEnd end
  where
    doEnd Return = do
                   (term', frames') <- doFrames
                   return $ Eval term' frames' Return
    doEnd (Case (TB case_bndr case_spec) alts)
      = case case_spec of
          FloatMe dest_lvl  -- Case expression moves
            | [Alt con@(DataAlt {}) bndrs rhs] <- alts
            -> do
               (term', frames') <- doFrames
               let scrut' = mkComputeEval term' frames'
                   float = unitCaseFloat dest_lvl scrut'
                                case_bndr con [b | TB b _ <- bndrs]
               emitFloats float
               floatComm rhs
            | otherwise
            -> pprPanic "Floating multi-case" (ppr alts)
          StayPut bind_lvl  -- Case expression stays put
            -> do
               (term', frames') <- doFrames
               end' <- Case case_bndr <$> mapM (float_alt bind_lvl) alts
               return $ Eval term' frames' end'
      where
        float_alt bind_lvl (Alt con bs rhs)
          = Alt con [b | TB b _ <- bs] <$> floatBodyComm bind_lvl rhs
            
    doFrames = go (reverse frames) []
                 -- In reverse because a tick influences the floats that come
                 -- from the term and the frames *before* it (remember that our
                 -- representation is "upside-down" from Core).
      where
        go :: [Levelled Frame] -- in reverse
           -> [SeqCoreFrame] -> FloatM (SeqCoreTerm, [SeqCoreFrame])
        go [] acc
          = do
            term' <- floatTerm term
            return (term', acc)
        go (App arg : fs_rev) acc
          = do
            arg' <- floatTerm arg
            go fs_rev (App arg' : acc)
        go (Cast co : fs_rev) acc
          = go fs_rev (Cast co : acc)
        go (Tick ti : fs_rev) acc
          | tickishScoped ti
          = do
            (floats, (term', fs')) <- captureFloats $ go fs_rev (Tick ti : acc)
            -- Annotate bindings floated outwards past an scc expression
            -- with the cc.  We mark that cc as "duplicated", though.
            let annotated_floats = wrapTick (mkNoCount ti) floats
            emitFloats annotated_floats
            return (term', fs')
          | otherwise  -- not scoped, can just float
          = go fs_rev (Tick ti : acc)
                               
floatComm (Jump args j)
  = Jump <$> mapM floatTerm args <*> pure j

floatJoin :: Levelled Join -> FloatM SeqCoreJoin
floatJoin (Join bndrs_w_lvls@(TB _ lam_spec : _) body)
  = do
    let bndrs                = [b | TB b _ <- bndrs_w_lvls]
        bndr_lvl             = floatSpecLevel lam_spec
        -- All the binders have the same level
        -- See SetLevels.lvlLamBndrs
    body' <- addingToStats $ floatBodyComm bndr_lvl body
    return $ Join bndrs body'

floatJoin (Join [] body)
  = Join [] <$> floatComm body

{-
Note [Avoiding unnecessary floating]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In general we want to avoid floating a let unnecessarily, because
it might worsen strictness:
    let 
       x = ...(let y = e in y+y)....
Here y is demanded.  If we float it outside the lazy 'x=..' then
we'd have to zap its demand info, and it may never be restored.

So at a 'let' we leave the binding right where the are unless
the binding will escape a value lambda, e.g.  

(\x -> let y = fac 100 in y)

That's what the partitionByMajorLevel does in the floatTerm (Let ...)
case.

Notice, though, that we must take care to drop any bindings
from the body of the let that depend on the staying-put bindings.

We used instead to do the partitionByMajorLevel on the RHS of an '=',
in floatRhs.  But that was quite tiresome.  We needed to test for
values or trival rhss, because (in particular) we don't want to insert
new bindings between the "=" and the "\".  E.g.
        f = \x -> let <bind> in <body>
We do not want
        f = let <bind> in \x -> <body>
(a) The simplifier will immediately float it further out, so we may
        as well do so right now; in general, keeping rhss as manifest 
        values is good
(b) If a float-in pass follows immediately, it might add yet more
        bindings just after the '='.  And some of them might (correctly)
        be strict even though the 'let f' is lazy, because f, being a value,
        gets its demand-info zapped by the simplifier.
And even all that turned out to be very fragile, and broke
altogether when profiling got in the way.

So now we do the partition right at the (Let..) itself.

%************************************************************************
%*                                                                      *
\subsection{Utility bits for floating stats}
%*                                                                      *
%************************************************************************

I didn't implement this with unboxed numbers.  I don't want to be too
strict in this stuff, as it is rarely turned on.  (WDP 95/09)
-}

data FloatStats
  = FlS Int  -- Number of top-floats * lambda groups they've been past
        Int  -- Number of non-top-floats * lambda groups they've been past
        Int  -- Number of lambda (groups) seen

get_stats :: FloatStats -> (Int, Int, Int)
get_stats (FlS a b c) = (a, b, c)

zeroStats :: FloatStats
zeroStats = FlS 0 0 0

sum_stats :: [FloatStats] -> FloatStats
sum_stats xs = foldr add_stats zeroStats xs

add_stats :: FloatStats -> FloatStats -> FloatStats
add_stats (FlS a1 b1 c1) (FlS a2 b2 c2)
  = FlS (a1 + a2) (b1 + b2) (c1 + c2)

add_to_stats :: FloatStats -> FloatBinds -> FloatStats
add_to_stats (FlS a b c) (FB tops others)
  = FlS (a + lengthBag tops) (b + lengthBag (flattenMajor others)) (c + 1)

instance Monoid FloatStats where
  mempty  = zeroStats
  mappend = add_stats
  mconcat = sum_stats

{-
%************************************************************************
%*                                                                      *
\subsection{Utility bits for floating}
%*                                                                      *
%************************************************************************

Note [Representation of FloatBinds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The FloatBinds types is somewhat important.  We can get very large numbers
of floating bindings, often all destined for the top level.  A typical example
is     x = [4,2,5,2,5, .... ]
Then we get lots of small expressions like (fromInteger 4), which all get
lifted to top level.  

The trouble is that  
  (a) we partition these floating bindings *at every binding site* 
  (b) SetLevels introduces a new bindings site for every float
So we had better not look at each binding at each binding site!

That is why MajorEnv is represented as a finite map.

We keep the bindings destined for the *top* level separate, because
we float them out even if they don't escape a *value* lambda; see
partitionByMajorLevel.
-}


type FloatLet = SeqCoreBind     -- INVARIANT: a FloatLet is always lifted
type MajorEnv = M.IntMap MinorEnv         -- Keyed by major level
type MinorEnv = M.IntMap (Bag FloatBind)  -- Keyed by minor level

data FloatBinds  = FB !(Bag FloatLet)           -- Destined for top level
                      !MajorEnv                 -- Levels other than top
     -- See Note [Representation of FloatBinds]

instance Outputable FloatBind where
  ppr (FloatLet b) = ptext (sLit "LET") <+> ppr b
  ppr (FloatCase e b c bs) = hang (ptext (sLit "CASE") <+> ppr e <+> ptext (sLit "of") <+> ppr b)
                                2 (ppr c <+> ppr bs)

instance Outputable FloatBinds where
  ppr (FB fbs defs) 
      = ptext (sLit "FB") <+> (braces $ vcat
           [ ptext (sLit "tops =")     <+> ppr fbs
           , ptext (sLit "non-tops =") <+> ppr defs ])

instance Monoid FloatBinds where
  mempty = emptyFloats
  mappend = plusFloats

flattenTopFloats :: FloatBinds -> Bag SeqCoreBind
flattenTopFloats (FB tops defs) 
  = ASSERT2( isEmptyBag (flattenMajor defs), ppr defs )
    tops 

addTopFloatPairs :: Bag SeqCoreBind -> [SeqCoreBindPair] -> [SeqCoreBindPair]
addTopFloatPairs float_bag prs
  = foldrBag add prs float_bag
  where
    add (NonRec pair) prs  = pair:prs
    add (Rec prs1)    prs2 = prs1 ++ prs2

flattenMajor :: MajorEnv -> Bag FloatBind
flattenMajor = M.fold (unionBags . flattenMinor) emptyBag

flattenMinor :: MinorEnv -> Bag FloatBind
flattenMinor = M.fold unionBags emptyBag

emptyFloats :: FloatBinds
emptyFloats = FB emptyBag M.empty

unitCaseFloat :: Level -> SeqCoreTerm -> Id -> AltCon -> [Var] -> FloatBinds
unitCaseFloat (Level major minor) e b con bs 
  = FB emptyBag (M.singleton major (M.singleton minor (unitBag (FloatCase e b con bs))))

unitLetFloat :: Level -> FloatLet -> FloatBinds
unitLetFloat lvl@(Level major minor) b 
  | isTopLvl lvl = FB (unitBag b) M.empty
  | otherwise    = FB emptyBag (M.singleton major (M.singleton minor floats))
  where
    floats = unitBag (FloatLet b)

plusFloats :: FloatBinds -> FloatBinds -> FloatBinds
plusFloats (FB t1 l1) (FB t2 l2) 
  = FB (t1 `unionBags` t2) (l1 `plusMajor` l2)

plusMajor :: MajorEnv -> MajorEnv -> MajorEnv
plusMajor = M.unionWith plusMinor

plusMinor :: MinorEnv -> MinorEnv -> MinorEnv
plusMinor = M.unionWith unionBags

installInTerm :: Bag FloatBind -> SeqCoreTerm -> SeqCoreTerm
installInTerm defn_groups expr
  = foldrBag wrapTermInFloat expr defn_groups

installInCommand :: Bag FloatBind -> SeqCoreCommand -> SeqCoreCommand
installInCommand defn_groups expr
  = foldrBag wrapFloat expr defn_groups

partitionByLevel
        :: Level                -- Partitioning level
        -> FloatBinds           -- Defns to be divided into 2 piles...
        -> (FloatBinds,         -- Defns  with level strictly < partition level,
            Bag FloatBind)      -- The rest

{-
--       ---- partitionByMajorLevel ----
-- Float it if we escape a value lambda, 
--     *or* if we get to the top level
--     *or* if it's a case-float and its minor level is < current
-- 
-- If we can get to the top level, say "yes" anyway. This means that 
--      x = f e
-- transforms to 
--    lvl = e
--    x = f lvl
-- which is as it should be

partitionByMajorLevel (Level major _) (FB tops defns)
  = (FB tops outer, heres `unionBags` flattenMajor inner)
  where
    (outer, mb_heres, inner) = M.splitLookup major defns
    heres = case mb_heres of 
               Nothing -> emptyBag
               Just h  -> flattenMinor h
-}

partitionByLevel (Level major minor) (FB tops defns)
  = (FB tops (outer_maj `plusMajor` M.singleton major outer_min),
     here_min `unionBags` flattenMinor inner_min 
              `unionBags` flattenMajor inner_maj)

  where
    (outer_maj, mb_here_maj, inner_maj) = M.splitLookup major defns
    (outer_min, mb_here_min, inner_min) = case mb_here_maj of
                                            Nothing -> (M.empty, Nothing, M.empty)
                                            Just min_defns -> M.splitLookup minor min_defns
    here_min = mb_here_min `orElse` emptyBag

wrapTick :: Tickish Id -> FloatBinds -> FloatBinds
wrapTick t (FB tops defns)
  = FB (mapBag wrap_bind tops) (M.map (M.map wrap_defns) defns)
  where
    wrap_defns = mapBag wrap_one 

    wrap_bind (NonRec pair)       = NonRec (wrap_pair pair)
    wrap_bind (Rec pairs)         = Rec (map wrap_pair pairs)
    
    wrap_pair (BindTerm b term)   = BindTerm b (maybe_tick term)
    wrap_pair _                   = panic "wrapTick"
    
    wrap_one (FloatLet bind)      = FloatLet (wrap_bind bind)
    wrap_one (FloatCase e b c bs) = FloatCase (maybe_tick e) b c bs

    maybe_tick e | termIsHNF e = tickHNFArgs t e
                 | otherwise   = mkTickTerm t e
      -- we don't need to wrap a tick around an HNF when we float it
      -- outside a tick: that is an invariant of the tick semantics
      -- Conversely, inlining of HNFs inside an SCC is allowed, and
      -- indeed the HNF we're floating here might well be inlined back
      -- again, and we don't want to end up with duplicate ticks.

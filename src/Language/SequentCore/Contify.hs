{-# LANGUAGE BangPatterns, CPP, FlexibleInstances, LambdaCase, MultiWayIf,
             ParallelListComp, TupleSections, TypeSynonymInstances,
             ViewPatterns #-}

-- | 
-- Module      : Language.SequentCore.Contify
-- Description : Contification pass
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Pass that turns as many functions as possible into join points.

module Language.SequentCore.Contify (
  runContify, runContifyGently,
  contifyInProgram, contifyGentlyInProgram, contifyInProgramWith,
  contifyInTerm, contifyGentlyInTerm
) where

import {-# SOURCE #-} Language.SequentCore.Translate

import Language.SequentCore.Driver.Flags
import Language.SequentCore.FVs
import Language.SequentCore.Syntax
import Language.SequentCore.Syntax.Util
import Language.SequentCore.Util
import Language.SequentCore.WiredIn

import BasicTypes ( Arity, TopLevelFlag(..), TupleSort(..)
                  , isTopLevel, isNotTopLevel )
import Bag
import CoreMonad
import CoreSubst
import CoreUnfold
import qualified CoreSyn as Core
import DynFlags
import qualified ErrUtils as Err
import FastString
import Id
import IdInfo
import Maybes
import MkId
import Outputable hiding ( (<>) )
import qualified Outputable as Out
import SrcLoc     ( noSrcSpan )
import Type hiding ( substTy )
import TysPrim
import TysWiredIn
import UniqFM     ( intersectUFM_C )
import Unique
import Util       ( count, debugIsOn )
import VarEnv
import VarSet

import Control.Applicative
import Control.Exception    ( assert )
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.Writer.Strict
import Data.IntMap          ( IntMap )
import qualified Data.IntMap as IntMap
import Data.IntSet          ( IntSet )
import qualified Data.IntSet as IntSet
import Data.List
import Data.Monoid
import Numeric

#define ASSERT(e)      if debugIsOn && not (e) then (assertPanic __FILE__ __LINE__) else
#define ASSERT2(e,msg) if debugIsOn && not (e) then (assertPprPanic __FILE__ __LINE__ (msg)) else
#define WARN( e, msg ) (warnPprTrace (e) __FILE__ __LINE__ (msg)) $
#define MASSERT(e)     ASSERT(e) return ()

tracing :: Bool
tracing = False

dumping :: Bool
dumping = False

runContify :: SeqFlags -> ContifySwitches -> SeqCoreProgram -> CoreM SeqCoreProgram
runContify sflags sw pgm
  = do
    let pgm_uniqd       = uniquifyProgram pgm
        (cst1, pgm_esc) = escAnalProgram sw pgm_uniqd
        (cst2, pgm')    = cfyInTopLevelBinds sw pgm_esc
        cst             = cst1 <> cst2
        
    dflags <- getDynFlags
    when (sdopt Opt_D_dump_cfy_stats sflags) $ liftIO $
        log_action dflags dflags Err.SevInfo noSrcSpan defaultDumpStyle $
          vcat [ blankLine, text "Contification statistics:", blankLine, ppr cst ]
    
    return pgm'
          
-- | Run contification in gentle mode, as used automatically after translation.
-- 'Language.SequentCore.Translate.fromCoreModule' operates by translating
-- straightforwardly, with no functions converted to join points, then calling
-- this routine. As such, it makes no special effort to maximize the number of
-- join points found. This makes the pass both faster and less disruptive. For
-- example, aggressive contification may float bindings inward, which allows
-- more join points to be created but prevents CSE from eliminating those
-- bindings entirely.
--
-- In contrast, gentle mode only contifies in place, and thus should be safe to
-- run regularly. Any pass that may cause more bindings to be contifiable may
-- benefit from running a gentle Contify pass afterward.
runContifyGently :: SeqFlags -> SeqCoreProgram -> CoreM SeqCoreProgram
runContifyGently sflags = runContify sflags gentleMode
  -- FIXME uniquifyProgram probably not necessary in gentle mode but hides bugs

contifyInProgram, contifyGentlyInProgram :: SeqCoreProgram -> SeqCoreProgram 
contifyInProgram       = contifyInProgramWith aggressiveMode
contifyGentlyInProgram = contifyInProgramWith gentleMode

contifyInProgramWith :: ContifySwitches -> SeqCoreProgram -> SeqCoreProgram
contifyInProgramWith sw pgm = snd $ cfyInTopLevelBinds sw $ snd $ escAnalProgram sw $ uniquifyProgram pgm

contifyInTerm, contifyGentlyInTerm :: SeqCoreTerm -> SeqCoreTerm
contifyInTerm       = contifyInTermWith aggressiveMode
contifyGentlyInTerm = contifyInTermWith gentleMode

contifyInTermWith :: ContifySwitches -> SeqCoreTerm -> SeqCoreTerm
contifyInTermWith sw term = snd $ runCfyM $ cfyInTerm env $ snd $ runEscM sw $ escAnalTerm $ uniquifyTerm term
  where
    env = initCfyEnvForTerm sw term

----------------
-- Statistics --
----------------

data CfyStats = CfyStats { cst_bindsTotal    :: !Int
                         , cst_bindsCfied    :: !Int
                         , cst_bindsFloated  :: !Int
                         , cst_bindsNotCfied :: !Int
                         , cst_joinBinds     :: !Int
                         , cst_scopeMismatch :: !Int
                         , cst_arityMismatch :: !Int
                         , cst_etaExpanded   :: !Int
                         , cst_splitLams     :: !Int
                         , cst_typeFixed     :: !Int
                         , cst_polyFail      :: !Int
                         , cst_dontCfyRules  :: !Int }
              | ZeroCfyStats

emptyCfyStats :: CfyStats
emptyCfyStats = CfyStats 0 0 0 0 0 0 0 0 0 0 0 0

scaleCfyStats :: Int -> CfyStats -> CfyStats
scaleCfyStats _ ZeroCfyStats = ZeroCfyStats
scaleCfyStats n (CfyStats s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12)
  = CfyStats (n * s1) (n * s2) (n * s3) (n * s4)  (n * s5)  (n * s6)
             (n * s7) (n * s8) (n * s9) (n * s10) (n * s11) (n * s12)

instance Monoid CfyStats where
  mempty = ZeroCfyStats
  
  ZeroCfyStats `mappend` cst = cst
  cst `mappend` ZeroCfyStats = cst
  CfyStats s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 `mappend`
    CfyStats t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12
    = CfyStats (s1 + t1) (s2 + t2) (s3 + t3) (s4 + t4) (s5 + t5) (s6 + t6)
               (s7 + t7) (s8 + t8) (s9 + t9) (s10 + t10) (s11 + t11) (s12 + t12)

class (Monad m) => MonadCfyStats m where
  writeStats :: CfyStats -> m ()

----------------------------------
-- Phase 1: Escape-analyse code --
----------------------------------

{-
Note [Escape analysis]
~~~~~~~~~~~~~~~~~~~~~~

The purpose of the escape analysis is to work out which let-bound functions we
can translate as parameterized continuations rather than as functions. To do
this, we gather information on all the identifier's occurrences, namely:

  Does every occurrence of f appear in a non-escaping context?

To be in a non-escaping context, the occurrence of f must be a tail call in the
context that declared it - that is, not inside a lambda, an argument, a cast
(see Note [Calls inside casts]), etc.

We perform the escape analysis by passing a Var -> Bool mapping bottom-up. Any
candidate for contification (that is, any let-bound variable) that appears in an
expression will appear in the returned mapping. If f appears only in
non-escaping contexts (that is, does not escape), it maps to True; if it appears
at least once in an escaping context, it maps to False. When combining mappings,
say when analysing the branches of a case, we union them together, performing an
AND on any two variables that appear in both mappings. Then, whenever the
traversal returns from an escaping context, such as a lambda or an argument
position, we take the whole mapping and set every value to False, since every
variable that appears in such a context escapes.

(In practice, we save some time by keeping two sets rather than one mapping--one
records all variables seen, and the other records the subset of those that
escape. Rather than set every value to False, then, we just set the escapee set
equal to the occurrence set.)

The result of the escape analysis is an annotated version of the code where each
binder is marked according to whether it should be contified and, if so, what
its total arity is (that is, arity counting both type and value binders).

Note [Calls inside casts]
~~~~~~~~~~~~~~~~~~~~~~~~~

If we try to contify a function that's invoked inside a cast, the resulting
program will be ill-typed. From the perspective of (Dual) System FC's
operational semantics, this is unsurprising because a cast is an operation and
a tail call is definitionally the final operation a function performs. However,
the cast is a fiction; all casts (and types) are erased on translation to STG.
Hence CoreToStg's escape analysis is able to contify (or let-no-escape) more
functions than ours. It's unclear what the workaround might be, though it's also
unclear how often this is a problem in practice.

Note [Aggressive mode]
~~~~~~~~~~~~~~~~~~~~~~

Many contification opportunities are missed if bindings are constrained to
remain where they are. For example, consider:

  let k = \x. x + 1 in k y * 2

This translates as:

  compute. let k = \x. compute. <(+) | $ x; $ 1; ret>
           in <(*) | $ compute. <k | $ y; ret>; $ 2; ret>
  
We can't contify k as is, since it's called from an escaping context. But it's
*only* called from that context. If we first float k in, giving

  compute. <(*) | $ compute. let k = \x. compute. <(+) | $ x; $ 1; ret>
                             in <k | $ y; ret>
                ; $ 2
                ; ret>,

now we can contify after all:

  compute. <(*) | $ compute. let join k = \x. <(+) | $ x; $ 1; ret>
                             in jump k (y)
                ; $ 2
                ; ret>

We don't want to do this with every translation to Sequent Core, since it's
invasive - it may interfere with other passes such as CSE. Hence, much like the
simplifier, the contifier operates in two modes: gentle and aggressive. In
aggressive mode, contification acts much like the gentle contifier and a
specialized Float In at the same time. 

Note [Aggressive mode: Continuation binders]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In aggressive mode, contification becomes akin to interprocedural constant
propagation: We want to know whether all invocations of a given term have the
same continuation. This would be somewhat easier if our AST gave binders to
continuation parameters and term parameters alike, but (currently) it does not.
Thus we invent an integer to tag each 'Compute' subterm, and then using these
"continuation binders," we ask for each function f:  

  Is there a continuation binder p that is the nearest enclosing continuation
  binder for every invocation of f?

(We reobtain the gentle-mode rule by further requiring that p is the nearest
enclosing continuation binder at f's own binding.) If the answer is yes, we move
f's binding inside p.

Crucially, for the above criterion to work, we have to eta-expand any bare
occurrence of a variable x as (compute. <x | ret>) so that it gets its own
continuation binder. 

Returning to our example, we can add continuation binders like so:

  compute p1.
    let k = \x. compute p2. <(+) | $ compute p3. <x | ret p3>; $ 1; ret p2>
    in <(*) | $ compute p4. <k | $ compute p5. <y | ret p5>; ret p4>; $ 2; ret p1>

Here we've also annotated the returns with their corresponding binders.      
The only call to k is a tail call under p4, so that's where the binding
for f goes.

Note [Aggressive mode: Recursive join points]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Looking for recursive join points makes things trickier, but the potential for
code motion makes it worthwhile. Consider a variation on our example:

  let k n acc = case n of 0 -> acc; _ -> fac (n-1) (n*acc)
  in even (k y 1)
  
In (simplified) Sequent Core with continuation binders:

  compute p1.
    let k n acc
          = compute p2.
              <n | case of 0 -> <acc | ret p2>
                           _ -> <k | $ compute p3. <(-) | $ n; $ 1; ret p3>
                                   ; $ compute p4. <(*) | $ n; $ acc; ret p4>
                                   ; ret p2>>
    in <even | $ compute p5. <k | $ y; $ 1; ret p5>; ret p1>

(Here we have not bothered to eta-expand parameters, which can't be contified
anyway.)

There are two invocations of k, one with continuation p5 and the other with
continuation p2. However, the call with p2 is from within fib itself, and p2 is
k's top-level continuation binder. Therefore *p2 is always equal to p5*, and
we can float and contify:

  compute p1.
    <even
      | $ compute p5.
            let join k (n, acc)
                  = <n | case of
                           0 -> <acc | ret p5>
                           _ -> jump k ( compute p3. <(-) | $ n; $ 1; ret p3>
                                       , compute p4. <(*) | $ n; $ acc; ret p4> )>
            in jump k (y, 1)
      ; ret p1>

So, to determine whether to contify a recursive function, we look for whether
each invocation is EITHER

  (a) an exact call from *inside* the RHS, in the scope* of the function's
      top-level continuation binder, or
  (b) an exact call from *outside* the RHS, in the scope of the same
      continuation binder as all other calls of type (b).

For mutual recursion, as always we must contify either all or none; to contify,
each invocation must be either

  (a) an exact call from *inside* the RHS of a function in the group, in the
      scope of that function's top-level continuation binder, or
  (b) an exact call from *outside* the RHSes (i.e. in the body of the let), in
      the scope of the same continuation binder as all other calls of type (b).

* Note that only one continuation binder (besides join points) is considered
  in-scope at a time, so it can't be under an inner continuation binder instead.
  Conveniently, an inner continuation binder forms an escaping context anyway. 

Note [Aggressive mode: Benefits]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To demonstrate the potential benefit, note that even is strict (and pretend it's
too big to inline). Therefore we can transform it by case-binding its argument:

  compute p1.
    <compute p5.
       let join k (n, acc)
             = <n | case of
                      0 -> <acc | ret p5>
                      _ -> jump k ( compute p3. <(-) | $ n; $ 1; ret p3>
                                  , compute p4. <(*) | $ n; $ acc; ret p4> )>
            in jump k (y, 1)
    | case as x of DEFAULT -> <even | $ x; ret p1>>

The command under compute p1 is a redex - p5 will be bound to (case as x ...).
Thus we have:

  compute p1.
    let join k (n, acc)
          = <n | case of
                   0 -> <acc | case as x of DEFAULT -> <even | $ x; ret p1>>
                   _ -> jump k ( compute p3. <(-) | $ n; $ 1; ret p3>
                               , compute p4. <(*) | $ n; $ acc; ret p4> )>
         in jump k (y, 1)

(Note that the Sequent Core simplifier would actually bind the body of the case
as a join point, then inline the join point because it's only used once.)

In terms of Core, the net effect is roughly to transform

  let k n acc = case n of 0 -> acc; _ -> k (n-1) (n*acc)
  in even (k y 1)

into

  let k n acc = case n of 0 -> even acc; _ -> k (n-1) (n*acc)
  in k y 1.
  
Moving the invocation of even into the branch is not an obvious operation, but
it is correct, and in general it may provide many of the same benefits as the
case-of-case transform. For instance:

  if -1 `elem` xs then error "urk" else frob xs
  
  => (inlining, beta-expansion, simple floating)
  
  let go ys = case ys of []      -> False
                         y : ys' -> if y == -1 then True else go ys'
  in if go xs then error "urk" else frob xs
     
  => (aggressive contification, mu-beta-expansion)

  let go ys = case ys of []      -> if False then error "urk" else frob xs
                         y : ys' -> if y == -1 then if True then error "urk"
                                                            else frob xs
                                               else go ys'
  in go xs

  => (case-reduction)
  
  let go ys = case ys of []      -> frob xs
                         y : ys' -> if y == -1 then error "urk" else go ys'
  in go xs

Note that the Boolean values have disappeared entirely.

Note [Continuation dispositions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The decision to contify a function often depends on whether a function below it
was contified as well, since tail calls in a join point don't escape. Now,
KontIds are assigned top-down, so each function body gets a continuaton id even
though it may become a join point, thus sharing its context's continuation.
Therefore, when we contify, we have to remember that the function body's
continuation is being identified with its parent.

A simple example, with continuation ids in brackets:

  compute [0]
    let k x = compute [1] ...
        g y = compute [2] < k | $ compute [3] < (+) | $ y; $ 1; ret >; ret >)
    in <a | case of True  -> < k | $ b; ret >
                    False -> < g | $ c; ret > >

The invocation of k from g occurs in scope 2 (by which I mean the scope of
continuation 2), so at first it appears we can't contify k. But we *do* contify
g, which effectively substitutes continuation 0 in place of 2. When considering
all the calls to k, then, we must consider 2 and 0 equivalent. This equivalence
information is part of the KontStates value that propagates upward with the
escape analysis.

We include the "parentage" of each continuation so that we can check whether a
recursive function is called from a proper descendent of its own body (or that
of a sibling), since we can't float the binding into its own right-hand side and
hence can't contify in this case.

Finally, rules and unfoldings present a futher complication. We don't want to
float into a rule or unfolding, as this will lead to code duplication. However,
a call from a rule or unfolding does not necessarily escape (rules and
unfoldings are effectively alternate RHSes). Since marking a continuation as a
proper child makes calls escape, but marking it as merged allows floating in, we
need a third option. Namely, we give rules and unfoldings their own
continuations but mark them as float barriers.

None of this is necessary in gentle mode, where we simply mark a variable as
escaping as soon as it appears in an escaping context. The prospect of floating
a binding inward forces us to keep closer track of what's going on.
-}

-- Bottom-up data --

data EscapeAnalysis
  = EA { ea_calls   :: IdEnv (Bag CallInfo)
       , ea_allVars :: IdSet
       , ea_kstates :: KontStates }

data CallInfo
  = CI { ci_arity   :: TotalArity  -- Counts *all* arguments, including types
       , ci_args    :: Call        -- Invariant: Length is ci_arity
       , ci_kontId  :: KontId
       }

type TotalArity = Arity            -- Counts *all* arguments, including types
type Call = [SeqCoreArg]
type KontId = Int                  -- Note [Aggressive mode: Continuation binders] 
type KontIdSet = IntSet

type KontStates = IntMap KontState
data KontState = ChildOf KontId Disposition deriving (Show)
-- The relation of a child continuation to its parent. See Note [Dispositions]
data Disposition = Child           -- ^ True child scope; referenced variables escape
                 | Merged          -- ^ Contification is making these scopes equivalent
                 | Barrier         -- ^ Similar to 'Merged' (vars don't escape) EXCEPT
                                   --   floating past here not allowed
  deriving (Eq, Enum, Show)

data Relationship = Self | Descendant | Neither deriving (Eq, Enum, Show)
data CallRegion   = Outside | DeepOutside | Inside | Barred deriving (Eq, Enum, Show) 

emptyEscapeAnalysis :: EscapeAnalysis
emptyEscapeAnalysis = EA { ea_calls   = emptyVarEnv, ea_allVars = emptyVarSet
                         , ea_kstates = IntMap.empty }

isEmptyEscapeAnalysis :: EscapeAnalysis -> Bool
isEmptyEscapeAnalysis ea = isEmptyVarEnv (ea_allVars ea) && IntMap.null (ea_kstates ea)

unitCall :: Id -> Call -> KontId -> EscapeAnalysis
unitCall x call kid = EA { ea_calls   = unitVarEnv x (unitBag ci)
                         , ea_allVars = unitVarSet x
                         , ea_kstates = IntMap.empty }
  where ci = CI { ci_arity = length call, ci_args = call, ci_kontId = kid }

markAllAsEscaping :: EscapeAnalysis -> EscapeAnalysis
markAllAsEscaping ea = ea { ea_calls = emptyVarEnv }

combineEscapeAnalyses :: EscapeAnalysis -> EscapeAnalysis -> EscapeAnalysis
combineEscapeAnalyses ea1 ea2
  | isEmptyEscapeAnalysis ea1 = ea2
  | isEmptyEscapeAnalysis ea2 = ea1
  | otherwise = EA { ea_allVars = ea_allVars ea1 `unionVarSet` ea_allVars ea2
                   , ea_calls   = calls'
                   , ea_kstates = kstates' }
  where
    -- If any variable appears in ea_allVars but not ea_calls, this signals that
    -- an escaping occurrence was definitely seen (see markAllAsEscaping). Hence
    -- the domain of ea_calls comprises the set of (potentially) non-escaping
    -- variables. Thus there are three ways a variable's calls stay in the table:    
    --   1. It appears in the left non-escaping set and not at all on the right
    --   2. It appears in the right non-escaping set and not at all on the left
    --   3. It appears in both non-escaping sets
    
    onlyIn1 = ea_calls ea1 `minusVarEnv` ea_allVars ea2
    onlyIn2 = ea_calls ea2 `minusVarEnv` ea_allVars ea1
    inBoth  = intersectUFM_C unionBags (ea_calls ea1) (ea_calls ea2)
    calls'  = onlyIn1 `plusVarEnv` onlyIn2 `plusVarEnv` inBoth
    
    kstates' = IntMap.unionWithKey (\_ _ _ -> panic "kstates")
                                   (ea_kstates ea1) (ea_kstates ea2)

forgetVars :: EscapeAnalysis -> [Id] -> EscapeAnalysis
forgetVars ea@(EA { ea_calls = calls, ea_allVars = allVars }) xs
  = ea { ea_calls   = calls   `delVarEnvList` xs
       , ea_allVars = allVars `delVarSetList` xs }

-- | Description of occurrences of an identifier (see 'checkEscaping')
data Occs = Abs -- No calls whatsoever (dead binder!)
          | Esc -- At least one call escapes
          | NonEsc CallInfo CallRegion
              -- No calls escape; furthermore, this call and all others are in
              -- the given region (inside, outside, or deep outside (needing float)).

-- | Return a call to the given function, so long as all calls are admissible.
-- An admissible call (a) occurs in an admissible scope and (b) has the same
-- number of arguments (both type and value) as the other admissible calls. An
-- admissible scope is either one of the given "inside" scopes, if any, or the
-- single "outside" scope. The outside scope may be specified; otherwise, it can
-- be any single scope, so long as it is conistent among the admissible calls.
-- (The outside scope is the scope of the body of the let-binding (after
-- contification in aggressive mode); the inside scopes are those of the RHSes
-- of the let-bindings in a recursive group.)
--
-- If no calls escape (and there is at least one call), then `NonEsc call` is
-- returned for some call. The particular call is arbitrary, except that if
-- possible it will be from the outside scope. (See Note [Determining fixed type
-- arguments].) If there is at least one inadmissible call, `Esc` is returned
-- (since the function escapes). If there are no calls whatsoever (dead binder),
-- `Abs` is returned.
checkEscaping :: EscapeAnalysis -- ^ The escape analysis to query.
              -> Id             -- ^ The binder whose calls will be inspected.
              -> KontId         -- ^ The binder's own scope.
              -> Bool           -- ^ True if the binder may float inward if
                                --   necessary for contification (aggressive mode).
              -> KontIdSet      -- ^ The inside scopes. Empty for non-recursive
                                --   binding.
              -> (CfyStats,
                  Occs)         -- ^ `Abs` if no calls; `Esc` if any escaping
                                --   calls; `NonEsc call` if only non-escaping
                                --   calls.
checkEscaping ea x outside allowFloat insides
  | tracing
  , pprTraceShort "checkEscaping" (ppr x $$ ppr ea $$
                              text "  pin to:" <+> ppr outside $$
                              ppWhen (not (IntSet.null insides))
                                (text " rec grp:" <+> ppr (IntSet.toList insides)) $$
                              text "==>" <+> ppr answer) False = undefined
  | otherwise
  = answer
  where
    states = ea_kstates ea
    answer = case lookupVarEnv (ea_calls ea) x of
               Just cis -> go Inside Nothing (bagToList cis)
               Nothing   | x `elemVarSet` ea_allVars ea -> (scopeMismatch, Esc)
                         | otherwise                    -> (ZeroCfyStats, Abs)
    
    go _      Nothing    []         = pprPanic "checkEscaping" $ ppr ea $$ ppr x
                                        -- shouldn't be any empty bags
    go region (Just ci)  []         = (ZeroCfyStats, NonEsc ci region)
    go _      _          (ci:_)     | not (okScope ci)        = (scopeMismatch, Esc)
    go _      Nothing    (ci:cis)   = go region (Just ci) cis
      where
        region = locateCallIn states (ci_kontId ci) outside insides
    go region1 (Just ci1) (ci2:cis) | let (cst, matching) = ci1 `matches` ci2
                                    , not matching            = (cst, Esc)
                                    | otherwise               = go region' (Just ci') cis
      where
        (region', ci') | region1 == Inside, region2 /= Inside = (region2, ci2)
                       | otherwise                            = (region1, ci1)
        region2 = locateCallIn states (ci_kontId ci2) outside insides
    
    okScope ci
      | allowFloat = okScope_agg region
      | otherwise  = okScope_gentle ci region
      where
        region     = locateCallIn states (ci_kontId ci) outside insides 
                                 
    okScope_agg Barred = False
    okScope_agg _      = True -- inside, outside, or deep outside
    
    okScope_gentle _  _       | not debugIsOn = True -- check is redundant
    okScope_gentle _  Inside  = True
    okScope_gentle _  Outside = True
    okScope_gentle ci region
      = WARN(True,
             text "Call in wrong scope not removed" $$
             text "Call:" <+> ppr ci $$
             text "Region:" <+> text (show region) $$
             text "Outside scope:" <+> ppr outside $$
             ppWhen (not (IntSet.null insides)) (
               text "Inside scope(s):" <+> ppr (IntSet.toAscList insides)
             ) $$
             text "Escape analysis:" <+> ppr ea)
        False
    
    ci1 `matches` ci2 | ci_arity ci1 /= ci_arity ci2
                      = (arityMismatch, False)
                      | ci_kontId ci1 == ci_kontId ci2 ||
                        ci_kontId ci1 `IntSet.member` insides ||
                        ci_kontId ci2 `IntSet.member` insides
                      = (ZeroCfyStats, True)
                      | otherwise
                      = (scopeMismatch, False)

    scopeMismatch = emptyCfyStats { cst_scopeMismatch = 1 }
    arityMismatch = emptyCfyStats { cst_arityMismatch = 1 }
-- If none of the variables escape, return the list of variables that occur,
-- along with their apparent arities and call lists, and the scope to float to,
-- if any
checkEscapingRec :: EscapeAnalysis -> [Id] -> KontId -> Bool -> KontIdSet
                 -> (CfyStats, Maybe ([(Id, Maybe CallInfo)], Maybe KontId))
checkEscapingRec ea xs outside allowFloat insides
  = let (csts, mb_pairs)
          = unzip $ flip map xs $ \x ->
              let (cst, occs) = checkEscaping ea x outside allowFloat insides
              in (cst,) $ case occs of
                NonEsc ci region -> Just (x, Just (ci, region))
                Esc              -> Nothing
                Abs              -> Just (x, Nothing)
    in case sequence mb_pairs of
      Just pairs  | Just tgtKontId <- findTgtKontId pairs
                 -> ( mconcat csts
                    , Just ( [ (x, fst <$> maybe_ci_region) | (x, maybe_ci_region) <- pairs]
                           , tgtKontId ) )
      _          -> (mconcat (map markAsScopeMismatch csts), Nothing)
  where
    findTgtKontId []
      = Nothing -- no outside calls; can't contify (but dead anyway)
    findTgtKontId ((_, Nothing) : pairs)
      = findTgtKontId pairs
    findTgtKontId ((_, Just (ci, region)) : pairs)
      = case region of
          Inside      -> findTgtKontId pairs
          Outside     -> Just Nothing -- Contify but don't float
          DeepOutside -> Just (Just (ci_kontId ci))
          Barred      -> pprPanic "checkEscapingRec" $ ppr ci
  
    markAsScopeMismatch ZeroCfyStats = emptyCfyStats { cst_scopeMismatch = 1 }
    markAsScopeMismatch other        = other

instance Monoid EscapeAnalysis where
  mempty = emptyEscapeAnalysis
  mappend = combineEscapeAnalyses

-- Top-down data --

type CandidateSet = IdSet
data EscEnv = EE {
  ee_mode   :: ContifySwitches,
  ee_cands  :: CandidateSet,
  ee_kontId :: KontId -- Continuation id currently in scope
}

aggressiveMode, gentleMode :: ContifySwitches
aggressiveMode = ContifySwitches { cs_gentle = False }
gentleMode     = ContifySwitches { cs_gentle = True  }

emptyEscEnv :: ContifySwitches -> EscEnv
emptyEscEnv mode = EE { ee_mode = mode, ee_cands = emptyCandidateSet,
                        ee_kontId = panic "emptyEscEnv" }

emptyCandidateSet :: CandidateSet
emptyCandidateSet = emptyVarEnv

alterCandidates :: EscEnv -> (CandidateSet -> CandidateSet) -> EscEnv
alterCandidates env f = env { ee_cands = f (ee_cands env) }

addCandidate :: EscEnv -> Id -> EscEnv
addCandidate env x
  = alterCandidates env $ \cands -> extendVarSet cands x

addRecCandidates :: EscEnv -> [Id] -> EscEnv
addRecCandidates env ids
  = env { ee_cands  = extendVarSetList (ee_cands env) ids }

isCandidate :: EscEnv -> Id -> Bool
isCandidate env id
  = id `elemVarSet` ee_cands env

type Floats = IntMap (Bag SeqCoreBind)

emptyFloats :: Floats
emptyFloats = IntMap.empty

addFloat :: Floats -> KontId -> SeqCoreBind -> Floats
addFloat flts kontId bind = IntMap.insertWith unionBags kontId (unitBag bind) flts

floatsAt :: Floats -> KontId -> [SeqCoreBind]
floatsAt flts kontId = (bagToList <$> IntMap.lookup kontId flts) `orElse` []

-- State --

data EscState = EscState { es_kontIdSupply :: !KontIdSupply }

type KontIdSupply = KontId

initState :: KontIdSupply -> EscState
initState kids = EscState { es_kontIdSupply = kids }

locateCallIn :: KontStates -> KontId -> KontId -> KontIdSet -> CallRegion
locateCallIn states kontId outside insides
  = go False True kontId
  where
    go barred merged curr
      | is_outside = if | merged     -> Outside
                        | otherwise  -> DeepOutside
      | is_inside  = if | merged     -> Inside
                        | otherwise  -> Barred
      | otherwise
      = case IntMap.lookup curr states of
          Just (ChildOf parent disp) -> case disp of
             Child      | barred     -> Barred
                        | otherwise  -> go barred False  parent
             Merged                  -> go barred merged parent
             Barrier                 -> go True   merged parent
          Nothing                    -> pprPanic "locateCallIn" $
                                          ppr (IntMap.toList states) $$
                                          ppr kontId <+> ppr outside <+>
                                            ppr (IntSet.toList insides)
      where
        is_outside = curr == outside
        is_inside  = curr `IntSet.member` insides

-- Monad --

-- | The monad underlying the escape analysis.
newtype EscM a = EscM { unEscM :: EscEnv -> EscState
                               -> (Maybe EscapeAnalysis, CfyStats, EscState, a) }

instance Monad EscM where
  {-# INLINE return #-}
  return x = EscM $ \_env st -> (Nothing, mempty, st, x)
  
  {-# INLINE (>>=) #-}
  m >>= k  = EscM $ \env st ->
               let !(escs1, cst1, st1, x) = unEscM m env st
                   !(escs2, cst2, st2, y) = unEscM (k x) env st1
               in (escs1 <> escs2, cst1 <> cst2, st2, y)      

instance Functor EscM where fmap = liftM
instance Applicative EscM where { pure = return; (<*>) = ap }

instance MonadFix EscM where
  mfix f = EscM $ \env st ->
             let tup@(_, _, _, ans) = unEscM (f ans) env st
             in tup

instance MonadCfyStats EscM where
  writeStats cst = EscM $ \_env st -> (Nothing, cst, st, ()) 

runEscM :: ContifySwitches -> EscM a -> (CfyStats, a)
runEscM = runEscMWith 0

runEscMWith :: KontIdSupply -> ContifySwitches -> EscM a -> (CfyStats, a)
runEscMWith kids mode m = case unEscM m env st of (_, cst, _, a) -> (cst, a)
  where env = emptyEscEnv mode
        st  = initState kids

-- Monad operations --

getEnv :: EscM EscEnv
getEnv = EscM $ \env st -> (Nothing, mempty, st, env)

getMode :: EscM ContifySwitches
getMode = ee_mode <$> getEnv

alteringEnv :: (EscEnv -> EscEnv) -> EscM a -> EscM a
alteringEnv f m = EscM $ \env -> unEscM m (f env)

alteringCandidates :: (CandidateSet -> CandidateSet) -> EscM a -> EscM a
alteringCandidates f = alteringEnv $ \env -> env { ee_cands = f (ee_cands env) }

withEnv :: EscEnv -> EscM a -> EscM a
withEnv env m = EscM $ \_ -> unEscM m env

withoutCandidate :: Id -> EscM a -> EscM a
withoutCandidate x = alteringCandidates (`delVarEnv` x)

withoutCandidates :: [Id] -> EscM a -> EscM a
withoutCandidates xs = alteringCandidates (`delVarEnvList` xs)

reportCall :: Id -> Call -> EscM ()
reportCall x call = do
                    env <- getEnv
                    when (isCandidate env x) $ do
                      when tracing $
                        pprTraceShort "reportCall" (ppr x <+> ppr call <+> ppr (ee_kontId env)) $
                        return ()
                      writeAnalysis (unitCall x call (ee_kontId env))

captureAnalysis, readAnalysis :: EscM a -> EscM (EscapeAnalysis, a)
captureAnalysis m
  = EscM $ \env st ->
             let !(escs, cst, st', ans) = unEscM m env st
             in (Nothing, cst, st', (escs `orElse` emptyEscapeAnalysis, ans))
readAnalysis m
  = EscM $ \env st ->
             let !(escs, cst, st', ans) = unEscM m env st
             in (escs, cst, st', (escs `orElse` emptyEscapeAnalysis, ans))

addChildKont :: EscapeAnalysis -> KontId -> KontId -> Disposition -> EscapeAnalysis
addChildKont ea child parent disp
  = ea { ea_kstates = IntMap.insertWith (\_ _ -> panic "addChildKont")
                                        child (ChildOf parent disp) (ea_kstates ea) }

addChildKonts :: EscapeAnalysis -> [KontId] -> KontId -> Disposition -> EscapeAnalysis
addChildKonts ea children parent disp
  = foldr (\child ea' -> addChildKont ea' child parent disp) ea children

writeAnalysis :: EscapeAnalysis -> EscM ()
writeAnalysis escs = EscM $ \_ st -> (Just escs, mempty, st, ())

inInnerContext :: Disposition -> EscM a -> EscM (KontId, a)
inInnerContext disp m
  = do
    kid <- mkFreshKontId
    env <- getEnv
    ~(escs, a) <- captureAnalysis $ withEnv (env { ee_kontId = kid }) m
    let escs' = if cs_gentle (ee_mode env) then markAllAsEscaping escs
                                           else escs
    writeAnalysis $ addChildKont escs' kid (ee_kontId env) disp
    return (kid, a)

getState :: EscM EscState
getState = EscM $ \_env st -> (Nothing, mempty, st, st)

putState :: EscState -> EscM ()
putState st' = EscM $ \_env _st -> (Nothing, mempty, st', ())

mkFreshKontId :: EscM KontId
mkFreshKontId
  = do
    st@EscState { es_kontIdSupply = kid } <- getState
    putState $ st { es_kontIdSupply = kid + 1 }
    return kid

-- Result: Marked binders --

{-
Note [Fixing type arguments]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Suppose we are contifying the polymorphic function:

    k :: forall a b. Bool -> a -> b -> [b]

Since we're contifying it, it is always tail-called from a particular context,
and that context expects a result of type [T] for some particular T. Thus we
cannot allow b to vary in the contified version of k: It must *always* return
[T] (and its final argument must be a T). Hence we must eliminate the type
parameter b and substitute T for b in the type and body of k. Supposing T is Int,
the contified k looks like

    k :: Cont# (exists a. (Bool, a, Int))

(type simplified for clarity). Note that since a doesn't appear in the original
function's return type, it is free to vary, and we construct the existential as
usual. This is important for case analyses on existential types, which produce
polymorphic join points.

Note [Determining fixed type values]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The above discussion glossed over a detail: How did we determine T to be the
constant value of b? It is true that k must always be invoked with the same
value of b *but* recursive calls will pass on the constant value, so looking
at them is unhelpful.

For instance:

    let rec { replicate :: forall a. Int -> a -> [a] -> [a]
              replicate @a n x xs =
                case n <= 0 of True  -> xs
                               False -> rep @a (n-1) (x:xs) }
    in case q of True  -> rep @Char 4 'a' []
                 False -> rep @Char 3 'b' []

The rep function is always tail-called with Char as the type argument, but in
the recursive call this is not apparent from syntax alone: The recursive call
passes a, not Char. Thus we need to differentiate between recursive calls and
"outside" calls and we need to look at an outside call to determine a. If there
are no outside calls, we would need either abstract interpretation or
unification to find the correct type, so we punt and give up on contifying.

(One is tempted to detect when a recursive call passes a tyvar that's equal to
the corresponding binder. This could solve the above case - we would know not
to use a because a is itself the binder. However, this does not cover mutual
recursion or other cases where a is passed indirectly just as the actual type
is.)
-}

data KontOrFunc = MakeKont [ArgDesc] KontId | Keep
data ArgDesc    = FixedType Type | FixedVoidArg | TyArg TyVar | ValArg Type
data MarkedVar  = Marked Var KontOrFunc

isValArgDesc :: ArgDesc -> Bool
isValArgDesc (ValArg {}) = True
isValArgDesc _           = False

removeFixedArgs :: [a] -> [ArgDesc] -> [a]
removeFixedArgs args descs
  = [ arg | (arg, desc) <- zip args descs, keep desc ]
  where
    keep (FixedType _) = False
    keep FixedVoidArg  = False
    keep _             = True

isKeep :: KontOrFunc -> Bool
isKeep Keep = True
isKeep _    = False

unmark :: MarkedVar -> Var
unmark (Marked var _) = var

instance HasId MarkedVar where identifier = unmark

-- | Decide whether a variable should be contified, returning the marked
-- variable and a flag (True if contifying).
markVar :: Id -> CallInfo -> KontId -> (CfyStats, MarkedVar, Bool)
markVar x ci tgtKontId
  = case mkArgDescs x (idType x) IntSet.empty ci of
      (cst, Just descs) -> (cst, Marked x (MakeKont descs tgtKontId), True)
      (cst, Nothing)    -> (cst, Marked x Keep,                       False)

-- | Decide whether a group of mutually recursive variables should be contified,
-- returning the marked variables and a continuation id. Either all of the
-- variables will be contified and floated into the given continuation binder
-- or none of them will.
markRecVars :: [Id] -> [CallInfo] -> [TotalArity] -> KontId -> KontIdSet -> (CfyStats, [MarkedVar])
markRecVars xs cis lamCounts tgtKontId insideScopes
  | tracing
  , pprTraceShort "markRecVars" (ppr xs $$ ppr cis $$ ppr lamCounts $$
                                 ppr tgtKontId $$ text (show insideScopes)) False = undefined
  | any_inexact
  = (arityMismatch, cancel) -- Can't contify recursive functions unless calls are exact
  | otherwise
  = case findCulprit csts_and_argDescss of
      Nothing  -> (ZeroCfyStats, [ Marked x (MakeKont descs tgtKontId)
                                 | x <- xs | (_, Just descs) <- csts_and_argDescss ])
      Just cst -> (scaleCfyStats (length xs) cst, cancel)
  where
    any_inexact = or (zipWith (\ci n -> ci_arity ci /= n) cis lamCounts)
    cancel = [ Marked x Keep | x <- xs ]
    
    csts_and_argDescss
      = zipWith (\x ci -> mkArgDescs x (idType x) insideScopes ci) xs cis
    
    findCulprit ((_, Just _) : pairs)
      = findCulprit pairs
    findCulprit ((cst, Nothing) : _)
      = Just cst
    findCulprit []
      = Nothing
    
    arityMismatch = emptyCfyStats { cst_arityMismatch = length xs }

-- | Return a constant value for each argument that needs one, given the type
-- and total arity of a function to be contified and a call made to it. Any
-- type parameters binding variables appearing in the return type must be made
-- constant, since the contified function will return to a fixed continuation in
-- which those parameters are not bound. (See Note [Determining fixed type
-- values].)
-- 
-- Returns Nothing if a type parameter needs to be fixed but the scope of the
-- given call is the RHS of a recursive binder in the same group, meaning only
-- recursive calls were made to the function. In this case, we give up on
-- contification. (TODO: A more sophisticated analysis might still find the
-- correct type to use.)
--
-- We also don't contify if the id has rules; this is uncommon, but it does
-- happen (often due to SpecConstr), and we don't want to stop rules from firing.
-- (TODO: We should be able to adapt the rules.)
--
-- It's possible the total arity is greater than the number of arrows and foralls
-- in the type, but only if the return type of the function is a type variable
-- bound in an outer scope. This is fine, because the extra arguments cannot
-- change the actual return type, so we don't need to fix (mask out) the extra
-- arguments. TODO Be more sure about this.
mkArgDescs :: Var -> Type -> KontIdSet -> CallInfo -> (CfyStats, Maybe [ArgDesc])
mkArgDescs x _ _ _
  | idHasRules x = ( emptyCfyStats { cst_dontCfyRules = 1 }
                   , Nothing ) -- unlikely but possible, and contification
                               -- would likely get in the way of rule firings
mkArgDescs x ty ins (CI { ci_arity = arity, ci_args = call, ci_kontId = kid })
  = case go ty call of Left cst    -> (cst, Nothing)
                       Right descs -> (ZeroCfyStats, Just descs)
  where
    (_tyVars, retTy) = splitPiTyN ty arity
    freeInRetTy     = tyVarsOfType retTy
    
    go ty (Type tyArg : call)
      | tyVar `elemVarSet` freeInRetTy
      = if kid `IntSet.member` ins
          then Left ( emptyCfyStats { cst_polyFail = 1 } ) -- Note [Determining fixed type values]
          else -- Start over with new return type
               case mkArgDescs x (substTyWith [tyVar] [tyArg] bodyTy) ins
                                              (CI { ci_arity  = length call
                                                  , ci_args   = call
                                                  , ci_kontId = kid }) of
                  (_, Just descs) -> Right (FixedType tyArg : descs)
                  (cst, Nothing)  -> Left cst
      | otherwise
      = (TyArg tyVar :) <$> go bodyTy call
      where
        (tyVar, bodyTy) = splitForAllTy_maybe ty `orElse`
                            pprPanic "mkArgDescs" (ppr ty <+> ppr tyArg)
    go ty (arg : call)
      | argTy `eqType` voidPrimTy
      = (FixedVoidArg :) <$> go retTy call
      | otherwise
      = (ValArg argTy :) <$> go retTy call
      where
        (argTy, retTy) = splitFunTy_maybe ty `orElse`
                           pprPanic "mkArgDescs" (ppr ty <+> ppr arg)
                           
    go _ [] = Right []

splitPiTyN :: Type -> TotalArity -> ([Maybe TyVar], Type)
splitPiTyN ty n
  | Just (tyVar, ty') <- splitForAllTy_maybe ty
  = let (args, retTy) = splitPiTyN ty' (n-1)
    in (Just tyVar : args, retTy)
  | Just (_, ty') <- splitFunTy_maybe ty
  = let (args, retTy) = splitPiTyN ty' (n-1)
    in (Nothing : args, retTy)
  | otherwise
  = ([], ty)

-- Annotated AST --

type MarkedTerm     = AnnTerm     MarkedVar KontId
type MarkedCommand  = AnnCommand  MarkedVar KontId
type MarkedFrame    = AnnFrame    MarkedVar KontId
type MarkedEnd      = AnnEnd      MarkedVar KontId
type MarkedBind     = AnnBind     MarkedVar KontId
type MarkedBindPair = AnnBindPair MarkedVar KontId
type MarkedJoin     = AnnJoin     MarkedVar KontId
type MarkedAlt      = AnnAlt      MarkedVar KontId
type MarkedProgram  = AnnProgram  MarkedVar KontId

-- "no kont binder"
nkb :: KontId
nkb = -1

-- Escape analysis --

escAnalProgram :: ContifySwitches -> SeqCoreProgram -> (CfyStats, MarkedProgram)
escAnalProgram mode binds
  | dumping   = pprTrace "escAnalProgram" (pprTopLevelAnnBinds ans) (cst, ans)
  | otherwise = (cst, ans)
  where
    (csts, ans) = unzip $ map (runEscM mode . escAnalTopLevelBind mode) binds
    cst = mconcat csts

escAnalTopLevelBind :: ContifySwitches -> SeqCoreBind -> EscM MarkedBind
escAnalTopLevelBind mode bind
  | tracing, pprTraceShort "escAnalTopLevelBind" (ppr mode $$ pprWithCommas (pprBndr LetBind . binderOfPair) (flattenBind bind)) False = undefined
  | otherwise
  = do -- runEscM mode $ do
      case bind of
        NonRec (BindTerm bndr term)
          -> (nkb,) . AnnNonRec <$> doTerm bndr term
        NonRec (BindJoin {})
          -> pprPanic "escAnalTopLevelBind" (ppr bind)
        Rec pairs
          -> ((nkb,) . AnnRec <$>) $ forM pairs $ \pair ->
               case pair of
                 BindTerm bndr term -> doTerm bndr term
                 BindJoin {} -> pprPanic "escAnalTopLevelBind" (ppr bind) 
  where
    doTerm bndr term
      = do
        term' <- escAnalTerm term
        return $ (nkb, AnnBindTerm (Marked bndr Keep) term')

escAnalBind :: SeqCoreBind -> EscapeAnalysis
            -> EscM (EscEnv, Maybe MarkedBind)
escAnalBind bind _
  | tracing, pprTraceShort "escAnalBind" (pprWithCommas (pprBndr LetBind . binderOfPair) (flattenBind bind)) False = undefined
escAnalBind (NonRec (BindTerm bndr rhs)) escs_body
  = do
    env <- getEnv
    let kontId = ee_kontId env
        mode   = ee_mode env
    rhsKontId <- mkFreshKontId
    let env_rhs  = env { ee_kontId = rhsKontId }
        env_body = addCandidate env bndr
    (escs_rhs, (rhs', lamCount)) <-
      captureAnalysis $ withEnv env_rhs $
        escAnalId bndr >> escAnalRhsTerm rhs
      -- escAnalId looks at rules and unfoldings, which act as alternate RHSes
    let allowFloat = not (cs_gentle mode)
        (cst1, occs) = checkEscaping escs_body bndr kontId allowFloat IntSet.empty
        (cst2, marked, rhs_escapes)
          | NonEsc ci region <- occs
          , region == Outside || okayToFloat bndr rhs' ci
          = let tgtKontId = case region of Outside     -> kontId
                                           DeepOutside -> ASSERT(not (cs_gentle mode))
                                                          ci_kontId ci
                                           _           -> pprPanic "escAnalBind" $
                                                            ppr bndr $$ ppr occs $$
                                                            ppr escs_body
                (cst, marked, contifying) = markVar bndr ci tgtKontId
            in (cst, marked, not contifying || ci_arity ci /= lamCount)
              -- Note [Contifying inexactly-applied functions]
          | NonEsc _ _ <- occs
          = (emptyCfyStats { cst_scopeMismatch = 1 }, Marked bndr Keep, True)
          | otherwise
          = (ZeroCfyStats, Marked bndr Keep, True)
        escs_rhs' | rhs_escapes, cs_gentle (ee_mode env)
                  = markAllAsEscaping escs_rhs
                  | otherwise
                  = escs_rhs
        
        escs_rhs''   = addChildKont escs_rhs' rhsKontId kontId disp
          where disp | rhs_escapes = Child
                     | otherwise   = Merged
        
        bind' = (nkb, AnnNonRec (nkb, AnnBindTerm marked rhs'))
    
    writeStats cst1
    writeStats cst2
    writeAnalysis escs_rhs''
    return $ (env_body, Just bind')

escAnalBind (NonRec (BindJoin bndr rhs)) _
  = do
    rhs' <- escAnalId bndr >> escAnalJoin rhs
    env <- getEnv
    return (env, Just (nkb, AnnNonRec (nkb, AnnBindJoin (Marked bndr Keep) rhs')))

escAnalBind (Rec pairs@(BindTerm {} : _)) escs_body
  = ASSERT(all bindsTerm pairs)
    do
    env <- getEnv
    let bndrs     = map binderOfPair pairs
        
        kontId    = ee_kontId env
        mode      = ee_mode   env
        env_rhs   = addRecCandidates env bndrs
        
    rhsKontIds <- forM bndrs $ \_ -> mkFreshKontId
    let rhsKontIdSet = IntSet.fromList rhsKontIds
    (unzip -> (escs_rhss, unzip -> (rhss', lamCounts)))
      <- forM (zip pairs rhsKontIds) $
           \(BindTerm bndr term, rhsKontId) ->
             withEnv (env_rhs { ee_kontId = rhsKontId }) $
             captureAnalysis $ escAnalId bndr >> escAnalRhsTerm term
    let escs = addChildKonts (mconcat escs_rhss <> escs_body) rhsKontIds kontId Child
        allowFloat = not (cs_gentle mode)
        (cst1, mb_occs) = checkEscapingRec escs bndrs kontId allowFloat rhsKontIdSet
        (cst2, pairs', contifying)
          | Just (occs, floatToKontId) <- mb_occs
          , let tgtKontId = floatToKontId `orElse` kontId
          , let (bndrs_live, cis, rhss'_live, lamCounts_live)
                  = unzip4 [ (bndr, ci, rhs', lamCount)
                           | ((bndr, Just ci), rhs', lamCount) <-
                               zip3 occs rhss' lamCounts ]
          , let (cst_bndrs, bndrs_marked) = markRecVars bndrs_live cis lamCounts_live tgtKontId rhsKontIdSet
          , isNothing floatToKontId || and (zipWith3 okayToFloat bndrs_live rhss'_live cis)
          = (cst_bndrs, [ (nkb, AnnBindTerm bndr rhs') | bndr <- bndrs_marked | rhs' <- rhss'_live ], True)
          | otherwise
          = (cst_keep,  [ (nkb, AnnBindTerm (Marked bndr Keep) rhs') | bndr <- bndrs | rhs' <- rhss' ], False)
          where
            cst_keep | Just _ <- mb_occs = emptyCfyStats { cst_scopeMismatch = 1 }
                         -- we just made the decision now
                     | otherwise         = ZeroCfyStats
                         -- decision was made earlier
        
        escs_rhss'
          | not contifying, cs_gentle mode = markAllAsEscaping (mconcat escs_rhss)
          | otherwise                      = mconcat escs_rhss
        
        escs_rhss''  = addChildKonts escs_rhss' rhsKontIds kontId disp
          where disp | contifying = Merged
                     | otherwise  = Child
    
    writeStats cst1
    writeStats cst2
    writeAnalysis (escs_rhss'' `forgetVars` bndrs)
    
    let ans | null pairs' = 
                            WARN(True, ppr bndrs)
                            Nothing
            | otherwise   = Just (nkb, AnnRec pairs')
    return (env_rhs, ans)

escAnalBind (Rec pairs) _
  = ASSERT(all bindsJoin pairs)
    do
    let bndrs = map binderOfPair pairs
    rhss' <- forM pairs $ \(BindJoin bndr join) ->
               escAnalId bndr >> escAnalJoin join
    env <- getEnv
    return (env, Just (nkb, AnnRec [ (nkb, AnnBindJoin (Marked bndr Keep) rhs') | bndr <- bndrs | rhs' <- rhss' ]))
    
-- | If we float this in (to contify it), will we lose sharing?
okayToFloat :: SeqCoreBndr -> MarkedTerm -> CallInfo -> Bool
okayToFloat bndr _term ci
  = idArity bndr > 0 && any isValueArg (ci_args ci) -- TODO Experiment with this condition
      -- TODO It should be okay to float in thunks sometimes, just not through a
      -- (serious) lambda. Are we missing out in practice?

{-
Note [Contifying inexactly-applied functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If a function is consistently tail-called, but with the "wrong" number of
arguments, then it can still be contified but its body is an escaping context.
Consider (assuming all calls are tail calls):

    let k = \x -> ...
        h = \y z ->
              let j = \w -> ... k (w + z) ... in ... j y ...
    in ... e ...

Consider three cases for e:
  * e = h a b: Here we will contify all three functions: h is consistently
    tail-called *with two arguments*, so its body is a tail context for k;
    similarly, j is consistently tail-called with one argument, so the call to
    k is a true tail call.
  * e = h a: Since h a is a lambda, its body is an escaping context. Thus h is
    contified (as a continuation of one argument), as is j, but k is not.
  * e = h a b c: To contify h, we will first need to eta-expand it:

        h = \y z eta ->
              (let j = \w -> ... k (w + z) ... in ... j y ...) eta

    (We don't bother moving the argument inward; phase 2 will do that.) Now
    k (w + z) is clearly not a tail call, so again h and j are contified but k
    is not.

Crucially, escape analysis is a bottom-up pass, so we can in fact decide on j
and h first, thus influencing the decision for k.
-}

-- | Analyse a term, but don't let its top-level lambdas cause calls to
-- escape. Returns the number of lambdas ignored; if the function is partially
-- applied or oversaturated, the calls escape after all.
escAnalRhsTerm :: SeqCoreTerm -> EscM (MarkedTerm, Int)
escAnalRhsTerm expr
  = do
    let (bndrs, body) = collectBinders expr
    kontId <- ee_kontId <$> getEnv
    
    -- We don't want to call escAnalTerm because we need to skip over the
    -- Compute; the caller (escAnalBind) already set up our continuation binder
    body' <- withoutCandidates bndrs $ case body of
               Var x           -> (kontId,) . AnnCompute (idType x) <$> escAnalComm (Eval (Var x) [] Return)
               Lam {}          -> panic "escAnalRhsTerm" -- collectBinders screwed up??
               Lit lit         -> return $ (kontId, AnnLit lit) -- keep kontId for debugging
               Type ty         -> return $ (kontId, AnnType ty)
               Coercion co     -> return $ (kontId, AnnCoercion co)
               Compute ty comm -> (kontId,) . AnnCompute ty <$> escAnalComm comm
    
    return $ ( foldr (\x v -> (nkb, AnnLam x v)) body' [ Marked bndr Keep | bndr <- bndrs ]
             , length bndrs )

escAnalTerm :: SeqCoreTerm -> EscM MarkedTerm
escAnalTerm (Var x)
  | tracing, pprTraceShort "escAnalTerm/Var" (ppr x) False = undefined
  | otherwise
  = escAnalTerm $ Compute (idType x) (Eval (Var x) [] Return)
      -- Eta-expand so that the occurrence escapes
escAnalTerm (Lit lit)
  | tracing, pprTraceShort "escAnalTerm/Lit" (ppr lit) False = undefined
  | otherwise
  = return $ (nkb, AnnLit lit)
escAnalTerm expr@(Lam bndr _)
  | tracing, pprTraceShort "escAnalTerm/Lam" (pprBndr LambdaBind bndr) False = undefined
  | otherwise
  = do
    let (bndrs, body) = collectBinders expr
    -- No need to worry about shadowing - we uniquified binders (see runContify)
    body' <- escAnalTerm body
    let bndrs' = [ Marked bndr Keep | bndr <- bndrs ]
    return $ foldr (\x v -> (nkb, AnnLam x v)) body' bndrs'
escAnalTerm (Type ty)
  | tracing, pprTraceShort "escAnalTerm/Type" (ppr ty) False = undefined
  | otherwise
  = return $ (nkb, AnnType ty)
escAnalTerm (Coercion co)
  | tracing, pprTraceShort "escAnalTerm/Coercion" (ppr co) False = undefined
  | otherwise
  = return $ (nkb, AnnCoercion co)
escAnalTerm (Compute ty comm)
  | tracing, pprTraceShort "escAnalTerm/Compute" Out.empty False = undefined
  | otherwise
  = do
    (kontId, comm') <- inInnerContext Child $ escAnalComm comm
    return $ (kontId, AnnCompute ty comm')

escAnalComm :: SeqCoreCommand -> EscM MarkedCommand
escAnalComm comm@(Let bind body)
  | Rec pairs <- bind
  , let (termPairs, joinPairs) = partitionBindPairs pairs
  , not (null termPairs)
  , not (null joinPairs)
  = do
    when tracing $ do
      pprTraceShort "escAnalComm/1"
        (text "disentangling:" <+> ppr (bindersOf bind) <+> text "==>"
                               <+> ppr (map fst termPairs, map fst joinPairs)) $
        return ()
    escAnalComm $
      Let (Rec (map (uncurry BindTerm) termPairs)) $
      Let (Rec (map (uncurry BindJoin) joinPairs)) body
  | otherwise
  = do
    when tracing $ do
      env <- getEnv
      pprTraceShort "escAnalComm/2" (char '@' Out.<> ppr (ee_kontId env) $$ ppr comm) $ return ()
    (_escs, maybe_bind', body') <- mfix $ \ ~(rec_escs_body, _, _) -> do
      (env', maybe_bind') <- escAnalBind bind rec_escs_body
      (escs_body, body') <- readAnalysis $ withEnv env' $ escAnalComm body
      return (escs_body, maybe_bind', body')
    return $ maybe id (\b c -> (nkb, AnnLet b c)) maybe_bind' body'
escAnalComm (Jump args j)
  = do
    args' <- mapM escAnalTerm args
    return $ (nkb, AnnJump args' j)
escAnalComm (Eval term frames end)
  = do
    mode <- getMode
    kid <- ee_kontId <$> getEnv
    case term of
      Var fid 
         | null otherFrames, isReturn end
        -> doCall -- tail call; happens in this scope
         | not (cs_gentle mode) -- don't try floating in in gentle mode
        -> do -- not a tail call; happens in inner scope
           (innerKontId, innerComm') <- inInnerContext Child doCall
           let innerTy = idType fid `applyTypeToArgs` leftArgs
           
           frames' <- mapM escAnalFrame otherFrames
           end' <- escAnalEnd end
           
           return $ (kid, AnnEval (innerKontId, AnnCompute innerTy innerComm') frames' end')
                      -- If nothing floats in, we've just created a
                      -- mu-beta-redex, but hopefully the simplifier helps
        where
          (leftArgs, otherFrames) = mapWhileJust (\case App arg -> Just arg
                                                        _       -> Nothing) frames
          doCall = do reportCall fid leftArgs
                      args' <- mapM escAnalTerm leftArgs
                      return $ (kid, AnnEval (kid, AnnVar fid) (map ((nkb,) . AnnApp) args') (kid, AnnReturn))
      _ -> do
           -- If term is a variable and we're in gentle mode, this will record
           -- a call with no args, but the CallInfo will get tossed anyway
           term'   <- escAnalTerm term
           frames' <- mapM escAnalFrame frames
           end'    <- escAnalEnd end
           return $ (kid, AnnEval term' frames' end')

escAnalFrame :: SeqCoreFrame -> EscM MarkedFrame
escAnalFrame (App arg) = (nkb,) . AnnApp <$> escAnalTerm arg
escAnalFrame (Cast co) = return $ (nkb, AnnCast co)
escAnalFrame (Tick ti) = return $ (nkb, AnnTick ti)

escAnalEnd :: SeqCoreEnd -> EscM MarkedEnd
escAnalEnd Return = (ee_kontId <$> getEnv) >>= \kid -> return (kid, AnnReturn)
escAnalEnd (Case bndr alts)
  = do
    kid <- ee_kontId <$> getEnv
    alts' <- withoutCandidate bndr $ forM alts $ \(Alt con bndrs rhs) -> do
      rhs' <- withoutCandidates bndrs $ escAnalComm rhs
      return $ (kid, AnnAlt con (map (`Marked` Keep) bndrs) rhs')
    return $ (kid, AnnCase (Marked bndr Keep) alts')

escAnalJoin :: SeqCoreJoin -> EscM MarkedJoin
escAnalJoin (Join bndrs comm)
  = do
    comm' <- withoutCandidates bndrs $ escAnalComm comm
    return $ (nkb, AnnJoin (map (`Marked` Keep) bndrs) comm')

-- Analyse unfolding and rules
escAnalId :: Id -> EscM ()
escAnalId x
  | isId x
  = void $ inInnerContext Barrier $ do -- don't float into rules or unfolding, but
                                       -- don't mark all references as escaping
      mapM_ escAnalRule (idCoreRules x)
      escAnalUnfolding (idUnfolding x)
  | otherwise
  = return ()

escAnalRule :: Core.CoreRule -> EscM ()
escAnalRule (Core.Rule { Core.ru_bndrs = bndrs, Core.ru_rhs = coreRhs })
  = let rhs = termFromCoreExpr coreRhs
      -- Note: This may be a wildly invalid term if this is a rule for a join
      -- point, since the RHS will translate as an application rather than a
      -- Jump. However, for our purposes here, this doesn't matter; the
      -- important thing is that the arguments escape. 
    in void $ withoutCandidates bndrs $ escAnalTerm rhs
escAnalRule _
  = return ()

escAnalUnfolding :: Unfolding -> EscM ()
escAnalUnfolding (Core.CoreUnfolding { Core.uf_tmpl = rhs  })
  = void $ escAnalTerm (termFromCoreExpr rhs)
escAnalUnfolding (Core.DFunUnfolding { Core.df_args = args })
  = mapM_ (escAnalTerm . termFromCoreExpr) args
escAnalUnfolding _ = return ()

----------------------
-- Phase 2: Contify --
----------------------

-- Continuation calling conventions --

-- | The protocol for invoking a given let-bound continuation. Currently all
-- such continuations must be invoked using a jump, so @ByJump@ is the only
-- constructor, but we must still keep track of which arguments are fixed and
-- should be omitted when converting a function call.
newtype KontCallConv = ByJump [ArgDesc]

-- Auxiliary datatype for idToJoinId
data KontType = KTExists TyVar KontType | KTTuple [KontType] | KTType Type

-- | Convert an id to the id of a join point, changing its type according to the
-- given calling convention. Updates the arity but NOT the rules or unfolding.
idToJoinId :: Id -> KontCallConv -> JoinId
idToJoinId p (ByJump descs)
  = p `setIdType` kontTypeToType (go (idType p) descs)
      `setIdArity` valArgCount
  where
    valArgCount = count (\case { ValArg {} -> True; _ -> False }) descs
    
    go _  [] = KTTuple []
    go ty (FixedType tyArg : descs')
      | Just (tyVar, ty') <- splitForAllTy_maybe ty
      = go (substTyWith [tyVar] [tyArg] ty') descs'
    go ty (FixedVoidArg : descs')
      | Just (argTy, retTy) <- splitFunTy_maybe ty
      = assert (argTy `eqType` voidPrimTy) $
        go retTy descs'
    go ty (TyArg tyVar : descs')
      | Just (tyVar', ty') <- splitForAllTy_maybe ty
      = assert (tyVar == tyVar') $
        KTExists tyVar (go ty' descs')
    go ty (ValArg argTy : descs')
      | Just (argTy', retTy) <- splitFunTy_maybe ty
      = assert (argTy `eqType` argTy') $
        argTy `consKT` go retTy descs'
    go _ _
      = pprPanic "idToJoinId" (pprBndr LetBind p $$ ppr descs)

    kontTypeToType :: KontType -> Type
    kontTypeToType = mkKontTy . go
      where 
        go (KTExists bndr kty) = mkUbxExistsTy bndr (go kty)
        go (KTTuple ktys)      = mkTupleTy UnboxedTuple (map go ktys)
        go (KTType ty)         = ty

    consKT :: Type -> KontType -> KontType
    ty `consKT` kty@KTExists {} = KTTuple [KTType ty, kty]
    ty `consKT` (KTTuple ktys)  = KTTuple (KTType ty : ktys)
    ty `consKT` (KTType ty2)    = KTTuple [KTType ty, KTType ty2]

-- Environment for contification --

data CfyEnv
  = CE { ce_mode       :: ContifySwitches
       , ce_subst      :: Subst      -- Renamings (var -> var only)
       , ce_floats     :: Floats
       , ce_kontId     :: KontId
       , ce_contifying :: IdEnv KontCallConv }
       
initCfyEnv :: ContifySwitches -> CfyEnv
initCfyEnv mode = CE { ce_mode       = mode
                     , ce_subst      = emptySubst
                     , ce_floats     = emptyFloats
                     , ce_kontId     = 0 -- always top-level continuation id
                     , ce_contifying = emptyVarEnv }

initCfyEnvForTerm :: ContifySwitches -> SeqCoreTerm -> CfyEnv
initCfyEnvForTerm mode term = (initCfyEnv mode) { ce_subst = freeVarSet }
  where
    freeVarSet = mkSubst (mkInScopeSet (freeVars term))
                   emptyVarEnv emptyVarEnv emptyVarEnv

bindAsContifying :: CfyEnv -> JoinId -> KontCallConv -> CfyEnv
bindAsContifying env j conv
  = env { ce_contifying = extendVarEnv (ce_contifying env) j conv }

bindAllAsContifying :: CfyEnv -> [(JoinId, KontCallConv)] -> CfyEnv
bindAllAsContifying env js = foldr (\(j, conv) env' -> bindAsContifying env' j conv) env js

kontCallConv :: CfyEnv -> Var -> Maybe KontCallConv
kontCallConv env var = lookupVarEnv (ce_contifying env) var 

zapSubst :: CfyEnv -> CfyEnv
zapSubst env = env { ce_subst = zapSubstEnv (ce_subst env) }

-- Monad --

type CfyM a = Writer CfyStats a

runCfyM :: CfyM a -> (CfyStats, a)
runCfyM m = (cst, a)
  where (a, cst) = runWriter m

cfyM :: (CfyStats, a) -> CfyM a
cfyM (cst, a) = writer (a, cst)

instance MonadCfyStats (Writer CfyStats) where
  writeStats = tell

-- Contification --

cfyInTopLevelBinds :: ContifySwitches -> MarkedProgram -> (CfyStats, SeqCoreProgram)
cfyInTopLevelBinds mode binds = runCfyM $ mapM cfy binds
  where
    cfy (_, AnnNonRec pair) = NonRec <$> do_pair pair
    cfy (_, AnnRec pairs)   = Rec <$> mapM do_pair pairs
    
    do_pair pair = cfyInRhs env TopLevel (unmark (binderOfAnnPair pair)) pair
    
    env = (initCfyEnv mode) { ce_subst = extendInScopeIds emptySubst bndrs }
      -- Start fresh for each top-level bind, since only locals can be contified
    bndrs = [ bndr | Marked bndr _ <- bindersOfAnnBinds binds ]

cfyInBind :: CfyEnv -> MarkedBind -> CfyM (CfyEnv, Maybe SeqCoreBind)
cfyInBind env bind =
  cfyM $ case bind of
    (_, AnnNonRec pair) ->
      case mark of MakeKont _ tgtKontId | tgtKontId /= ce_kontId env
                                       -> ASSERT(not (cs_gentle (ce_mode env)))
                                          (cst_float, (env_float tgtKontId, Nothing))
                   _                   -> (cst,       (env_no_float, Just bind'))
        where
          x@(Marked _ mark) = binderOfAnnPair pair
          
          (env', x')   = cfyInBndr env x
          (cst, pair') = runCfyM $ cfyInRhs env NotTopLevel x' pair
          cst_float    = cst <> emptyCfyStats { cst_bindsFloated = 1 }
          bind'        = NonRec pair'
          
          env_float tgtKontId
            = env' { ce_floats = addFloat (ce_floats env') tgtKontId bind' }
          env_no_float = env'

    (_, AnnRec pairs) ->
      case mark of MakeKont _ tgtKontId  | tgtKontId /= ce_kontId env
                                        -> ASSERT(not (cs_gentle (ce_mode env)))
                                           (cst_float, (env_float tgtKontId, Nothing))
                   _                    -> (cst,       (env_no_float, Just bind'))
        where
          xs@(Marked _ mark : _) = ASSERT(not (null pairs))
                                   map binderOfAnnPair pairs
          (env', xs')   = cfyInRecBndrs env xs
          (cst, pairs') = runCfyM $ zipWithM (cfyInRhs env' NotTopLevel) xs' pairs
          cst_float     = cst <> emptyCfyStats { cst_bindsFloated = length pairs }
          bind'         = Rec pairs'
          
          env_float tgtKontId
            = env' { ce_floats = addFloat (ce_floats env') tgtKontId bind' }
          env_no_float = env'

cfyInRhs :: CfyEnv -> TopLevelFlag -> Id -> MarkedBindPair -> CfyM SeqCoreBindPair
cfyInRhs env lvl x' (_, AnnBindTerm (Marked _ Keep) term)
  = do
    unless (isTopLevel lvl) $ writeStats (emptyCfyStats { cst_bindsTotal    = 1
                                                        , cst_bindsNotCfied = 1 })
    BindTerm x' <$> cfyInTerm env term
cfyInRhs env lvl j' (_, AnnBindTerm (Marked _ (MakeKont descs _)) term)
  = ASSERT(isNotTopLevel lvl)
    do
    writeStats cst
    writeStats (emptyCfyStats { cst_bindsTotal = 1
                              , cst_bindsCfied = 1 })
    BindJoin j' . Join xs <$> (writeStats cst >> body')
  where
    (cst, (env', xs, maybe_kontId, _, body)) = runCfyM $ etaExpandForJoinBody env descs term
    flts  = case maybe_kontId of Just kontId -> floatsAt (ce_floats env') kontId
                                 Nothing     -> []
    body' = addLets flts <$> cfyInComm env' body
cfyInRhs env lvl j' (_, AnnBindJoin (Marked _ Keep) join)
  = ASSERT(isNotTopLevel lvl)
    do
    writeStats (emptyCfyStats { cst_bindsTotal = 1
                              , cst_joinBinds  = 1 })
    BindJoin j' <$> cfyInJoin env join
cfyInRhs _ _ _ (_, AnnBindJoin (Marked j (MakeKont _ _)) _)
  = pprPanic "cfyInRhs" (text "Trying to contify a join point" $$ pprBndr LetBind j)

cfyInBndr :: CfyEnv -> MarkedVar -> (CfyEnv, Var)
cfyInBndr env (Marked bndr mark) = (env_final, bndr_final)
  where
    (subst', bndr') = substBndr (ce_subst env) bndr
    bndr''          = case mark of
                        MakeKont descs _ -> idToJoinId bndr' (ByJump descs)
                        Keep             -> bndr'
    bndr_final      = cfyInIdInfo (zapSubst env) mark bndr''
                        -- zapSubst because bndr'' was already substBndr'd
    subst_final     = extendInScope subst' bndr_final -- update stored version
    
    env'      = env { ce_subst = subst_final }
    env_final = case mark of
                  MakeKont descs _ -> bindAsContifying env' bndr_final (ByJump descs)
                  Keep             -> env'
    
cfyInRecBndrs :: CfyEnv -> [MarkedVar] -> (CfyEnv, [Var])
cfyInRecBndrs env markedBndrs = (env_final, bndrs_final)
  where
    (bndrs, marks)   = unzip [ (bndr, mark) | Marked bndr mark <- markedBndrs ]
    (subst', bndrs') = substRecBndrs (ce_subst env) bndrs
    bndrs''          = zipWith convert bndrs' marks
      where
        convert bndr (MakeKont descs _) = idToJoinId bndr (ByJump descs)
        convert bndr Keep               = bndr
    
    bndrs_final      = [ cfyInIdInfo env_bndrs mark bndr
                       | bndr <- bndrs'' | mark <- marks ]
    env_bndrs        = zapSubst env_final -- knot
    subst_final      = extendInScopeIds subst' bndrs_final
    
    env'      = env { ce_subst = subst_final }    
    env_final = bindAllAsContifying env' [ (bndr, ByJump descs) 
                                         | (bndr, MakeKont descs _) <- zip bndrs' marks ]
                                             -- okay to use old-ish binders
                                             -- because only unique is used as key
     
-- | Perform contification inside a binder's IdInfo. If the binder itself is
-- being contified, it should already have passed through idToJoinId, which sets
-- the type and arity accordingly. If the binding is recursive, the environment
-- should already be updated for the binder (in knot-tying fashion).
--
-- The binder should have passed through substBndr already, and accordingly the
-- environment's substitution should be zapped (with only an in-scope set).
cfyInIdInfo :: CfyEnv -> KontOrFunc -> Var -> Var
cfyInIdInfo env mark var
  | isTyVar var          = var
  | Keep <- mark
  , not (idHasRules var)
  , unf_is_boring        = var
  | otherwise            = var'
  where
    var' = var `setIdSpecialisation` specInfo'
               `setIdUnfolding` unf'
    
    unf = realIdUnfolding var
    unf_is_boring = case unf of Core.NoUnfolding -> True
                                Core.OtherCon {} -> True
                                _                -> False

    specInfo' = case idSpecialisation var of
                  SpecInfo rules fvs -> SpecInfo (map (cfyInRule env) rules)
                                                 (substVarSet (ce_subst env) fvs)
                                                   -- update with new IdInfo
    unf' = cfyInUnfolding env var mark unf

cfyInTerm :: CfyEnv -> MarkedTerm -> CfyM SeqCoreTerm
cfyInTerm _   (_, AnnLit lit)         = return $ Lit lit
cfyInTerm env (_, AnnType ty)         = return $ Type (substTy (ce_subst env) ty)
cfyInTerm env (_, AnnCoercion co)     = return $ Coercion (substCo (ce_subst env) co)
cfyInTerm env (_, AnnVar x)           = ASSERT2(isNothing (kontCallConv env x_new), ppr x_new)
                                        return $ Var x_new
  where x_new = substIdOccAndRefine (ce_subst env) x
cfyInTerm env (k, AnnCompute ty comm) | null flts
                                      , (_, AnnEval (_, AnnVar x) []
                                                    (_, AnnReturn)) <- comm
                                      = cfyInTerm env' (nkb, AnnVar x)
                                          -- Eta-expanded by case analysis
                                      | otherwise
                                      = Compute (substTy (ce_subst env) ty) . addLets flts
                                                <$> cfyInComm env' comm
  where
    flts = floatsAt (ce_floats env) k 
    env' = env { ce_kontId = k }    
cfyInTerm env (_, AnnLam (Marked x mark) body)
  = ASSERT2(isKeep mark, ppr x)
    Lam x' <$> body'
  where
    (subst', x') = substBndr (ce_subst env) x
    -- Lambda variables can have unfoldings, but those unfoldings are only ever
    -- constructor applications to variables, so no need to worry about contifying
    body' = cfyInTerm (env { ce_subst = subst' }) body

cfyInComm :: CfyEnv -> MarkedCommand -> CfyM SeqCoreCommand
cfyInComm env (_, AnnLet bind comm)
  = do
    (env', maybe_bind') <- cfyInBind env bind
    comm'               <- cfyInComm env' comm
    return $ maybe id Let maybe_bind' comm'

cfyInComm env (_, AnnJump args j)
  = Jump <$> mapM (cfyInTerm env) args <*> pure (substIdOccAndRefine (ce_subst env) j)
cfyInComm env (_, AnnEval (_, AnnVar x) frames end)
  | let j' = substIdOccAndRefine (ce_subst env) x
  , Just (ByJump descs) <- kontCallConv env j'
  = ASSERT2(all (isAppFrame . deAnnotateFrame) frames, ppr x $$ ppr (map deAnnotateFrame frames))
    ASSERT2(isReturn (deAnnotateEnd end), ppr (deAnnotateEnd end))
    let args  = removeFixedArgs [ arg | (_, AnnApp arg) <- frames ] descs
        args' = mapM (cfyInTerm env) args
    in Jump <$> args' <*> pure j'
cfyInComm env (_, AnnEval term frames end)
  = Eval <$> cfyInTerm env term <*> mapM (cfyInFrame env) frames <*> cfyInEnd env end

cfyInFrame :: CfyEnv -> MarkedFrame -> CfyM SeqCoreFrame
cfyInFrame env (_, AnnApp arg) = App <$> (cfyInTerm env arg)
cfyInFrame env (_, AnnCast co) = return $ Cast (substCo (ce_subst env) co)
cfyInFrame env (_, AnnTick ti) = return $ Tick (substTickish (ce_subst env) ti)

cfyInEnd :: CfyEnv -> MarkedEnd -> CfyM SeqCoreEnd
cfyInEnd _   (_, AnnReturn)                       = return Return
cfyInEnd env (_, AnnCase (Marked bndr mark) alts) = ASSERT2(isKeep mark, ppr bndr)
                                                    Case bndr' <$> alts'
  where
    (subst', bndr') = substBndr (ce_subst env) bndr
    alts'           = mapM (cfyInAlt (env { ce_subst = subst' })) alts

cfyInAlt :: CfyEnv -> MarkedAlt -> CfyM SeqCoreAlt
cfyInAlt env (_, AnnAlt con mbndrs rhs) = ASSERT2(all isKeep marks, ppr mbndrs)
                                          Alt con bndrs' <$> rhs'
  where
    (bndrs, marks)   = unzip [ (bndr, mark) | Marked bndr mark <- mbndrs ]
    (subst', bndrs') = substBndrs (ce_subst env) bndrs
    rhs'             = cfyInComm (env { ce_subst = subst' }) rhs

cfyInJoin :: CfyEnv -> MarkedJoin -> CfyM SeqCoreJoin
cfyInJoin env (_, AnnJoin mbndrs body) = ASSERT2(all isKeep marks, ppr mbndrs)
                                         Join bndrs' <$> body'
  where
    (bndrs, marks)   = unzip [ (bndr, mark) | Marked bndr mark <- mbndrs ]
    (subst', bndrs') = substBndrs (ce_subst env) bndrs
    body'            = cfyInComm (env { ce_subst = subst' }) body

cfyInRule :: CfyEnv -> Core.CoreRule -> Core.CoreRule
cfyInRule _   rule@(Core.BuiltinRule {}) = rule
cfyInRule env rule@(Core.Rule { Core.ru_bndrs = bndrs, Core.ru_args = args, Core.ru_rhs = rhs })
  = rule { Core.ru_bndrs = bndrs', Core.ru_args = map cfy args, Core.ru_rhs = cfy rhs }
  where
    (subst', bndrs') = substBndrs (ce_subst env) bndrs
    env' = env { ce_subst = subst' }
    cfy expr = expr'
      where
        term = termFromCoreExprNoContify expr
        comm = case term of Compute _ body -> body
                            other          -> Eval other [] Return
        (_, comm_ann) = runEscM (ce_mode env) $ escAnalComm comm
        (_, comm')    = runCfyM (cfyInComm env' comm_ann)
        expr'         = commandToCoreExpr (termType term) comm'

cfyInUnfolding :: CfyEnv -> Id -> KontOrFunc -> Unfolding -> Unfolding
cfyInUnfolding env id mark unf
  = case unf of
      Core.CoreUnfolding { Core.uf_src = src, Core.uf_tmpl = tmpl, Core.uf_arity = arity
                         , Core.uf_is_top = is_top, Core.uf_guidance = guid }
        | not (Core.isStableSource (Core.uf_src unf)) -> Core.NoUnfolding -- don't bother
        | otherwise -> mkCoreUnfolding src is_top tmpl' arity' guid'
            where
              (_, term) = runEscM (ce_mode env) $ escAnalTerm (termFromCoreExprNoContify tmpl)
              
              (tmpl', arity', guid')
                = case mark of
                    Keep
                      | isJoinId id ->
                          (joinToCoreExpr (termType (deAnnotateTerm bodyTerm)) join', arity, guid)
                      | otherwise ->
                          (termToCoreExpr term', arity, guid)
                      where
                        (_, term') = runCfyM $ cfyInTerm env term
                        join = (nkb, AnnJoin bndrs body)
                        (_, join') = runCfyM $ cfyInJoin env join
                        -- It's possible there are too many binders (greater than the
                        -- arity of the join point, which is determined by the
                        -- callers), so in general we must put some back.
                        (allBndrs, innerBody) = collectAnnBinders term
                        (bndrs, extraBndrs) = splitAt arity allBndrs
                        bodyTerm = foldr (\x v -> (nkb, AnnLam x v)) innerBody extraBndrs
                        body = case bodyTerm of
                                 (_, AnnCompute _ comm) -> comm
                                 other                  -> (nkb, AnnEval other [] (nkb, AnnReturn))
                    MakeKont descs _
                      -> (joinToCoreExpr ty join, arity', guid')
                      where
                        join = Join bndrs body'
                        (_, (env', bndrs, _, ty, body)) = runCfyM $ etaExpandForJoinBody env descs term
                        (_, body') = runCfyM $ cfyInComm env' body
                        arity' = count isValArgDesc descs `min` 1
                        guid' = fixGuid descs guid
      Core.DFunUnfolding { Core.df_bndrs = bndrs, Core.df_con = con, Core.df_args = args } ->
        warnPprTrace (case mark of MakeKont {} -> True; _ -> False) __FILE__ __LINE__
          (text "Trying to contify a dictionary??" $$ pprBndr LetBind id) $
        mkDFunUnfolding bndrs' con args'
        where
          (subst', bndrs') = substBndrs (ce_subst env) bndrs
          env' = env { ce_subst = subst' }
          args' = map (onCoreExpr (snd . runCfyM . cfyInTerm env' . snd . runEscM (ce_mode env) . escAnalTerm)) args
      _ -> unf
  where
    fixGuid descs guid@(Core.UnfIfGoodArgs { Core.ug_args = args })
      | not (any isValArgDesc descs)
      = guid { Core.ug_args = [0] } -- We keep a single Void# lambda in the unfolding
      | otherwise
      = guid { Core.ug_args = fixArgs args descs }
    fixGuid _ guid = guid
    
    fixArgs allArgs allDescs = go allArgs allDescs
      where
        go [] [] = []
        go [] (ValArg _ : _)
          = warnPprTrace True __FILE__ __LINE__
              (text "Out of value discounts" $$
               text "Unfolding:" <+> ppr unf $$
               text "Arg descs:" <+> ppr allDescs)
            []
        go args []
          = warnPprTrace True __FILE__ __LINE__
              (text "Leftover arg discounts:" <+> ppr args $$
               text "Unfolding:" <+> ppr unf $$
               text "Arg descs:" <+> ppr allDescs)
            []
        go (arg:args) (ValArg _ : descs)
          = arg : go args descs
        go (_:args) (FixedVoidArg : descs)
          = go args descs
        go args (_ : descs) -- Type argument (fixed or variable)
          = go args descs


etaExpandForJoinBody :: CfyEnv -> [ArgDesc] -> MarkedTerm
                     -> CfyM (CfyEnv, [Var], Maybe KontId, Type, MarkedCommand)
etaExpandForJoinBody env descs term
  = cfyM (cst, (env_final, bndrs_final, swallowedKontId, ty, etaBody))
  where
    -- Calculate outer binders (existing ones from expr, minus fixed args)
    (bndrs, body) = collectNBinders (length descs) term
    bndrs_unmarked = identifiers bndrs
    subst = ce_subst env
    (subst', bndr_maybes) = mapAccumL doBndr subst (zip bndrs_unmarked descs)
    bndrs' = catMaybes bndr_maybes

    -- Calculate eta-expanding binders and arguments
    extraArgs = drop (length bndrs) descs -- will need to eta-expand with these
    (subst_final, unzip -> (etaBndr_maybes, etaArgs))
      = mapAccumL mkEtaBndr subst' (zip [1..] extraArgs)
    etaBndrs = catMaybes etaBndr_maybes
    bndrs_final = bndrs' ++ etaBndrs
    
    env' = case swallowedKontId of Just kontId' -> env { ce_kontId = kontId' }
                                   Nothing      -> env
    env_final = env' { ce_subst = subst_final }
    
    -- Create new join body
    etaFrames = map ((nkb,) . AnnApp) etaArgs
    (etaBody, swallowedKontId)
      | null etaFrames, (kontId, AnnCompute _ty comm) <- body
      = (comm, Just kontId)
      | otherwise
      = ((nkb, AnnEval body etaFrames (nkb, AnnReturn)), Nothing)
    
    ty = foldl (\ty frTy -> substTy subst_final (frameType ty frTy))
               (substTy subst_final . termType . deAnnotateTerm $ body)
               (map deAnnotateFrame etaFrames)
    
    cst = emptyCfyStats { cst_etaExpanded = if null extraArgs then 0 else 1 
                        , cst_splitLams   = case body of (_, AnnLam {}) -> 1; _ -> 0
                        , cst_typeFixed   = if any is_fixed_type descs then 1 else 0 }
      where
        is_fixed_type (FixedType _) = True
        is_fixed_type _             = False
    
    -- Process a binder, possibly dropping it, and return a new subst
    doBndr :: Subst -> (Var, ArgDesc) -> (Subst, Maybe Var)
    doBndr subst (bndr, FixedType ty)
      = (CoreSubst.extendTvSubst subst bndr (substTy subst ty), Nothing)
    doBndr subst (bndr, FixedVoidArg)
      -- Usually, a binder for a Void# is dead, but in case it's not, take the
      -- argument to be void#. Note that, under the let/app invariant, any
      -- argument of unlifted type must be ok-for-speculation, and any
      -- ok-for-speculation expression of Void# is equal to void# (it can't be
      -- _|_ or have side effects or possible errors and still be OFS; it could
      -- still be case x +# y of z -> void#, but then we can eliminate the case).
      -- So this is always correct.
      = (extendSubstWithVar subst bndr voidPrimId, Nothing)
    doBndr subst (bndr, TyArg tyVar)
      = (subst'', Just bndr')
      where
        (subst', bndr') = substBndr subst bndr
        -- Further ArgInfos may refer to tyVar, so we need to substitute to get
        -- the right types for generated arguments (when eta-expanding).
        subst'' = CoreSubst.extendTvSubst subst' tyVar (mkTyVarTy bndr')
    doBndr subst (bndr, ValArg _)
      = (subst', Just bndr')
      where
        (subst', bndr') = substBndr subst bndr

    -- From an ArgDesc, generate an argument to apply and (possibly) a parameter
    -- to the eta-expanded function
    mkEtaBndr :: Subst -> (Int, ArgDesc) -> (Subst, (Maybe Var, MarkedTerm))
    mkEtaBndr subst (_, FixedType ty)
      = (subst, (Nothing, (nkb, AnnType (substTy subst ty))))
    mkEtaBndr subst (_, FixedVoidArg)
      = (subst, (Nothing, (nkb, AnnVar voidPrimId)))
    mkEtaBndr subst (_, TyArg tyVar)
      = (subst', (Just tv', (nkb, AnnType (mkTyVarTy tv'))))
      where
        (subst', tv') = substBndr subst tyVar
    mkEtaBndr subst (n, ValArg ty)
      = (subst', (Just x, (nkb, AnnVar x)))
      where
        (subst', x) = freshEtaId n subst ty
        
    collectNBinders :: TotalArity -> MarkedTerm -> ([MarkedVar], MarkedTerm)
    collectNBinders = go []
      where
        go acc n (_, AnnLam x e) | n /= 0 = go (x:acc) (n-1) e
        go acc _ e                        = (reverse acc, e)

----------------
-- Miscellany --
----------------

instance Outputable CfyStats where
  ppr ZeroCfyStats = ppr emptyCfyStats
  ppr (CfyStats { cst_bindsTotal    = tot,    cst_joinBinds     = js
                , cst_bindsCfied    = cfied,  cst_bindsNotCfied = not_cfied
                , cst_bindsFloated  = fltd
                , cst_splitLams     = split,  cst_etaExpanded   = etad
                , cst_typeFixed     = fixed,  cst_polyFail      = poly_fails
                , cst_dontCfyRules  = rules
                , cst_scopeMismatch = sc_mis, cst_arityMismatch = ar_mis })
    = vcat [ text "    Local Binds:" <+> int tot
           , text "--------------------"
           , text "  Already Joins:" <+> with_pct js tot
           , text "  Not Contified:" <+> with_pct not_cfied tot
           , text "      Contified:" <+> with_pct cfied tot
           , blankLine
           , text "      Contified:" <+> int cfied
           , text "--------------------"
           , text "     Floated In:" <+> with_pct fltd cfied
           , text "     Lost Arity:" <+> with_pct split cfied
           , text "   Eta-Expanded:" <+> with_pct etad cfied
           , text "  Monomorphosed:" <+> with_pct fixed cfied
           , blankLine
           , text "  Not Contified:" <+> int not_cfied
           , text "--------------------"
           , text "    Wrong Scope:" <+> with_pct sc_mis not_cfied
           , text "    Wrong Arity:" <+> with_pct ar_mis not_cfied
           , text "     Can't Mono:" <+> with_pct poly_fails not_cfied
           , text "      Has Rules:" <+> with_pct rules not_cfied
           ]
    where
      with_pct 0 0 = int 0
      with_pct num den = ppr num <+> parens (pct num den)
      pct num den = text (showFFloat (Just 2)
                           (fromIntegral num * (100.0 :: Float) / fromIntegral den)
                           "%")

instance Outputable EscapeAnalysis where
  ppr (EA { ea_calls = calls, ea_allVars = allVars, ea_kstates = kstates })
    = text "   calls:" <+> ppr calls $$
      text "escaping:" <+> ppr (allVars `minusVarEnv` calls) $$
      text " kstates:" <+> text (show kstates)

instance Outputable EscEnv where
  ppr (EE { ee_mode = mode, ee_cands = cands, ee_kontId = kid })
    = brackets $ sep [ text "Mode:" Out.<> ppr mode
                     , text "Scope:" Out.<> ppr kid
                     , text "Candidates:" Out.<> ppr (varSetElems cands) ]

instance Outputable CallInfo where
  ppr (CI { ci_arity = arity, ci_kontId = kid })
    = int arity <+> text "args @" Out.<> int kid

instance Outputable Occs where
  ppr Abs = text "abs"
  ppr Esc = text "esc"
  ppr (NonEsc ci region) = text "non-esc" <+> parens (ppr region) Out.<> colon
                                          <+> ppr ci

instance Outputable CallRegion where
  ppr Inside      = text "inside"
  ppr Outside     = text "outside"
  ppr DeepOutside = text "deep outside"
  ppr Barred      = text "barred"

instance Outputable KontOrFunc where
  ppr Keep = text "keep"
  ppr (MakeKont _ tgtKontId) = text "cont @" Out.<> int tgtKontId

instance Outputable KontState where
  ppr (ChildOf parent disp) = text rel <+> ppr parent
    where rel = case disp of Child   -> "child of"
                             Merged  -> "merged with"
                             Barrier -> "barrier at" 

instance Outputable MarkedVar where
  ppr (Marked var mark) = ppr var <+> brackets (ppr mark)

instance OutputableBndr MarkedVar where
  pprBndr site (Marked var Keep) = pprBndr site var
  pprBndr site (Marked var mark) = pprBndr site var <+> brackets (ppr mark)
  pprPrefixOcc (Marked var _) = pprPrefixOcc var
  pprInfixOcc  (Marked var _) = pprInfixOcc  var

instance Outputable ArgDesc where
  ppr (FixedType ty) = text "fixed type:" <+> ppr ty
  ppr FixedVoidArg   = text "fixed void#"
  ppr (TyArg tyVar)  = text "type arg:" <+> pprBndr LambdaBind tyVar
  ppr (ValArg ty)    = text "arg of type" <+> ppr ty

-- copied from CoreArity
freshEtaId :: Int -> Subst -> Type -> (Subst, Id)
freshEtaId n subst ty
      = (subst', eta_id')
      where
        ty'     = substTy subst ty
        eta_id' = uniqAway (substInScope subst) $
                  mkSysLocal (fsLit "cfyeta") (mkBuiltinUnique n) ty'
        subst'  = extendInScope subst eta_id'

-- Fix shortcoming in CoreSubst: returned substed id not refined by in-scope set
substIdOccAndRefine :: Subst -> Id -> Var
substIdOccAndRefine subst id
  = lookupInScope (substInScope subst) id' `orElse` id'
  where
    id' = substIdOcc subst id

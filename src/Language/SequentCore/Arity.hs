-- | 
-- Module      : Language.SequentCore.Arity
-- Description : Arity analysis and eta-expansion
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Arity and eta expansion

{-
%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%

        Arity and eta expansion

-}
{-# LANGUAGE CPP, ViewPatterns #-}
{-# OPTIONS -fno-warn-tabs #-}

module Language.SequentCore.Arity (
        manifestArity, termArity, termBotStrictness_maybe,
        termEtaExpandArity, findRhsArity, CheapMeasure, etaExpand, etaExpandRhs
    ) where

import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import CoreFVs ( exprFreeVars )
import CoreSyn ( tickishIsCode )
import CoreSubst
import Demand
import Var
import VarEnv
import Id
import Type
import TyCon    ( initRecTc, checkRecTc )
import Coercion
import BasicTypes
import Unique
import DynFlags ( DynFlags, GeneralFlag(..), gopt )
import Outputable
import FastString
import Pair

import Control.Exception ( assert )
{-

%************************************************************************
%*                                                                      *
              manifestArity and termArity
%*                                                                      *
%************************************************************************

termArity is a cheap-and-cheerful version of termEtaExpandArity.
It tells how many things the expression can be applied to before doing
any work.  It doesn't look inside cases, lets, etc.  The idea is that
termEtaExpandArity will do the hard work, leaving something that's easy
for termArity to grapple with.  In particular, Simplify uses termArity to
compute the ArityInfo for the Id. 

Originally I thought that it was enough just to look for top-level lambdas, but
it isn't.  I've seen this

        foo = PrelBase.timesInt

We want foo to get arity 2 even though the eta-expander will leave it
unchanged, in the expectation that it'll be inlined.  But occasionally it
isn't, because foo is blacklisted (used in a rule).  

Similarly, see the ok_note check in termEtaExpandArity.  So 
        f = __inline_me (\x -> e)
won't be eta-expanded.

And in any case it seems more robust to have termArity be a bit more intelligent.
But note that   (\x y z -> f x y z)
should have arity 3, regardless of f's arity.

-}
manifestArity :: SeqCoreTerm -> Arity
-- ^ manifestArity sees how many leading value lambdas there are
manifestArity v
  = go v
  where
    go (Lam v e)                      | isId v      = 1 + go e
                                      | otherwise   = go e
    go (Compute _ (Eval v fs Return)) | all skip fs = go v
    go _                                            = 0
    
    skip (Tick ti) = not (tickishIsCode ti)
    skip (Cast _)  = True
    skip (App _)   = False

---------------
termArity :: SeqCoreTerm -> Arity
-- ^ An approximate, fast, version of 'termEtaExpandArity'
termArity e = goT e
  where
    goT (Var v)                    = idArity v
    goT (Lam x e) | isId x         = goT e + 1
                  | otherwise      = goT e
    goT (Compute _ (Eval v fs e))  = goF v fs e
    goT _                          = 0
    
    goF v (Tick t : fs)  e | not (tickishIsCode t)
                           = goF v fs e
    goF v (Cast co : fs) e = trim_arity (goF v fs e) (pSnd (coercionKind co))
                                   -- Note [termArity invariant]
    goF v (App a : fs) e   | Type {} <- a
                           = goF v fs e
                           | isTrivialTerm a
                           = (goF v fs e - 1) `max` 0
        -- See Note [termArity for applications]
        -- NB: coercions count as a value argument
    goF v [] Return        = goT v
    goF _ _ _              = 0

    trim_arity :: Arity -> Type -> Arity
    trim_arity arity ty = arity `min` length (typeArity ty)

---------------
typeArity :: Type -> [OneShotInfo]
-- How many value arrows are visible in the type?
-- We look through foralls, and newtypes
-- See Note [termArity invariant]
typeArity ty 
  = go initRecTc ty
  where
    go rec_nts ty 
      | Just (_, ty')  <- splitForAllTy_maybe ty 
      = go rec_nts ty'

      | Just (arg,res) <- splitFunTy_maybe ty    
      = typeOneShot arg : go rec_nts res
      | Just (tc,tys) <- splitTyConApp_maybe ty 
      , Just (ty', _) <- instNewTyCon_maybe tc tys
      , Just rec_nts' <- checkRecTc rec_nts tc  -- See Note [Expanding newtypes]
                                                -- in TyCon
--   , not (isClassTyCon tc)    -- Do not eta-expand through newtype classes
--                              -- See Note [Newtype classes and eta expansion]
--                              (no longer required)
      = go rec_nts' ty'
        -- Important to look through non-recursive newtypes, so that, eg 
        --      (f x)   where f has arity 2, f :: Int -> IO ()
        -- Here we want to get arity 1 for the result!
        --
        -- AND through a layer of recursive newtypes
        -- e.g. newtype Stream m a b = Stream (m (Either b (a, Stream m a b)))

      | otherwise
      = []

---------------
termBotStrictness_maybe :: SeqCoreTerm -> Maybe (Arity, StrictSig)
-- A cheap and cheerful function that identifies bottoming functions
-- and gives them a suitable strictness signatures.  It's used during
-- float-out
termBotStrictness_maybe e
  = case getBotArity (arityType env e) of
        Nothing -> Nothing
        Just ar -> Just (ar, sig ar)
  where
    env    = AE { ae_bndrs = [], ae_ped_bot = True, ae_cheap_fn = \ _ _ -> False }
    sig ar = mkClosedStrictSig (replicate ar topDmd) botRes
                  -- For this purpose we can be very simple
{-

Note [termArity invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~~
termArity has the following invariant:

  (1) If typeArity (exprType e) = n,
      then manifestArity (etaExpand e n) = n
 
      That is, etaExpand can always expand as much as typeArity says
      So the case analysis in etaExpand and in typeArity must match
 
  (2) termArity e <= typeArity (exprType e)      

  (3) Hence if (termArity e) = n, then manifestArity (etaExpand e n) = n

      That is, if termArity says "the arity is n" then etaExpand really 
      can get "n" manifest lambdas to the top.

Why is this important?  Because 
  - In TidyPgm we use termArity to fix the *final arity* of 
    each top-level Id, and in
  - In CorePrep we use etaExpand on each rhs, so that the visible lambdas
    actually match that arity, which in turn means
    that the StgRhs has the right number of lambdas

An alternative would be to do the eta-expansion in TidyPgm, at least
for top-level bindings, in which case we would not need the trim_arity
in termArity.  That is a less local change, so I'm going to leave it for today!

Note [Newtype classes and eta expansion]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    NB: this nasty special case is no longer required, because
    for newtype classes we don't use the class-op rule mechanism
    at all.  See Note [Single-method classes] in TcInstDcls. SLPJ May 2013

-------- Old out of date comments, just for interest -----------
We have to be careful when eta-expanding through newtypes.  In general
it's a good idea, but annoyingly it interacts badly with the class-op 
rule mechanism.  Consider
 
   class C a where { op :: a -> a }
   instance C b => C [b] where
     op x = ...

These translate to

   co :: forall a. (a->a) ~ C a

   $copList :: C b -> [b] -> [b]
   $copList d x = ...

   $dfList :: C b -> C [b]
   {-# DFunUnfolding = [$copList] #-}
   $dfList d = $copList d |> co@[b]

Now suppose we have:

   dCInt :: C Int    

   blah :: [Int] -> [Int]
   blah = op ($dfList dCInt)

Now we want the built-in op/$dfList rule will fire to give
   blah = $copList dCInt

But with eta-expansion 'blah' might (and in Trac #3772, which is
slightly more complicated, does) turn into

   blah = op (\eta. ($dfList dCInt |> sym co) eta)

and now it is *much* harder for the op/$dfList rule to fire, because
exprIsConApp_maybe won't hold of the argument to op.  I considered
trying to *make* it hold, but it's tricky and I gave up.

The test simplCore/should_compile/T3722 is an excellent example.
-------- End of old out of date comments, just for interest -----------


Note [termArity for applications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When we come to an application we check that the arg is trivial.
   eg  f (fac x) does not have arity 2, 
                 even if f has arity 3!

* We require that is trivial rather merely cheap.  Suppose f has arity 2.
  Then    f (Just y)
  has arity 0, because if we gave it arity 1 and then inlined f we'd get
          let v = Just y in \w. <f-body>
  which has arity 0.  And we try to maintain the invariant that we don't
  have arity decreases.

*  The `max 0` is important!  (\x y -> f x) has arity 2, even if f is
   unknown, hence arity 0


%************************************************************************
%*                                                                      *
           Computing the "arity" of an expression
%*                                                                      *
%************************************************************************

Note [Definition of arity]
~~~~~~~~~~~~~~~~~~~~~~~~~~
The "arity" of an expression 'e' is n if
   applying 'e' to *fewer* than n *value* arguments
   converges rapidly

Or, to put it another way

   there is no work lost in duplicating the partial
   application (e x1 .. x(n-1))

In the divegent case, no work is lost by duplicating because if the thing
is evaluated once, that's the end of the program.

Or, to put it another way, in any context C

   C[ (\x1 .. xn. e x1 .. xn) ]
         is as efficient as
   C[ e ]

It's all a bit more subtle than it looks:

Note [One-shot lambdas]
~~~~~~~~~~~~~~~~~~~~~~~
Consider one-shot lambdas
                let x = expensive in \y z -> E
We want this to have arity 1 if the \y-abstraction is a 1-shot lambda.

Note [Dealing with bottom]
~~~~~~~~~~~~~~~~~~~~~~~~~~
A Big Deal with computing arities is expressions like

   f = \x -> case x of
               True  -> \s -> e1
               False -> \s -> e2

This happens all the time when f :: Bool -> IO ()
In this case we do eta-expand, in order to get that \s to the
top, and give f arity 2.

This isn't really right in the presence of seq.  Consider
        (f bot) `seq` 1

This should diverge!  But if we eta-expand, it won't.  We ignore this
"problem" (unless -fpedantic-bottoms is on), because being scrupulous
would lose an important transformation for many programs. (See 
Trac #5587 for an example.)

Consider also
        f = \x -> error "foo"
Here, arity 1 is fine.  But if it is
        f = \x -> case x of 
                        True  -> error "foo"
                        False -> \y -> x+y
then we want to get arity 2.  Technically, this isn't quite right, because
        (f True) `seq` 1
should diverge, but it'll converge if we eta-expand f.  Nevertheless, we
do so; it improves some programs significantly, and increasing convergence
isn't a bad thing.  Hence the ABot/ATop in ArityType.

So these two transformations aren't always the Right Thing, and we
have several tickets reporting unexpected bahaviour resulting from
this transformation.  So we try to limit it as much as possible:

 (1) Do NOT move a lambda outside a known-bottom case expression
       case undefined of { (a,b) -> \y -> e }
     This showed up in Trac #5557

 (2) Do NOT move a lambda outside a case if all the branches of 
     the case are known to return bottom.
        case x of { (a,b) -> \y -> error "urk" }
     This case is less important, but the idea is that if the fn is 
     going to diverge eventually anyway then getting the best arity 
     isn't an issue, so we might as well play safe

 (3) Do NOT move a lambda outside a case unless 
     (a) The scrutinee is ok-for-speculation, or
     (b) There is an enclosing value \x, and the scrutinee is x
         E.g.  let x = case y of ( DEFAULT -> \v -> blah }
     We don't move the \y out.  This is pretty arbitrary; but it
     catches the common case of doing `seq` on y.
     This is the reason for the under_lam argument to arityType.
     See Trac #5625

Of course both (1) and (2) are readily defeated by disguising the bottoms.

4. Note [Newtype arity]
~~~~~~~~~~~~~~~~~~~~~~~~
Non-recursive newtypes are transparent, and should not get in the way.
We do (currently) eta-expand recursive newtypes too.  So if we have, say

        newtype T = MkT ([T] -> Int)

Suppose we have
        e = coerce T f
where f has arity 1.  Then: etaExpandArity e = 1; 
that is, etaExpandArity looks through the coerce.

When we eta-expand e to arity 1: eta_expand 1 e T
we want to get:                  coerce T (\x::[T] -> (coerce ([T]->Int) e) x)

  HOWEVER, note that if you use coerce bogusly you can ge
        coerce Int negate
  And since negate has arity 2, you might try to eta expand.  But you can't
  decopose Int to a function type.   Hence the final case in eta_expand.
  
Note [The state-transformer hack]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have 
        f = e
where e has arity n.  Then, if we know from the context that f has
a usage type like
        t1 -> ... -> tn -1-> t(n+1) -1-> ... -1-> tm -> ...
then we can expand the arity to m.  This usage type says that
any application (x e1 .. en) will be applied to uniquely to (m-n) more args
Consider f = \x. let y = <expensive> 
                 in case x of
                      True  -> foo
                      False -> \(s:RealWorld) -> e
where foo has arity 1.  Then we want the state hack to
apply to foo too, so we can eta expand the case.

Then we expect that if f is applied to one arg, it'll be applied to two
(that's the hack -- we don't really know, and sometimes it's false)
See also Id.isOneShotBndr.

Note [State hack and bottoming functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It's a terrible idea to use the state hack on a bottoming function.
Here's what happens (Trac #2861):

  f :: String -> IO T
  f = \p. error "..."

Eta-expand, using the state hack:

  f = \p. (\s. ((error "...") |> g1) s) |> g2
  g1 :: IO T ~ (S -> (S,T))
  g2 :: (S -> (S,T)) ~ IO T

Extrude the g2

  f' = \p. \s. ((error "...") |> g1) s
  f = f' |> (String -> g2)

Discard args for bottomming function

  f' = \p. \s. ((error "...") |> g1 |> g3
  g3 :: (S -> (S,T)) ~ (S,T)

Extrude g1.g3

  f'' = \p. \s. (error "...")
  f' = f'' |> (String -> S -> g1.g3)

And now we can repeat the whole loop.  Aargh!  The bug is in applying the
state hack to a function which then swallows the argument.

This arose in another guise in Trac #3959.  Here we had

     catch# (throw exn >> return ())

Note that (throw :: forall a e. Exn e => e -> a) is called with [a = IO ()].
After inlining (>>) we get 

     catch# (\_. throw {IO ()} exn)

We must *not* eta-expand to 

     catch# (\_ _. throw {...} exn)

because 'catch#' expects to get a (# _,_ #) after applying its argument to
a State#, not another function!  

In short, we use the state hack to allow us to push let inside a lambda,
but not to introduce a new lambda.


Note [ArityType]
~~~~~~~~~~~~~~~~
ArityType is the result of a compositional analysis on expressions,
from which we can decide the real arity of the expression (extracted
with function termEtaExpandArity).

Here is what the fields mean. If an arbitrary expression 'f' has 
ArityType 'at', then

 * If at = ABot n, then (f x1..xn) definitely diverges. Partial
   applications to fewer than n args may *or may not* diverge.

   We allow ourselves to eta-expand bottoming functions, even
   if doing so may lose some `seq` sharing, 
       let x = <expensive> in \y. error (g x y)
       ==> \y. let x = <expensive> in error (g x y)

 * If at = ATop as, and n=length as, 
   then expanding 'f' to (\x1..xn. f x1 .. xn) loses no sharing, 
   assuming the calls of f respect the one-shot-ness of of
   its definition.  

   NB 'f' is an arbitary expression, eg (f = g e1 e2).  This 'f'
   can have ArityType as ATop, with length as > 0, only if e1 e2 are 
   themselves.

 * In both cases, f, (f x1), ... (f x1 ... f(n-1)) are definitely
   really functions, or bottom, but *not* casts from a data type, in
   at least one case branch.  (If it's a function in one case branch but
   an unsafe cast from a data type in another, the program is bogus.)
   So eta expansion is dynamically ok; see Note [State hack and
   bottoming functions], the part about catch#

Example: 
      f = \x\y. let v = <expensive> in 
          \s(one-shot) \t(one-shot). blah
      'f' has ArityType [ManyShot,ManyShot,OneShot,OneShot]
      The one-shot-ness means we can, in effect, push that
      'let' inside the \st.


Suppose f = \xy. x+y
Then  f             :: AT [False,False] ATop
      f v           :: AT [False]       ATop
      f <expensive> :: AT []            ATop

-------------------- Main arity code ----------------------------
-}
data ArityType = ATop | AOkSpec | AArr OneShotInfo ArityType | ABot Arity
data CoArityType = CTop | CApp CheapFlag CoArityType | CCase ArityType
                        | CTrunc Arity CoArityType

data CheapFlag = Cheap | NotCheap

aTop :: [OneShotInfo] -> ArityType
aTop = foldr AArr ATop

cheapFlag :: Bool -> CheapFlag
cheapFlag True  = Cheap
cheapFlag False = NotCheap

-- ^ The Arity returned is the number of value args the
-- expression can be applied to without doing much work
termEtaExpandArity :: DynFlags -> SeqCoreTerm -> Arity
-- termEtaExpandArity is used when eta expanding
--      e  ==>  \xy -> e x y
termEtaExpandArity dflags e
  = arityTypeArity (arityType env e)
  where
    env = AE { ae_bndrs    = []
             , ae_cheap_fn = mk_cheap_fn dflags isCheapApp
             , ae_ped_bot  = gopt Opt_PedanticBottoms dflags }

getBotArity :: ArityType -> Maybe Arity
-- Arity of a divergent function
getBotArity (ABot n) = Just n
getBotArity _        = Nothing

arityTypeArity :: ArityType -> Arity
arityTypeArity ATop        = 0
arityTypeArity AOkSpec     = 0
arityTypeArity (ABot a)    = a
arityTypeArity (AArr _ at) = 1 + arityTypeArity at

mk_cheap_fn :: DynFlags -> CheapAppMeasure -> CheapMeasure
mk_cheap_fn dflags cheap_app
  | not (gopt Opt_DictsCheap dflags)
  = \e _     -> termIsCheapBy cheap_app e
  | otherwise
  = \e mb_ty -> termIsCheapBy cheap_app e
             || case mb_ty of
                  Nothing -> False
                  Just ty -> isDictLikeTy ty


----------------------
findRhsArity :: DynFlags -> Id -> SeqCoreTerm -> Arity -> Arity
-- This implements the fixpoint loop for arity analysis
-- See Note [Arity analysis]
findRhsArity dflags bndr rhs old_arity
  = go (rhsEtaExpandArity dflags init_cheap_app rhs)
       -- We always call termEtaExpandArity once, but usually
       -- that produces a result equal to old_arity, and then
       -- we stop right away (since arities should not decrease)
       -- Result: the common case is that there is just one iteration
  where
    init_cheap_app :: CheapAppMeasure
    init_cheap_app fn n_val_args
      | fn == bndr = True   -- On the first pass, this binder gets infinite arity
      | otherwise  = isCheapApp fn n_val_args

    go :: Arity -> Arity
    go cur_arity
      | cur_arity <= old_arity = cur_arity
      | new_arity == cur_arity = cur_arity
      | otherwise = assert ( new_arity < cur_arity )
#ifdef DEBUG
                    pprTrace "Exciting arity"
                       (vcat [ ppr bndr <+> ppr cur_arity <+> ppr new_arity
                                                    , ppr rhs])
#endif
                    go new_arity
      where
        new_arity = rhsEtaExpandArity dflags cheap_app rhs

        cheap_app :: CheapAppMeasure
        cheap_app fn n_val_args
          | fn == bndr = n_val_args < cur_arity
          | otherwise  = isCheapApp fn n_val_args

-- ^ The Arity returned is the number of value args the
-- expression can be applied to without doing much work
rhsEtaExpandArity :: DynFlags -> CheapAppMeasure -> SeqCoreTerm -> Arity
-- termEtaExpandArity is used when eta expanding
--      e  ==>  \xy -> e x y
rhsEtaExpandArity dflags cheap_app e
  = case arityType env e of
      AArr os at
        | isOneShotInfo os || has_lam e -> 1 + arityTypeArity at
                                   -- Don't expand PAPs/thunks
                                   -- Note [Eta expanding thunks]
      ABot n              -> n
      _                   -> 0
  where
    env = AE { ae_bndrs    = []
             , ae_cheap_fn = mk_cheap_fn dflags cheap_app
             , ae_ped_bot  = gopt Opt_PedanticBottoms dflags }

    has_lam (Lam b e)  = isId b || has_lam e
    has_lam (Compute _ (Eval v fs Return))
                       = all skip fs && has_lam v
    has_lam _          = False
    
    skip (Tick _) = True
    skip _        = False

{-

Note [Arity analysis]
~~~~~~~~~~~~~~~~~~~~~
The motivating example for arity analysis is this:

  f = \x. let g = f (x+1)
          in \y. ...g...

What arity does f have?  Really it should have arity 2, but a naive
look at the RHS won't see that.  You need a fixpoint analysis which
says it has arity "infinity" the first time round.

This example happens a lot; it first showed up in Andy Gill's thesis,
fifteen years ago!  It also shows up in the code for 'rnf' on lists
in Trac #4138.

The analysis is easy to achieve because termEtaExpandArity takes an
argument
     type CheapMeasure = CoreExpr -> Maybe Type -> Bool
used to decide if an expression is cheap enough to push inside a
lambda.  And exprIsCheap' in turn takes an argument
     type CheapAppFun = Id -> Int -> Bool
which tells when an application is cheap. This makes it easy to
write the analysis loop.

The analysis is cheap-and-cheerful because it doesn't deal with
mutual recursion.  But the self-recursive case is the important one.


Note [Eta expanding through dictionaries]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If the experimental -fdicts-cheap flag is on, we eta-expand through
dictionary bindings.  This improves arities. Thereby, it also
means that full laziness is less prone to floating out the
application of a function to its dictionary arguments, which
can thereby lose opportunities for fusion.  Example:
        foo :: Ord a => a -> ...
     foo = /\a \(d:Ord a). let d' = ...d... in \(x:a). ....
        -- So foo has arity 1

     f = \x. foo dInt $ bar x

The (foo DInt) is floated out, and makes ineffective a RULE 
     foo (bar x) = ...

One could go further and make exprIsCheap reply True to any
dictionary-typed expression, but that's more work.

See Note [Dictionary-like types] in TcType.lhs for why we use
isDictLikeTy here rather than isDictTy

Note [Eta expanding thunks]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
We don't eta-expand
   * Trivial RHSs     x = y
   * PAPs             x = map g
   * Thunks           f = case y of p -> \x -> blah

When we see
     f = case y of p -> \x -> blah
should we eta-expand it? Well, if 'x' is a one-shot state token 
then 'yes' because 'f' will only be applied once.  But otherwise
we (conservatively) say no.  My main reason is to avoid expanding
PAPSs
        f = g d  ==>  f = \x. g d x
because that might in turn make g inline (if it has an inline pragma), 
which we might not want.  After all, INLINE pragmas say "inline only
when saturated" so we don't want to be too gung-ho about saturating!

-}
arityLam :: Id -> ArityType -> ArityType
arityLam _  (ABot n)  = ABot (n+1)
arityLam id at        = AArr (idOneShotInfo id) at

floatIn :: CheapFlag -> ArityType -> ArityType
-- We have something like (let x = E in b),
-- where b has the given arity type.
floatIn Cheap at        = at
floatIn NotCheap at     = keepOneShots at
   -- If E is not cheap, keep arity only for one-shots

keepOneShots :: ArityType -> ArityType
keepOneShots (ABot n) = ABot n
keepOneShots (AArr os at) | isOneShotInfo os = AArr os (keepOneShots at)
                          | otherwise        = ATop
keepOneShots AOkSpec                         = AOkSpec
keepOneShots ATop                            = ATop

arityApp :: ArityType -> CheapFlag -> ArityType
-- Processing (fun arg) where at is the ArityType of fun,
-- Knock off an argument and behave like 'let'
arityApp (ABot 0)      _     = ABot 0
arityApp (ABot n)      _     = ABot (n-1)
arityApp ATop          _     = ATop
arityApp AOkSpec       _     = ATop
arityApp (AArr _ at)   cheap = floatIn cheap at

andArityType :: ArityType -> ArityType -> ArityType   -- Used for branches of a 'case'
andArityType AOkSpec    AOkSpec  = AOkSpec
andArityType AOkSpec    at       = at
andArityType at         AOkSpec  = at
andArityType (ABot n1) (ABot n2) = ABot (n1 `min` n2)
andArityType (ABot _)   at       = at
andArityType at         (ABot _) = at
andArityType ATop       at       = keepOneShots at
andArityType at         ATop     = keepOneShots at
-- See Note [Combining case branches]
andArityType (AArr os1 at1) (AArr os2 at2) = AArr (os1 `bestOneShot` os2)
                                                  (andArityType at1 at2)

cutArityType :: ArityType -> CoArityType -> ArityType
cutArityType (ABot 0) _              = ABot 0
cutArityType at       CTop           = at
cutArityType at       (CTrunc n ca)  = cutArityType (truncArityType at n) ca
cutArityType at       (CApp ch ca)   = cutArityType (arityApp at ch) ca
cutArityType (ABot _) (CCase _)      = ATop
cutArityType AOkSpec  (CCase at)     = at
cutArityType _        (CCase at)
  = case at of ABot n | n > 0       -> ATop
                      | otherwise   -> ABot 0
               _                    -> keepOneShots at

truncArityType :: ArityType -> Arity -> ArityType
truncArityType (ABot n)     n' = ABot (n `min` n')
truncArityType (AArr os at) n  | n > 0     = AArr os (truncArityType at (n-1))
                               | otherwise = ATop
truncArityType ATop         _  = ATop
truncArityType AOkSpec      _  = AOkSpec

{-

Note [Combining case branches]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
  go = \x. let z = go e0
               go2 = \x. case x of
                           True  -> z
                           False -> \s(one-shot). e1
           in go2 x
We *really* want to eta-expand go and go2.
When combining the barnches of the case we have
     ATop [] `andAT` ATop [OneShotLam]
and we want to get ATop [OneShotLam].  But if the inner
lambda wasn't one-shot we don't want to do this.
(We need a proper arity analysis to justify that.)

So we combine the best of the two branches, on the (slightly dodgy)
basis that if we know one branch is one-shot, then they all must be.

-}
---------------------------
type CheapMeasure = SeqCoreTerm -> Maybe Type -> Bool
  -- How to decide if an expression is cheap
        -- If the Maybe is Just, the type is the type
        -- of the expression; Nothing means "don't know"

data ArityEnv 
  = AE { ae_bndrs :: [Id]          -- Enclosing value-lambda Ids
                                   -- See Note [Dealing with bottom (3)]
       , ae_cheap_fn :: CheapMeasure
       , ae_ped_bot  :: Bool       -- True <=> be pedantic about bottoms
  }

arityType :: ArityEnv -> SeqCoreTerm -> ArityType
arityType = goT
  where
    goT _ v | termIsBottom v = ABot 0
    
    goT env (Var v)
      | v `elem` ae_bndrs env
      , not (ae_ped_bot env)
      , idArity v == 0
      = AOkSpec
      | strict_sig <- idStrictness v
      , not $ isNopSig strict_sig
      , (ds, res) <- splitStrictSig strict_sig
      , let arity = length ds
      = if isBotRes res then ABot arity
                        else aTop (take arity one_shots)
      | otherwise
      = aTop (take (idArity v) one_shots)
      where
        one_shots :: [OneShotInfo]  -- One-shot-ness derived from the type
        one_shots = typeArity (idType v)

        -- Lambdas; increase arity
    goT env (Lam x e)
      | isId x    = arityLam x (goT env' e)
      | otherwise = goT env e
      where
        env' = env { ae_bndrs = x : ae_bndrs env }
    
    goT env v@(Compute _ c)
      = case goC env c of 
          ATop | termOkForSpeculation v -> AOkSpec
               | otherwise              -> ATop
          other                         -> other
    goT _ _ = ATop
    
    goC env (Eval v fs e) = let at = goT env v
                                ca = goF env fs e
                         in cutArityType at ca
                         
    goC env (Let b e) 
      = floatIn (cheap_bind b) (goC env e)
      where
        cheap_bind (NonRec pair) = cheapFlag $ is_cheap pair
        cheap_bind (Rec prs)     = cheapFlag $ all is_cheap prs
        is_cheap (BindTerm x v)  = ae_cheap_fn env v (Just (idType x))
        is_cheap (BindJoin _ _)  = True -- joins aren't shared anyway
    
    goC _ (Jump {}) = ATop -- TODO

    goF env (App arg : fs) e | Type _ <- arg = goF env fs e
                               | otherwise     = CApp cheap (goF env fs e)
      where cheap = cheapFlag $ ae_cheap_fn env arg Nothing
    
    goF env (Tick ti : fs) e | not (tickishIsCode ti) = goF env fs e
                               | otherwise     = CTop
    goF env (Cast co : fs) e = CTrunc (length (typeArity toTy)) (goF env fs e)
      where toTy = pSnd (coercionKind co)
    goF env []             e = goE env e
    
    goE _   (Case _ [])      = CCase (ABot 0)
    goE env (Case _ alts)    = CCase $ foldr1 andArityType
                                   [ goC env rhs | Alt _ _ rhs <- alts ]
    goE _   Return           = CTop

{-
  
  
%************************************************************************
%*                                                                      *
              The main eta-expander                                                             
%*                                                                      *
%************************************************************************

At this point, GHC's CoreArity.lhs has a note about wanting eta-expanded code
not to have too many redexes and such, because they want to call this from
CorePrep when there isn't going to be a simplifier pass afterward. However, we
don't need to bother, so we can lean on the simplifier and do almost nothing
here.

TODO: If we ever write SequentCorePrep, we'll have to bring back much of the
complexity here.

-}
-- | @etaExpand n us e ty@ returns an expression with
-- the same meaning as @e@, but with arity @n@.
--
-- Given:
--
-- > e' = etaExpand n us e ty
--
-- We should have that:
--
-- > ty = exprType e = exprType e'
etaExpand :: Arity              -- ^ Result should have this number of value args
          -> SeqCoreTerm        -- ^ Expression to expand
          -> SeqCoreTerm
-- etaExpand deals with for-alls. For example:
--              etaExpand 1 E
-- where  E :: forall a. a -> a
-- would return
--      (/\b. \y::a -> E b y)
--
-- It deals with coerces too, though they are now rare
-- so perhaps the extra code isn't worth it

etaExpand n orig_term
  = go n orig_term
  where
      -- Strip off existing lambdas (TODO and casts)
      -- Note [Eta expansion and SCCs]
    go 0 term = term
    go n (Lam v body) | isTyVar v = Lam v (go n     body)
                      | otherwise = Lam v (go (n-1) body)
    -- go n (Cast expr co) = Cast (go n expr) co 
    go n term           = -- pprTrace "ee" (vcat [ppr orig_expr, ppr expr, ppr etas]) $
                          etaInfoAbs etas (etaInfoApp term etas bodyTy)
                        where
                            in_scope = mkInScopeSet (exprFreeVars (termToCoreExpr term))
                            (bodyTy, etas) = mkEtaWW n orig_term in_scope (termType term)

etaExpandRhs :: Arity -> SeqCoreBindPair -> SeqCoreBindPair
etaExpandRhs n (BindTerm bndr term) = BindTerm bndr (etaExpand n term)
etaExpandRhs _ bindJoin             = bindJoin

                                -- Wrapper    Unwrapper
--------------
data EtaInfo = EtaVar Var       -- /\a. [],   [] a
                                -- \x.  [],   [] x
             | EtaCo Coercion   -- [] |> co,  [] |> (sym co)

instance Outputable EtaInfo where
   ppr (EtaVar v) = ptext (sLit "EtaVar") <+> ppr v
   ppr (EtaCo co) = ptext (sLit "EtaCo")  <+> ppr co

--------------
etaInfoAbs :: [EtaInfo] -> SeqCoreTerm -> SeqCoreTerm
etaInfoAbs []               expr = expr
etaInfoAbs (EtaVar v : eis) expr = Lam v (etaInfoAbs eis expr)
etaInfoAbs (EtaCo co : eis) expr = mkCast (etaInfoAbs eis expr) (mkSymCo co)

--------------
etaInfoApp :: SeqCoreTerm -> [EtaInfo] -> Type -> SeqCoreTerm
-- (etaInfoApp s e eis) returns something equivalent to 
--             ((substExpr s e) `appliedto` eis)

etaInfoApp v eis ty
  = mkCompute ty (Eval v (map frame eis) Return)
  where
    frame (EtaVar v) = App (mkVarArg v)
    frame (EtaCo co) = Cast co

--------------
mkEtaWW :: Arity -> SeqCoreTerm -> InScopeSet -> Type
        -> (Type, [EtaInfo])
        -- EtaInfo contains fresh variables,
        --   not free in the incoming CoreExpr
        -- Outgoing InScopeSet includes the EtaInfo vars
        --   and the original free vars

mkEtaWW orig_n orig_expr in_scope orig_ty
  = go orig_n empty_subst orig_ty []
  where
    empty_subst = TvSubst in_scope emptyTvSubstEnv

    go n subst ty eis       -- See Note [termArity invariant]
       | n == 0
       = (ty, reverse eis)

       | Just (tv,ty') <- splitForAllTy_maybe ty
       , let (subst', tv') = Type.substTyVarBndr subst tv
           -- Avoid free vars of the original expression
       = go n subst' ty' (EtaVar tv' : eis)

       | Just (arg_ty, res_ty) <- splitFunTy_maybe ty
       , let (subst', eta_id') = freshEtaId n subst arg_ty 
           -- Avoid free vars of the original expression
       = go (n-1) subst' res_ty (EtaVar eta_id' : eis)
                                   
       | Just (co, ty') <- topNormaliseNewType_maybe ty
       =        -- Given this:
                --      newtype T = MkT ([T] -> Int)
                -- Consider eta-expanding this
                --      eta_expand 1 e T
                -- We want to get
                --      coerce T (\x::[T] -> (coerce ([T]->Int) e) x)
         go n subst ty' (EtaCo co : eis)

       | otherwise       -- We have an expression of arity > 0, 
                         -- but its type isn't a function.                 
       = warnPprTrace True __FILE__ __LINE__ ((ppr orig_n <+> ppr orig_ty) $$ ppr orig_expr)
         (ty, reverse eis)
        -- This *can* legitmately happen:
        -- e.g.  coerce Int (\x. x) Essentially the programmer is
        -- playing fast and loose with types (Happy does this a lot).
        -- So we simply decline to eta-expand.  Otherwise we'd end up
        -- with an explicit lambda having a non-function type

--------------
freshEtaId :: Int -> TvSubst -> Type -> (TvSubst, Id)
-- Make a fresh Id, with specified type (after applying substitution)
-- It should be "fresh" in the sense that it's not in the in-scope set
-- of the TvSubstEnv; and it should itself then be added to the in-scope
-- set of the TvSubstEnv
-- 
-- The Int is just a reasonable starting point for generating a unique;
-- it does not necessarily have to be unique itself.
freshEtaId n subst ty
      = (subst', eta_id')
      where
        ty'     = Type.substTy subst ty
        eta_id' = uniqAway (getTvInScope subst) $
                  mkSysLocal (fsLit "eta") (mkBuiltinUnique n) ty'
        subst'  = extendTvInScope subst eta_id'           

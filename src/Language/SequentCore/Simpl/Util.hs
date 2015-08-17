{-# LANGUAGE CPP #-}

module Language.SequentCore.Simpl.Util (
  -- * State of argument processing
  RevList, ArgInfo(..),
  mkArgInfo, argInfoToTerm, addFrame, swallowCoercion,
  
  -- * Summary of arguments
  ArgSummary(..),
  interestingArg, nonTriv,
  
  -- * Coercion management
  castApp, combineCo, consCastMaybe, simplCoercion,
  
  -- * Miscellany
  matchCase
) where

import Language.SequentCore.Simpl.Env
import Language.SequentCore.Syntax

import Coercion
import CoreSyn     ( CoreRule, isConLikeUnfolding )
import Demand
import FastString
import Id
import Maybes      ( orElse )
import OptCoercion
import Outputable
import Pair
import Rules
import Type hiding ( substTy )
import Util        ( count, lengthExceeds )

import Control.Exception ( assert )

-------------
-- ArgInfo --
-------------

type RevList a = [a]

data ArgInfo
  = ArgInfo {
        ai_term   :: OutTerm,    -- The function (or possibly a literal)
        ai_frames :: RevList OutFrame, -- ...applied to these args/casts (which are in *reverse* order)
        ai_co     :: Maybe InCoercion, -- Last coercion applied; not yet added to ai_frames
        ai_rules  :: [CoreRule], -- Rules for this function
        ai_encl   :: Bool,       -- Flag saying whether this function
                                 -- or an enclosing one has rules (recursively)
                                 --      True => be keener to inline in all args
                                 --      TODO Currently "or an enclosing one" is a lie;
                                 --      need to track interestingness of context in env
        ai_strs   :: [Bool],     -- Strictness of remaining value arguments
                                 --   Usually infinite, but if it is finite it guarantees
                                 --   that the function diverges after being given
                                 --   that number of args
        ai_discs  :: [Int]       -- Discounts for remaining value arguments; non-zero => be keener to inline
                                 --   Always infinite
    }

mkArgInfo :: SimplEnv -> OutTerm -> Maybe InCoercion -> [InFrame] -> ArgInfo
mkArgInfo env term@(Var fun) co_m fs
  | n_val_args < idArity fun            -- Note [Unsaturated functions]
  = ArgInfo { ai_term = term, ai_frames = [], ai_co = co_m
            , ai_rules = rules, ai_encl = False
            , ai_strs = vanilla_stricts
            , ai_discs = vanilla_discounts }
  | otherwise
  = ArgInfo { ai_term = term, ai_frames = [], ai_co = co_m
            , ai_rules = rules
            , ai_encl = False -- TODO Implement this when implementing rules
            , ai_strs  = add_type_str fun_ty arg_stricts
            , ai_discs = arg_discounts }
  where
    fun_ty = idType fun
    n_val_args = count isValueAppFrame fs
    rules = getRules (getSimplRules env) fun

    vanilla_discounts, arg_discounts :: [Int]
    vanilla_discounts = repeat 0
    arg_discounts = case findDef env fun of
                        Just (BoundTo {def_guidance = Sometimes {guArgDiscounts = discounts}})
                              -> discounts ++ vanilla_discounts
                        _     -> vanilla_discounts

    vanilla_stricts, arg_stricts :: [Bool]
    vanilla_stricts  = repeat False

    arg_stricts
      = case splitStrictSig (idStrictness fun) of
          (demands, result_info)
                | not (demands `lengthExceeds` n_val_args)
                ->      -- Enough args, use the strictness given.
                        -- For bottoming functions we used to pretend that the arg
                        -- is lazy, so that we don't treat the arg as an
                        -- interesting context.  This avoids substituting
                        -- top-level bindings for (say) strings into
                        -- calls to error.  But now we are more careful about
                        -- inlining lone variables, so its ok (see SimplUtils.analyseCont)
                   if isBotRes result_info then
                        map isStrictDmd demands         -- Finite => result is bottom
                   else
                        map isStrictDmd demands ++ vanilla_stricts
               | otherwise
               -> warnPprTrace True __FILE__ __LINE__ 
                               (text "More demands than arity" <+> ppr fun <+> ppr (idArity fun)
                                <+> ppr n_val_args <+> ppr demands )
                   vanilla_stricts      -- Not enough args, or no strictness

    add_type_str :: Type -> [Bool] -> [Bool]
    -- If the function arg types are strict, record that in the 'strictness bits'
    -- No need to instantiate because unboxed types (which dominate the strict
    -- types) can't instantiate type variables.
    -- add_type_str is done repeatedly (for each call); might be better
    -- once-for-all in the function
    -- But beware primops/datacons with no strictness
    add_type_str _ [] = []
    add_type_str fun_ty strs            -- Look through foralls
        | Just (_, fun_ty') <- splitForAllTy_maybe fun_ty       -- Includes coercions
        = add_type_str fun_ty' strs
    add_type_str fun_ty (str:strs)      -- Add strict-type info
        | Just (arg_ty, fun_ty') <- splitFunTy_maybe fun_ty
        = (str || isStrictType arg_ty) : add_type_str fun_ty' strs
    add_type_str _ strs
        = strs
mkArgInfo _env term co_m _fs
  -- Build "arg info" for something that's not a function.
  -- Any App frame is a type error anyway, so many of these fields don't matter.
  = ArgInfo { ai_term = term, ai_frames = [], ai_co = co_m
            , ai_rules = [], ai_encl = False
            , ai_strs = repeat False -- Could be [], but applying to a non-function
                                     -- isn't bottom, it's ill-defined!
            , ai_discs = repeat 0 }

argInfoToTerm :: SimplEnv -> ArgInfo -> OutTerm
argInfoToTerm env ai = mkComputeEval (ai_term ai') (reverse (ai_frames ai'))
  where ai' = swallowCoercion env ai

-- Add a frame to the ArgInfo. Don't try anything clever like pushing casts
-- past arguments (simplKont will do this itself), but do simplify the coercion
-- before adding it to the frames.
addFrame :: SimplEnv -> ArgInfo -> OutFrame -> ArgInfo
addFrame env ai f
  = case f of
      Cast co -> ai { ai_co = ai_co ai `combineCo` co }
      App _   -> ai' { ai_frames = f : ai_frames ai' }
        where ai' = swallowCoercion env ai
      Tick _  -> ai { ai_frames = f : ai_frames ai }

-- Clear the coercion, if there is one, by adding it to the frames after
-- simplifying it.
swallowCoercion :: SimplEnv -> ArgInfo -> ArgInfo
swallowCoercion env ai@(ArgInfo { ai_co = Just co, ai_frames = fs })
  = ai { ai_co     = Nothing
       , ai_frames = Cast (simplCoercion env co) : fs }
swallowCoercion _ ai = ai

----------------
-- ArgSummary --
----------------

data ArgSummary = TrivArg        -- Nothing interesting
                | NonTrivArg        -- Arg has structure
                | ValueArg        -- Arg is a con-app or PAP
                            -- ..or con-like. Note [Conlike is interesting]

interestingArg :: SeqCoreTerm -> ArgSummary
-- See Note [Interesting arguments]
interestingArg e = goT e 0
  where
    -- n is # value args to which the expression is applied
    goT (Lit {}) _              = ValueArg
    goT (Var v)  n
       | isConLikeId v     = ValueArg        -- Experimenting with 'conlike' rather that
                                             --    data constructors here
       | idArity v > n           = ValueArg  -- Catches (eg) primops with arity but no unfolding
       | n > 0                   = NonTrivArg        -- Saturated or unknown call
       | conlike_unfolding = ValueArg        -- n==0; look for an interesting unfolding
                                      -- See Note [Conlike is interesting]
       | otherwise         = TrivArg        -- n==0, no useful unfolding
       where
         conlike_unfolding = isConLikeUnfolding (idUnfolding v)

    goT (Type _)         _ = TrivArg
    goT (Coercion _)     _ = TrivArg
    goT (Lam v e)           n 
       | isTyVar v     = goT e n
       | n>0           = goT e (n-1)
       | otherwise     = ValueArg
    goT (Compute _ c) n    = goC c n
    
    goC (Let _ c)    n = case goC c n of { ValueArg -> ValueArg; _ -> NonTrivArg }
    goC (Eval v k)   n = maybe NonTrivArg (goT v) (goK k n)
    goC (Jump vs j)  _ = goT (Var j) (length (filter isValueArg vs))
    
    goK (Kont _ (Case {}))   _ = Nothing
    goK (Kont fs Return)     n = Just $ length (filter realArg fs) + n
    
    realArg (App (Type _))     = False
    realArg (App (Coercion _)) = False
    realArg (App _)            = True
    realArg _                  = False

nonTriv ::  ArgSummary -> Bool
nonTriv TrivArg = False
nonTriv _       = True


instance Outputable ArgSummary where
  ppr TrivArg    = ptext (sLit "TrivArg")
  ppr NonTrivArg = ptext (sLit "NonTrivArg")
  ppr ValueArg   = ptext (sLit "ValueArg")

-----------------------
-- Coercion handling --
-----------------------

simplCoercion :: SimplEnv -> Coercion -> Coercion
simplCoercion env co = optCoercion (getCvSubst env) co

combineCo :: Maybe InCoercion -> InCoercion -> Maybe InCoercion
combineCo co_m co'
  -- Skip reflexive coercion
  | fromTy2 `eqType` toTy2
  = co_m
  | otherwise
  = case co_m of
      Nothing -> Just co'
      Just co | let Pair fromTy1 toTy1 = coercionKind co
              , fromTy2 `eqType` toTy1
              , fromTy1 `eqType` toTy2
              -- Skip back-and-forth
              -> Nothing
              | otherwise
              -> Just (mkTransCo co co')
  where Pair fromTy2 toTy2 = coercionKind co'

castApp :: InArg -> Maybe InCoercion -> (InArg, Maybe InCoercion)
castApp arg              Nothing   = (arg, Nothing)
castApp arg@(Type argTy) (Just co) = (arg, Just (mkInstCo co argTy))
castApp arg              (Just co) = (mkCast arg (mkSymCo argCo), Just bodyCo)
  where [argCo, bodyCo]            = decomposeCo 2 co

consCastMaybe :: Maybe InCoercion -> [InFrame] -> [InFrame]
Nothing `consCastMaybe` fs = fs
Just co `consCastMaybe` fs = Cast co : fs

----------------
-- Miscellany --
----------------

matchCase :: SimplEnv -> InValue -> [InAlt] -> Maybe InAlt
matchCase _env_v (LitVal lit) (alt@(Alt (LitAlt lit') xs _) : _alts)
  | assert (null xs) True
  , lit == lit'
  = Just alt
matchCase _env_v (ConsVal ctor _tyArgs valArgs) (alt@(Alt (DataAlt ctor') xs _) : _alts)
  | ctor == ctor'
  , assert (length valArgs == length xs) True
  = Just alt
matchCase env_v value (alt@(Alt DEFAULT xs _) : alts)
  | assert (null xs) True
  = Just $ matchCase env_v value alts `orElse` alt
matchCase env_v value (_ : alts)
  = matchCase env_v value alts
matchCase _ _ []
  = Nothing

instance Outputable ArgInfo where
  ppr (ArgInfo { ai_term = term
               , ai_frames = fs
               , ai_co = co_m
               , ai_strs = strs })
    = hang (text "ArgInfo") 8 $ vcat [ text "Term:" <+> ppr term
                                     , text "Prev. Frames:" <+> pprWithCommas ppr fs
                                     , case co_m of Just co -> text "Coercion:" <+> ppr co
                                                    Nothing -> empty
                                     , strictDoc ]
    where
      strictDoc = case strs of []        -> text "Expression is bottom"
                               True  : _ -> text "Next argument strict"
                               False : _ -> text "Next argument lazy"

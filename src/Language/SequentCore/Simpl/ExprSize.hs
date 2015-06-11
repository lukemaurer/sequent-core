module Language.SequentCore.Simpl.ExprSize (
  ExprSize(..), valueSize, contSize, commandSize
) where

import Language.SequentCore.Syntax

import Bag
import DataCon
import DynFlags
import Id
import IdInfo
import Literal
import Outputable
import PrelNames ( buildIdKey, augmentIdKey )
import PrimOp
import Type
import TysPrim   ( realWorldStatePrimTy )
import Unique
import Util      ( count )

import qualified Data.ByteString as BS

-- Size of an expression, with argument and result discounts
data ExprSize
  = ExprSize { esBase :: !Int
             , esArgDiscs :: ![Int]
             , esResultDisc :: !Int
             }

-- Size of an expression as represented internally during computation
data BodySize
  = TooBig
  | BodySize { bsBase :: !Int
             , bsArgDiscs :: Bag (Id, Int)
             , bsResultDisc :: !Int
             }

instance Outputable BodySize where
  ppr TooBig = text "TooBig"
  ppr (BodySize b _ r) = brackets (int b <+> int r)

instance Outputable ExprSize where
  ppr (ExprSize b as r) = brackets (int b <+> brackets (hsep $ map int as) <+> int r)

body2ExprSize :: [Id] -> BodySize -> Maybe ExprSize
body2ExprSize _       TooBig = Nothing
body2ExprSize topArgs (BodySize b as r)
  = Just (ExprSize b (map (discount as) topArgs) r)
  where
    discount :: Bag (Id, Int) -> Id -> Int
    discount cbs bndr = foldlBag combine 0 cbs
       where
         combine acc (bndr', disc) 
           | bndr == bndr' = acc `plus_disc` disc
           | otherwise     = acc

         plus_disc :: Int -> Int -> Int
         plus_disc | isFunTy (idType bndr) = max
                   | otherwise             = (+)

sizeZero :: BodySize
sizeZero = BodySize { bsBase = 0, bsArgDiscs = emptyBag, bsResultDisc = 0 }

sizeN :: Int -> BodySize
sizeN n = BodySize { bsBase = n, bsArgDiscs = emptyBag, bsResultDisc = 0 }

maxSize :: BodySize -> BodySize -> BodySize
TooBig               `maxSize` _                    = TooBig
_                    `maxSize` TooBig               = TooBig
s1@(BodySize b1 _ _) `maxSize` s2@(BodySize b2 _ _) = if b1 > b2 then s1 else s2

mkBodySize :: Int -> Int -> Bag (Id, Int) -> Int -> BodySize
mkBodySize cap b as r
  | cap < b - r = TooBig
  | otherwise   = BodySize { bsBase = b, bsArgDiscs = as, bsResultDisc = r }

valueSize   :: DynFlags -> Int -> SeqCoreValue   -> Maybe ExprSize
contSize    :: DynFlags -> Int -> SeqCoreCont    -> Maybe ExprSize
commandSize :: DynFlags -> Int -> SeqCoreCommand -> Maybe ExprSize

-- We have three mutually recursive functions, but only one argument changes
-- between recursive calls; easiest to use one recursive function that takes
-- a sum

bodySize :: DynFlags -> Int -> [Id] -> SeqCoreExpr -> BodySize

valueSize dflags cap (Lam xs _k body)
  = let valBinders = filter isId xs
    in body2ExprSize valBinders $ bodySize dflags cap valBinders (C body)
valueSize dflags cap val
  = body2ExprSize [] $ bodySize dflags cap [] (V val)

commandSize dflags cap comm
  = body2ExprSize [] $ bodySize dflags cap [] (C comm)

contSize dflags cap cont = body2ExprSize [] $ bodySize dflags cap [] (K cont)

bodySize dflags cap topArgs expr
  = cap `seq` size expr -- use seq to unbox cap now; we will use it often
  where
    size (V (Type _))       = sizeZero
    size (V (Coercion _))   = sizeZero
    size (V (Var _))        = sizeZero -- invariant: not a nullary constructor
    size (V (Compute _ comm)) = size (C comm)
    size (V (Cont cont))    = size (K cont)
    size (V (Lit lit))      = sizeN (litSize lit)
    size (V (Cons dc args)) = sizeArgs args `addSizeNSD`
                              sizeCall (dataConWorkId dc) args voids
      where voids           = count isRealWorldValue args
    size (V (Lam xs _ comm))| erased    = size (C comm)
                            | otherwise = lamScrutDiscount dflags (size (C comm))
      where erased          = all (\x -> not (isId x) || isRealWorldId x) xs
    
    size (K (Return _))     = sizeZero
    size (K (Cast _ cont))  = size (K cont)
    size (K (Tick _ cont))  = size (K cont)
    size (K (App arg cont)) = sizeArg arg `addSizeNSD` size (K cont)
    size (K (Case _ alts))  = sizeAlts alts

    size (C comm)           = sizeLets (cmdLet comm) `addSizeNSD`
                              sizeCut (cmdValue comm) (cmdCont comm)
    
    sizeCut :: SeqCoreValue -> SeqCoreCont -> BodySize
    -- Compare this clause to size_up_app in CoreUnfold; already having the
    -- function and arguments at hand avoids some acrobatics
    sizeCut (Var f) cont@(App {})
      = let (args, cont') = collectArgs cont
            realArgs      = filter (not . isErasedValue) args
            voids         = count isRealWorldValue realArgs
        in sizeArgs realArgs `addSizeNSD` sizeCall f realArgs voids
                             `addSizeOfCont` cont'
    sizeCut (Var x) (Case _b alts)
      | x `elem` topArgs
      = combineSizes total max
      where
        altSizes = map sizeAlt alts
        total    = foldr addAltSize sizeZero altSizes
        max      = foldr maxSize    sizeZero altSizes
        
        combineSizes (BodySize totBase totArgDiscs totResDisc)
                     (BodySize maxBase _           _)
          = BodySize totBase
                     (unitBag (x, 20 + totBase - maxBase)
                       `unionBags` totArgDiscs)
                     totResDisc
        combineSizes tot _ = tot -- must be TooBig

    sizeCut val cont
      = size (V val) `addSizeOfCont` cont

    sizeArg :: SeqCoreValue -> BodySize
    sizeArg arg = size (V arg)

    sizeArgs :: [SeqCoreValue] -> BodySize
    sizeArgs args = foldr (addSizeNSD . sizeArg) sizeZero args

    -- Lifted from CoreUnfold
    sizeCall :: Id -> [SeqCoreValue] -> Int -> BodySize
    sizeCall fun valArgs voids
       = case idDetails fun of
           FCallId _        -> sizeN (10 * (1 + length valArgs))
           DataConWorkId dc -> conSize dc (length valArgs)
           PrimOpId op      -> primOpSize op (length valArgs)
           ClassOpId _      -> classOpSize dflags topArgs valArgs
           _                -> funSize dflags topArgs fun (length valArgs) voids

    sizeAlt :: SeqCoreAlt -> BodySize
    sizeAlt (Alt _ _ rhs) = size (C rhs) `addSizeN` 10

    sizeAlts :: [SeqCoreAlt] -> BodySize
    sizeAlts alts = foldr (addAltSize . sizeAlt) sizeZero alts

    sizeBind :: SeqCoreBind -> BodySize
    sizeBind (NonRec x rhs)
      = size (V rhs) `addSizeN` allocSize
      where
        allocSize
          -- An unlifted type has no heap allocation
          | isUnLiftedType (idType x) =  0
          | otherwise                 = 10

    sizeBind (Rec pairs)
      = foldr (addSizeNSD . pairSize) (sizeN allocSize) pairs
      where
        allocSize                     = 10 * length pairs
        pairSize (_x, rhs)            = size (V rhs)

    sizeLets :: [SeqCoreBind] -> BodySize
    sizeLets binds = foldr (addSizeNSD . sizeBind) sizeZero binds

    addSizeN :: BodySize -> Int -> BodySize
    addSizeN TooBig            _ = TooBig
    addSizeN (BodySize b as r) d = mkBodySize cap (b + d) as r

    -- How to combine the sizes of alternatives
    addAltSize :: BodySize -> BodySize -> BodySize
    addAltSize (BodySize b1 as1 r1) (BodySize b2 as2 r2)
      = mkBodySize cap (b1 + b2) (as1 `unionBags` as2) (r1 + r2)
    addAltSize _ _ = TooBig

    -- ignores the result discount on the LEFT argument
    addSizeNSD :: BodySize -> BodySize -> BodySize
    addSizeNSD TooBig _      = TooBig
    addSizeNSD _      TooBig = TooBig
    addSizeNSD (BodySize b1 as1 _) (BodySize b2 as2 r2)
      = mkBodySize cap (b1 + b2) (as1 `unionBags` as2) r2

    -- If a continuation passes the value through unchanged, then it should not
    -- count against the result discount (and has size zero anyway).
    addSizeOfCont :: BodySize -> SeqCoreCont -> BodySize
    addSizeOfCont size1 cont
      | isPassThroughCont cont = size1
      | otherwise              = size1 `addSizeNSD` size (K cont)

    isPassThroughCont :: Cont b -> Bool
    isPassThroughCont (Return _)     = True
    isPassThroughCont (Tick _ cont)  = isPassThroughCont cont
    isPassThroughCont (Cast _ cont)  = isPassThroughCont cont
    isPassThroughCont (App arg cont) = isErasedValue arg
                                         && isPassThroughCont cont
    isPassThroughCont _              = False

    infixl 6 `addSizeN`, `addSizeNSD`, `addSizeOfCont`

-- Lifted from CoreUnfold
litSize :: Literal -> Int
litSize (LitInteger {}) = 100 -- Note [Size of literal integers]
litSize (MachStr str)   = 10 + 10 * ((BS.length str + 3) `div` 4)
  -- If size could be 0 then @f "x"@ might be too small
  -- [Sept03: make literal strings a bit bigger to avoid fruitless 
  --  duplication of little strings]
litSize _other = 0    -- Must match size of nullary constructors
                      -- Key point: if  x |-> 4, then x must inline unconditionally
                      --     	    (eg via case binding)

-- Lifted from CoreUnfold
classOpSize :: DynFlags -> [Id] -> [SeqCoreValue] -> BodySize
-- See Note [Conlike is interesting]
classOpSize _ _ []
  = sizeZero
classOpSize dflags top_args (arg1 : other_args)
  = BodySize size arg_discount 0
  where
    size = 20 + (10 * length other_args)
    -- If the class op is scrutinising a lambda bound dictionary then
    -- give it a discount, to encourage the inlining of this function
    -- The actual discount is rather arbitrarily chosen
    arg_discount = case arg1 of
                     Var dict | dict `elem` top_args 
                              -> unitBag (dict, ufDictDiscount dflags)
                     _other   -> emptyBag

-- Lifted from CoreUnfold
funSize :: DynFlags -> [Id] -> Id -> Int -> Int -> BodySize
-- Size for functions that are not constructors or primops
-- Note [Function applications]
funSize dflags top_args fun n_val_args voids
  | fun `hasKey` buildIdKey   = buildSize
  | fun `hasKey` augmentIdKey = augmentSize
  | otherwise = BodySize size arg_discount res_discount
  where
    some_val_args = n_val_args > 0

    size | some_val_args = 10 * (1 + n_val_args - voids)
         | otherwise     = 0
        -- The 1+ is for the function itself
        -- Add 1 for each non-trivial arg;
        -- the allocation cost, as in let(rec)
  
        --                  DISCOUNTS
        --  See Note [Function and non-function discounts]
    arg_discount | some_val_args && fun `elem` top_args
                 = unitBag (fun, ufFunAppDiscount dflags)
                 | otherwise = emptyBag
        -- If the function is an argument and is applied
        -- to some values, give it an arg-discount

    res_discount | idArity fun > n_val_args = ufFunAppDiscount dflags
                 | otherwise                = 0
        -- If the function is partially applied, show a result discount

-- Lifted from CoreUnfold
primOpSize :: PrimOp -> Int -> BodySize
primOpSize op n_val_args
 = if primOpOutOfLine op
      then sizeN (op_size + n_val_args)
      else sizeN op_size
 where
   op_size = primOpCodeSize op

-- Lifted from CoreUnfold
buildSize :: BodySize
buildSize = BodySize 0 emptyBag 40
  -- We really want to inline applications of build
  -- build t (\cn -> e) should cost only the cost of e (because build will be inlined later)
  -- Indeed, we should add a result_discount becuause build is 
  -- very like a constructor.  We don't bother to check that the
  -- build is saturated (it usually is).  The "-2" discounts for the \c n, 
  -- The "4" is rather arbitrary.

-- Lifted from CoreUnfold
augmentSize :: BodySize
augmentSize = BodySize 0 emptyBag 40
  -- Ditto (augment t (\cn -> e) ys) should cost only the cost of
  -- e plus ys. The -2 accounts for the \cn 

-- Lifted from CoreUnfold
conSize :: DataCon -> Int -> BodySize
conSize dc n_val_args
  | n_val_args == 0      = BodySize  0 emptyBag 10    -- Like variables

-- See Note [Unboxed tuple size and result discount]
  | isUnboxedTupleCon dc = BodySize  0 emptyBag (10 * (1 + n_val_args))

-- See Note [Constructor size and result discount]
  | otherwise            = BodySize 10 emptyBag (10 * (1 + n_val_args))

lamScrutDiscount :: DynFlags -> BodySize -> BodySize
lamScrutDiscount _      TooBig = TooBig
lamScrutDiscount dflags (BodySize b as _)
  = BodySize b as (ufFunAppDiscount dflags)

isRealWorldId :: Id -> Bool
isRealWorldId id = idType id `eqType` realWorldStatePrimTy

isRealWorldValue :: Value b -> Bool
-- an expression of type State# RealWorld must be a variable
isRealWorldValue (Var id) = isRealWorldId id
isRealWorldValue _        = False


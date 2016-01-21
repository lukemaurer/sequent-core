{-# LANGUAGE MagicHash, GADTs, RankNTypes #-}

module Main where

import GHC.Exts

-- Obvious case for contification.
case1_yes :: () -> Int#
case1_yes ()
  = let {-# NOINLINE k #-}
        k x = 1# +# x
    in k 3#

-- Can't contify because k is called in non-tail position.
case2_no :: () -> Int#
case2_no ()
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in if k 3# then 1# else 2#

-- Won't contify because _k isn't used at all.
case2b_gone :: () -> Int#
case2b_gone ()
  = let {-# NOINLINE _k #-}
        _k f = f 1#
    in 3#

-- Can't contify because one call is not in tail position
-- (even though the other is).
case3_no :: Bool
case3_no
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in k (if k 3# then 1# else 2#)

{-# NOINLINE flag #-}
flag :: Bool
flag = False

-- Can contify g but not k
case4_mixed :: Bool
case4_mixed
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
        {-# NOINLINE g #-}
        g y = k (y 5#)
    in if flag && k 3# then True else g (+# 1#)
    
-- Can contify both; decision to contify g propagates upward
case4b_yes :: Bool
case4b_yes
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
        {-# NOINLINE g #-}
        g y = k (y 5#)
    in if flag then k 3# else g (+# 1#)

-- Can contify; tail-called from one branch and not used in the other
case5_yes :: Bool
case5_yes
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in if flag then True else k 1#

-- An existential type to make things interesting
data Stringy where Stringy :: a -> (a -> String) -> Stringy

{-# NOINLINE stringy #-}
stringy :: Stringy
stringy = Stringy (3 :: Int) show

-- Produces a polymorphic continuation
case6_yes :: String
case6_yes
  = let {-# NOINLINE k #-}
        k x = case x of { [] -> "Empty!"; s -> s }
        {-# NOINLINE g #-}
        g y f = k (f y)
    in case stringy of Stringy y f -> g y f

-- Produces a rather oddly typed polymorphic continuation
case7_yes :: String
case7_yes
  = let {-# NOINLINE k #-}
        k :: forall a. a -> forall b. b -> (a -> String) -> (b -> String) -> String
        k x y f g = f x ++ g y
    in case (stringy, stringy) of (Stringy x f, Stringy y g) -> k x y f g

-- Produces a continuation that is NOT polymorphic because it would be ill-typed
case8a_yes :: [Int]
case8a_yes
  = let {-# NOINLINE k #-}
        k :: forall a. [a]
        k = []
    in k

-- Same; also, the Void# should be gone
case8b_yes :: [Int]
case8b_yes
  = let {-# NOINLINE k #-}
        k :: forall a. Void# -> [a]
        k _ = []
    in k void#

-- A tricky case of eta-expansion
case8c_yes :: Int
case8c_yes
  = let {-# NOINLINE k #-}
        k :: forall a. a -> a
        k x = x
    in k id 1

case9_yes :: Bool -> Int# -> Int# -> Int#
case9_yes b z
  = let {-# NOINLINE j #-}
        j x y = if x then z +# y else z -# y
    in case b of
      False -> j True
      True  -> j False

-- Can't contify only one among mutually recursive functions
case10_no :: Int# -> Int#
case10_no x =
  let {-# NOINLINE k #-}
      k y = if tagToEnum# (y <# 0#) then 0# else y +# f (y -# 1#)
      {-# NOINLINE f #-}
      f y = k (y -# 1#)
  in f x

-- We would like to handle this case, but it seems to require abstract
-- interpretation: We need to fix the type argument to h but it's only ever
-- called with an inner-bound tyvar as the type.
case11_yes_someday :: [Bool] -> [Bool]
case11_yes_someday bs
  = let k, h :: [a] -> [a] -> [a]
        {-# NOINLINE k #-}
        k xs acc = case xs of []      -> acc
                              _ : xs' -> h xs' acc
        {-# NOINLINE h #-}
        h xs acc = case xs of []      -> acc
                              x : xs' -> k xs' (x : x : acc)
    in k bs []

-- If a contified function is unsaturated, its free variables *do* escape
case12_mixed :: Int# -> Int#
case12_mixed
  = let f :: Int# -> Int# -> Int#
        {-# NOINLINE f #-}
        f x y = x +# y
        
        k, h :: Int# -> Int#
        {-# NOINLINE k #-}
        k = f 5#
        
        {-# NOINLINE h #-}
        h = \x -> k (x +# 1#) -- Not a tail call! Outer context wants Int# -> Int#
    in h

case13_yes :: Int -> Int
case13_yes x
  = let k, h :: Int -> Int
        {-# NOINLINE k #-}
        k y = if y == 0 then 1 else h (y-1)
        
        {-# NOINLINE h #-}
        h y = if y == 0 then 0 else k (y-1)
    in k x

main :: IO ()
main = return ()

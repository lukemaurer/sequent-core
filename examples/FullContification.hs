{-# LANGUAGE MagicHash, GADTs, RankNTypes #-}

module Main where

import GHC.Exts
{-
-- Obvious case for contification.
case1_yes :: () -> Int#
case1_yes ()
  = let {-# NOINLINE k #-}
        k x = 1# +# x
    in k 3#

-- Can contify by floating in toward the one call site.
case2_yes :: () -> Int#
case2_yes ()
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in if k 3# then 1# else 2#

-- Can't contify because one calls are in different continuations' scopes.
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

-- Can contify; tail-called from one branch and not used in the other
case5_yes :: Bool
case5_yes
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in if flag then True else k 1#

-- Can't contify only one among mutually recursive functions; also, can't float
-- into recursive RHS
case6_no :: Int# -> Int#
case6_no x =
  let {-# NOINLINE k #-}
      k y = if tagToEnum# (y <# 0#) then 0# else y +# f (y -# 1#)
      {-# NOINLINE f #-}
      f y = k (y -# 1#)
  in f x

-- We would like to handle this case, but seems to require abstract
-- interpretation: We need to fix the type argument to h but it's only ever
-- called with an inner-bound tyvar as the type.
case7_yes_someday :: [Bool] -> [Bool]
case7_yes_someday bs
  = let k, h :: [a] -> [a] -> [a]
        {-# NOINLINE k #-}
        k xs acc = case xs of []      -> acc
                              _ : xs' -> h xs' acc
        {-# NOINLINE h #-}
        h xs acc = case xs of []      -> acc
                              x : xs' -> k xs' (x : x : acc)
    in k bs []

-- If a contified function is unsaturated, its free variables *do* escape
case8_mixed :: Int# -> Int#
case8_mixed
  = let f :: Int# -> Int# -> Int#
        {-# NOINLINE f #-}
        f x y = x +# y
        
        k, h :: Int# -> Int#
        {-# NOINLINE k #-}
        k = f 5#
        
        {-# NOINLINE h #-}
        h = \x -> k (x +# 1#) -- Not a tail call! Outer context wants Int# -> Int#
    in h

case9_yes :: Int -> Int
case9_yes x
  = let k, h :: Int -> Int
        {-# NOINLINE k #-}
        k y = if y == 0 then 1 else h (y-1)
        
        {-# NOINLINE h #-}
        h y = if y == 0 then 0 else k (y-1)
    in k x
-}

-- Can float recursive groups inward
case10_yes :: Int -> Int
case10_yes x
  = let k, h :: Int -> Bool
        {-# NOINLINE k #-}
        k y = if y == 0 then True else h (y-1)
        
        {-# NOINLINE h #-}
        h y = if y == 0 then False else k (y-1)
    in if k x then 1 else 0

{-
-- Don't wreck sharing by floating a thunk inward
case11_no :: Int -> Int
case11_no x
  = let {-# NOINLINE y #-}
        y = x + 1
  
        {-# NOINLINE f #-}
        f 0 = 1
        f z = f (z-1) * y -- Could float into argument and contify (but shouldn't!)
    in f x
-}
main :: IO ()
main = return ()

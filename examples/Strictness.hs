{-# OPTIONS_GHC -fno-full-laziness #-} -- Keep lazy things unfloated

module Main where

{-# NOINLINE plusL #-}
{-# NOINLINE plusS #-}
plusL, plusS :: Bool -> Int -> Int -> Int
plusL b x y = if b then x + y else 0
plusS _ x y = x + y

lazyCall, strictCall, strictDupCall, lazyBotCall, strictBotCall ::
  Bool -> Int -> Int -> Int -> Int -> Int

-- Neither case nor let should float
lazyCall   b x y z w = plusL b (case divMod z w of (q, r) -> q + r)
                               (let {-# NOINLINE a #-}
                                    a = x + y in a * a)

-- Case should come to top; let should float
strictCall b x y z w = plusS b (case divMod z w of (q, r) -> q + r)
                               (let {-# NOINLINE a #-}
                                    a = x + y in a * a)

-- Case should came to top; let should float and a*a should get let-bound
strictDupCall b x y z w = plusS b (case divMod z w of (q, 0) -> 2 * q
                                                      (q, r) -> q + r)
                                  (let {-# NOINLINE a #-}
                                       a = x + y in a * a)

-- Should be the same as lazyCall
lazyBotCall   b x y z w = plusL b (error "oops" z w)
                                  (let {-# NOINLINE a #-}
                                       a = x + y in a * a)

-- Body should disappear, replaced by case error "oops" of {}
strictBotCall b x y z w = plusS b (error "oops" z w)
                                  (let {-# NOINLINE a #-}
                                       a = x + y in a * a)
                                       
main :: IO ()
main = return ()

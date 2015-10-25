{-# LANGUAGE KindSignatures #-}

module Language.SequentCore.Syntax where

data Term     (b :: *)
data Frame    (b :: *)
data End      (b :: *)
data Command  (b :: *)
data Bind     (b :: *)
data BindPair (b :: *)
data Join     (b :: *)
data Alt      (b :: *)

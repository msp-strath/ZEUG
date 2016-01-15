{-# LANGUAGE KindSignatures, DataKinds, EmptyCase, GADTs,
             DeriveFunctor #-}
module Utils where

data Nat = Zero | Suc Nat

type One = Suc Zero

data Fin (n :: Nat) where
  FZero :: Fin (Suc n)
  FSuc  :: Fin n -> Fin (Suc n)

absurd :: Fin Zero -> a
absurd k = case k of {}

-- utilities
data Bwd x = B0 | Bwd x :< x deriving Functor

bmap :: (a -> b) -> Bwd a -> Bwd b
bmap f B0 = B0
bmap f (xs :< x) = bmap f xs :< f x

(+<+) :: Bwd x -> Bwd x -> Bwd x
xs +<+ B0 = xs
xs +<+ (ys :< y) = (xs +<+ ys) :< y

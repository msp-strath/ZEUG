{-# LANGUAGE KindSignatures, DataKinds, EmptyCase, GADTs,
             DeriveFunctor, StandaloneDeriving  #-}
module Utils where

data Nat = Zero | Suc Nat deriving Show

type One = Suc Zero

data Fin (n :: Nat) where
  FZero :: Fin (Suc n)
  FSuc  :: Fin n -> Fin (Suc n)

deriving instance Eq (Fin n)
deriving instance Show (Fin n)

absurd :: Fin Zero -> a
absurd k = case k of {}

data Vec x (n :: Nat) where
  VNil  :: Vec x Zero
  VCons :: x -> Vec x n -> Vec x (Suc n)

vlookup :: Fin n -> Vec x n -> x
vlookup FZero    (VCons x _ ) = x
vlookup (FSuc i) (VCons _ xs) = vlookup i xs

velemIndex :: Eq x => x -> Vec x n -> Maybe (Fin n)
velemIndex x VNil          = Nothing
velemIndex x (VCons x' xs) =
  if x == x' then
    Just FZero              
  else
    fmap FSuc (velemIndex x xs)

velemIndex' :: Eq x => x -> Nat ->  Vec x n -> Maybe (Fin n)
velemIndex' x n VNil          = Nothing
velemIndex' x n (VCons x' xs) =
  if x == x' then
    case n of
      Zero  -> Just FZero
      Suc n -> fmap FSuc (velemIndex' x n xs)
  else
    fmap FSuc (velemIndex' x n xs)

-- utilities
data Bwd x = B0 | Bwd x :< x deriving Functor

bmap :: (a -> b) -> Bwd a -> Bwd b
bmap f B0 = B0
bmap f (xs :< x) = bmap f xs :< f x

(+<+) :: Bwd x -> Bwd x -> Bwd x
xs +<+ B0 = xs
xs +<+ (ys :< y) = (xs +<+ ys) :< y

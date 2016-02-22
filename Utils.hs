{-# LANGUAGE KindSignatures, DataKinds, EmptyCase, GADTs,
             DeriveFunctor, StandaloneDeriving, PolyKinds,
             TypeOperators, ScopedTypeVariables, RankNTypes #-}
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

-- find the first x in the vector and return its index
velemIndex :: Eq x => x -> Vec x n -> Maybe (Fin n)
velemIndex x VNil          = Nothing
velemIndex x (VCons x' xs) =
  if x == x' then
    Just FZero              
  else
    fmap FSuc (velemIndex x xs)

-- find the nth x in the vector and return its index
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

(<><) :: Bwd x -> [x] -> Bwd x
xs <>< (y : ys) = (xs :< y) <>< ys
xs <>< []       = xs

(<>>) :: Bwd x -> [x] -> [x]
B0        <>> ys = ys
(xs :< x) <>> ys = xs <>> (x : ys)

-- indexed unit type
data Happy :: k -> * where
  Happy :: Happy k

data (:*) (s :: k -> *) (t :: k -> *) (i :: k) = s i :&: t i

-- reflexive transitive closures

data LStar r a b where
  L0    :: LStar r a a
  (:<:) :: LStar r a b -> r b c -> LStar r a c

lextend :: (forall a b . r a b -> LStar s a b) -> LStar r a b  -> LStar s a b
lextend f L0 = L0
lextend f (xs :<: x) = lextend f xs >>> f x

lmap :: (forall a b . r a b -> s a b) -> LStar r a b  -> LStar s a b
lmap f xs = lextend (\ x -> L0 :<: f x) xs

data RStar r a b where
  R0    :: RStar r a a
  (:>:) :: r a b -> RStar r b c -> RStar r a c

class Category (hom :: obj -> obj -> *) where
  idCat :: hom x x
  (<<<) :: hom y z -> hom x y -> hom x z
  f <<< g = g >>> f
  (>>>) :: hom x y -> hom y z -> hom x z
  f >>> g = g <<< f

instance Category (->) where
  idCat = id
  (<<<) = (.)

instance Category (LStar r) where
  idCat = L0
  xs >>> L0 = xs
  xs >>> (ys :<: y) = (xs >>> ys) :<: y

instance Category (RStar r) where
  idCat = R0
  R0 >>> ys = ys
  (x :>: xs) >>> ys = x :>: (xs >>> ys)

-- existential

data Ex (f :: k -> *) where
  Wit :: f i -> Ex f

data Ex2 (f :: k -> l -> *)(j :: l) where
  Wit2 :: f i j  -> Ex2 f j

type Dot f g = Ex (f :* g)

newtype Flip {- pin'eck -} f x y = Flip {pilf :: f y x}

type RC r s x y = Dot (r x) (Flip s y)

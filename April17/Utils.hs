{-# LANGUAGE KindSignatures, DataKinds, EmptyCase, GADTs,
             DeriveFunctor, StandaloneDeriving, PolyKinds,
             TypeOperators, ScopedTypeVariables, RankNTypes,
             TypeFamilies, UndecidableInstances, PatternSynonyms,
             ConstraintKinds #-}
module Utils where

type family EQ x y where
  EQ x x = True
  EQ x y = False

type family OR x y where
  OR True  y =    True
  OR x     True  = True
  OR False y     = y
  OR x     False = x

data Nat = Zero | Suc Nat deriving Show

type One = Suc Zero

type family NatLT (m :: Nat) (n :: Nat) where
  NatLT m (Suc n) = NatLE m n
  NatLT m  n      = False -- wildcards not supported in ghc<8

type family NatLE (m :: Nat) (n :: Nat) where
  NatLE m n = OR (EQ m n) (NatLT m n)

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

-- bwd utilities
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

data ALL :: (s -> *) -> Bwd s -> * where
  A0 :: ALL p B0
  AS :: ALL p gamma -> p s -> ALL p (gamma :< s)

instance FunctorIx ALL where
  mapIx f A0 = A0
  mapIx f (AS ps p) = AS (mapIx f ps) (f p)

-- nonempty lists
data NEL x = x :- Maybe (NEL x)
nel :: NEL x -> [x]
nel (x :- xs) = x : case xs of
  Nothing  -> []
  Just xs  -> nel xs
instance Show x => Show (NEL x) where show = show . nel
pattern Only x   = x :- Nothing
pattern x :-: xs = x :- Just xs

-- indexed unit type
data Happy :: k -> * where
  Happy :: Happy k
  deriving Show
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

type f -:> g = forall i . f i -> g i

class FunctorIx (f :: (i -> *) -> (j -> *)) where
  mapIx :: (x -:> y) -> f x -:> f y

class FunctorIx f => MonadIx (f :: (i -> *) -> (i -> *)) where
  joinIx :: f (f x) -:> f x
  returnIx :: x -:> f x

(?>=) :: MonadIx m => m s i -> (s -:> m t) -> m t i
m ?>= k = joinIx (mapIx k m)

data Prog :: ((i -> *) -> (i -> *)) -> ((i -> *) -> (i -> *)) where
  RET :: s i -> Prog intf s i
  DO  :: intf r i
      -> (forall t. (s -:> Prog intf t) ->
                    (r -:> Prog intf t))
      -> Prog intf s i

instance FunctorIx (Prog f) where
  mapIx f (RET x)   = RET (f x)
  mapIx f (DO c g)  = DO c $ \ k -> g (k . f)

instance MonadIx (Prog f) where
  returnIx = RET
  joinIx (RET p)   = p
  joinIx (DO c g)  = DO c $ \ k -> g (joinIx . mapIx k)

cmd :: f x -:> Prog f x
cmd c = DO c ($)

data (@=) :: * -> i -> (i -> *) where
  At :: x -> (x @= i) i

mat :: (a -> b) -> ((a @= i) -:> (b @= i))
mat f (At a) = At (f a)

(@>=) :: MonadIx m => m (a @= j) i -> (a -> m t j) -> m t i
m @>= k = m ?>= \ x -> case x of At a -> k a

(@>) :: MonadIx m => m (() @= j) i -> m t j -> m t i
m @> n = m @>= const n
infixr 3 @>

raturn :: MonadIx m => a -> m (a @= i) i
raturn = returnIx . At

data Got :: * -> (i -> *) where
  Got :: x -> Got x i

mgt :: (a -> b) -> (Got a -:> Got b)
mgt f (Got a) = Got (f a)

(/>=) :: MonadIx m => m (Got a) i -> (forall j. a -> m t j) -> m t i
m />= k = m ?>= \ x -> case x of Got a -> k a

(/>) :: MonadIx m => m (Got ()) i -> (forall j. m t j) -> m t i
m /> n = m />= const n
infixr 3 />

rgturn :: MonadIx m => a -> m (Got a) i
rgturn = returnIx . Got

------------------------------------------------------------------------------
--  a type witnessing a constraint
------------------------------------------------------------------------------

type Holds c = forall t . (c => t) -> t

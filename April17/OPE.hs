------------------------------------------------------------------------------
-----                                                                    -----
-----     Order-Preserving Embeddings and Coproducts of their Slices     -----
-----                                                                    -----
------------------------------------------------------------------------------

{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances,
             PolyKinds #-}

module OPE where

import Utils

------------------------------------------------------------------------------
--  order-preserving embeddings
------------------------------------------------------------------------------

data (<=) :: Bwd s -> Bwd s -> * where
  OZ :: B0 <= B0
  OS :: gamma <= delta -> (gamma :< s) <= (delta :< s)
  O' :: gamma <= delta -> gamma <= (delta :< s)

-- composition
(-<=-) :: delta <= theta -> gamma <= delta -> gamma <= theta
OZ   -<=- OZ    = OZ
OS r -<=- OS r' = OS (r -<=- r')
OS r -<=- O' r' = O' (r -<=- r')
O' r -<=- r'    = O' (r -<=- r')
infixr 9 -<=-

class Sorted (gamma :: Bwd s) where
  oI :: gamma <= gamma    -- identity
  oN :: B0    <= gamma    -- initiality

instance Sorted B0 where
  oI = OZ
  oN = OZ

instance Sorted gamma => Sorted (gamma :< s) where
  oI = OS oI
  oN = O' oN

sortedObj :: gamma <= delta -> Holds (Sorted gamma, Sorted delta)
sortedObj OZ t = t
sortedObj (OS r) t = sortedObj r t
sortedObj (O' r) t = sortedObj r t

{-
One wart here is that while every object has an identity, runtime knowledge
of that object (or at least its length) is required to construct that
identity. So we have
  oI :: Sorted gamma =>   gamma <= gamma
rather than
  oI :: gamma <= gamma

As things stand, we cannot make <= an instance of Category.

Two options for "improving" the situation:
  1. Replace OZ (identity for B0) with OI (identity in general) and suck up
       the resulting redundancy.
  2. Degrade Category to "Partial Category", parametrising over a constraint
       (Sorted, in this case) which says which objects have identities. The
       sortedObj function would move into the class, asserting that any
       object which is the source or target of any morphism must have an
       identity morphism.
-}


------------------------------------------------------------------------------
--  thing-with-thinning
------------------------------------------------------------------------------

data (^) :: (Bwd s -> *) -> (Bwd s -> *) where
  (:^) :: f gamma -> gamma <= delta -> f ^ delta
infixl 5 :^

instance FunctorIx (^) where
  mapIx f (x :^ r) = f x :^ r

{-
Morally, things-with-thinning is a MonadIx, with
  returnIx x = x :^ oI
  joinIx ((x :^ r) :^ t) = x :^ (t -<=- r)
Again, however, the need for a Sorted constraint messes that up.
-}


------------------------------------------------------------------------------
--  coproduct of slice
------------------------------------------------------------------------------

-- CoP gamma delta theta encodes a pair of embeddings,
--   lCoP :: gamma <= theta, rCoP :: delta <= theta
-- which, between them, cover theta.

data CoP :: Bwd s -> Bwd s -> Bwd s -> * where
  CZZ :: CoP B0 B0 B0
  CSS :: CoP gamma delta theta -> CoP (gamma :< s) (delta :< s) (theta :< s) 
  CS' :: CoP gamma delta theta -> CoP (gamma :< s) delta (theta :< s) 
  C'S :: CoP gamma delta theta -> CoP gamma (delta :< s) (theta :< s) 

lCoP :: CoP gamma delta theta -> gamma <= theta
lCoP CZZ = OZ
lCoP (CSS c) = OS (lCoP c)
lCoP (CS' c) = OS (lCoP c)
lCoP (C'S c) = O' (lCoP c)

rCoP :: CoP gamma delta theta -> delta <= theta
rCoP CZZ = OZ
rCoP (CSS c) = OS (rCoP c)
rCoP (CS' c) = O' (rCoP c)
rCoP (C'S c) = OS (rCoP c)

-- Given two embeddings which may not cover their shared codomain,
-- we may compute that part of their codomain which they *do* cover,
-- together with its embedding into the whole.

coP :: gamma <= theta -> delta <= theta -> CoP gamma delta ^ theta
coP OZ OZ = CZZ :^ OZ
coP (OS r) (OS r') = case coP r r' of f :^ t -> CSS f :^ OS t
coP (OS r) (O' r') = case coP r r' of f :^ t -> CS' f :^ OS t
coP (O' r) (OS r') = case coP r r' of f :^ t -> C'S f :^ OS t
coP (O' r) (O' r') = case coP r r' of f :^ t -> f :^ O' t

{-
The unspoken invariant here is that

  coP r0 r1 = c :^ r
---------------------------------------------
  r0 = r -<=- lCoP c  &  r1 = r -<=- rCoP c

          theta
            ^
           /|\
          / r \
         /  |  \
       r0  _^_  r1
       / _/   \_ \
      /_/   c   \_\
      '           '
    gamma       delta

and the apex of c is as low as possible.

Any other such diagram (r0 = r' -<=- r0'  &  r1 = r' -<=- r1')
factors through ours: for some s,
   r0' = s -<=- lCoP c  &  r1' = s -<=- rCop c  &  r = r' -<=- s

The slice category, <=/theta, represents subcontexts of theta: its
objects are embeddings into theta; their morphisms are triangles.
Here, our c is the witness that r is the categorical coproduct of
r0 and r1.
-}


------------------------------------------------------------------------------
--  selections
------------------------------------------------------------------------------

-- Select gamma s delta means that removing s from gamma leaves delta
data Select :: Bwd s -> s -> Bwd s -> * where
  Top  :: Select (gamma :< s) s gamma
  Pop  :: Select gamma s delta -> Select (gamma :< t) s (delta :< t)

-- selections interact with coproducts to tell us where to find the selected
data Hits :: s -> Bwd s -> Bwd s -> Bwd s -> * where
  HLeft  :: Select gamma0' s gamma0 ->
            CoP gamma0 gamma1' gamma ->
            Hits s gamma0' gamma1' gamma
  HRight ::                            Select gamma1' s gamma1 ->
            CoP gamma0' gamma1 gamma ->
            Hits s gamma0' gamma1' gamma
  HBoth  :: Select gamma0' s gamma0 -> Select gamma1' s gamma1 ->
            CoP gamma0 gamma1 gamma ->
            Hits s gamma0' gamma1' gamma

hits :: CoP gamma0' gamma1' gamma' -> Select gamma' s gamma ->
        Hits s gamma0' gamma1' gamma
hits (CSS c) Top = HBoth Top Top c 
hits (CS' c) Top = HLeft Top c
hits (C'S c) Top = HRight Top c
hits (CSS c) (Pop x) = case hits c x of
  HLeft x c -> HLeft (Pop x) (CSS c)
  HRight y c -> HRight (Pop y) (CSS c)
  HBoth x y c -> HBoth (Pop x) (Pop y) (CSS c)
hits (CS' c) (Pop x) = case hits c x of
  HLeft x c -> HLeft (Pop x) (CS' c)
  HRight y c -> HRight y  (CS' c)
  HBoth x y c -> HBoth (Pop x) y (CS' c)
hits (C'S c) (Pop x) = case hits c x of
  HLeft x c -> HLeft x (C'S c)
  HRight y c -> HRight (Pop y) (C'S c)
  HBoth x y c -> HBoth x (Pop y) (C'S c)

------------------------------------------------------------------------------
--  relevant data structures
------------------------------------------------------------------------------

-- unit and product

data Unit :: Bwd s -> * where
  Void :: Unit B0

void :: Sorted gamma => Unit ^ gamma
void = Void :^ oN

data (><) :: (Bwd s -> *) -> (Bwd s -> *) -> (Bwd s -> *) where
  Pair :: CoP gamma delta theta -> f gamma -> g delta -> (f >< g) theta
infixr 8 ><

pair :: f ^ theta -> g ^ theta -> (f >< g) ^ theta
pair (f :^ r) (g :^ r') = case coP r r' of c :^ t -> Pair c f g :^ t 

-- usage and binding

data This :: s -> (Bwd s -> *) where
  It :: This s (B0 :< s)

data (!-) :: s -> (Bwd s -> *) -> (Bwd s -> *) where
  K :: f gamma -> (s !- f) gamma 
  L :: String -> f (gamma :< s) -> (s !- f) gamma
infixr 9 !-

abstract :: String -> f ^ (gamma :< s) -> (s !- f) ^ gamma
abstract x (f :^ OS r) = L x f :^ r
abstract _ (f :^ O' r) = K f :^ r

dive :: (s !- f) ^ gamma -> f ^ (gamma :< s)
dive (K f :^ r) = f :^ O' r
dive (L _ f :^ r) = f :^ OS r


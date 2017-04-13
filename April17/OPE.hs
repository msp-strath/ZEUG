------------------------------------------------------------------------------
-----                                                                    -----
-----     Order-Preserving Embeddings and Coproducts of their Slices     -----
-----                                                                    -----
------------------------------------------------------------------------------

{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances,
             PolyKinds #-}

module OPE where

import Prelude hiding ((^^))
import Data.Type.Equality((:~:)(Refl))
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
  misser :: Select gamma B0 gamma
  hitter :: Select gamma gamma B0
  copL :: CoP gamma B0 gamma
  copR :: CoP B0 gamma gamma

instance Sorted B0 where
  oI = OZ
  oN = OZ
  misser = None
  hitter = None
  copL = CZZ
  copR = CZZ

instance Sorted gamma => Sorted (gamma :< s) where
  oI = OS oI
  oN = O' oN
  misser = Miss misser
  hitter = Hit hitter
  copL = CS' copL
  copR = C'S copR

sortedObj :: gamma <= delta -> Holds (Sorted gamma, Sorted delta)
sortedObj OZ t = t
sortedObj (OS r) t = sortedObj r t
sortedObj (O' r) t = sortedObj r t

discard :: gamma <= delta -> ALL p delta -> ALL p gamma
discard OZ A0 = A0
discard (OS r) (AS ps p) = AS (discard r ps) p
discard (O' r) (AS ps _) = discard r ps

missDiscard :: CoP gamma0 gamma1 gamma ->
               Select gamma theta ^ delta -> ALL f theta ->
               (forall theta0 theta1.
                Select gamma0 theta0 ^ delta -> ALL f theta0 ->
                Select gamma1 theta1 ^ delta -> ALL f theta1 -> t) ->
               t
missDiscard c (xz :^ r) fz g = case hits xz c of
  Hits xz0 xz1 c0 c1 -> g (xz0 :^ r -<=- lCoP c1) (discard (lCoP c0) fz) (xz1 :^ r -<=- rCoP c1) (discard (rCoP c0) fz)
               

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

wk :: f ^ gamma -> f ^ (gamma :< s)
wk (f :^ r) = f :^ O' r

(^^) :: f ^ gamma -> gamma <= delta -> f ^ delta
(f :^ r) ^^ r' = f :^ r' -<=- r

joinH :: ((^) f) ^ gamma -> f ^ gamma
joinH (fH :^ r) = fH ^^ r

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

sortedCoP :: CoP gamma delta theta ->
             Holds (Sorted gamma, Sorted delta, Sorted theta)
sortedCoP c t = sortedObj (lCoP c) $ sortedObj (rCoP c) t

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

data Select :: Bwd s -> Bwd s -> Bwd s -> * where
  None :: Select B0 B0 B0
  Hit :: Select gamma' delta gamma -> Select (gamma' :< s) (delta :< s) gamma
  Miss :: Select gamma' delta gamma -> Select (gamma' :< s) delta (gamma :< s)

data Hits :: Bwd s -> Bwd s -> Bwd s -> Bwd s -> * where
  Hits :: Select gamma0' theta0 gamma0 -> Select gamma1' theta1 gamma1 ->
          CoP theta0 theta1 theta -> CoP gamma0 gamma1 gamma ->
          Hits gamma0' gamma1' theta gamma

hits :: Select gamma' theta gamma -> CoP gamma0' gamma1' gamma' ->
        Hits  gamma0' gamma1' theta gamma
hits None CZZ = Hits None None CZZ CZZ
hits (Miss s) (CSS c) = case hits s c of
  Hits s0 s1 ctheta cgamma -> Hits (Miss s0) (Miss s1) ctheta (CSS cgamma)
hits (Miss s) (CS' c) = case hits s c of
  Hits s0 s1 ctheta cgamma -> Hits (Miss s0) s1 ctheta (CS' cgamma)
hits (Miss s) (C'S c) = case hits s c of
  Hits s0 s1 ctheta cgamma -> Hits s0 (Miss s1) ctheta (C'S cgamma)
hits (Hit s) (CSS c) = case hits s c of
  Hits s0 s1 ctheta cgamma -> Hits (Hit s0) (Hit s1) (CSS ctheta) cgamma
hits (Hit s) (CS' c) = case hits s c of
  Hits s0 s1 ctheta cgamma -> Hits (Hit s0) s1 (CS' ctheta) cgamma
hits (Hit s) (C'S c) = case hits s c of
  Hits s0 s1 ctheta cgamma -> Hits s0 (Hit s1) (C'S ctheta) cgamma

missAll :: Select gamma' B0 gamma -> gamma' :~: gamma
missAll None = Refl
missAll (Miss s) = case missAll s of Refl -> Refl

data ThickSelect :: Bwd s -> Bwd s -> Bwd s -> * where
  ThickSelect :: Select gamma theta delta ->
                 theta <= theta' -> delta <= delta' ->
                 ThickSelect gamma theta' delta'

thickSelect :: gamma <= gamma' -> Select gamma' theta' delta' ->
               ThickSelect gamma theta' delta'
thickSelect OZ None = ThickSelect None OZ OZ
thickSelect (OS r) (Hit s) = case thickSelect r s of
  ThickSelect s rtheta rdelta -> ThickSelect (Hit s) (OS rtheta) rdelta
thickSelect (OS r) (Miss s) = case thickSelect r s of
  ThickSelect s rtheta rdelta -> ThickSelect (Miss s) rtheta (OS rdelta)
thickSelect (O' r) (Hit s) = case thickSelect r s of
  ThickSelect s rtheta rdelta -> ThickSelect s (O' rtheta) rdelta
thickSelect (O' r) (Miss s) = case thickSelect r s of
  ThickSelect s rtheta rdelta -> ThickSelect s rtheta (O' rdelta)

wkSelect :: Select gamma theta ^ delta ->
            Select (gamma :< s) theta ^ (delta :< s)
wkSelect (xz :^ r) = Miss xz :^ OS r

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

(>^<) :: (f >< g) ^ theta -> (f ^ theta -> g ^ theta -> t) -> t
Pair c f g :^ r >^< h = h (f :^ r -<=- lCoP c) (g :^ r -<=- rCoP c)
infixr 4 >^<

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

nom :: (s !- f) gamma -> String
nom (L x _) = x
nom (K _) = "h"

------------------------------------------------------------------------------
-- Equality testing
------------------------------------------------------------------------------

opeEq :: gamma <= theta -> delta <= theta -> Maybe (gamma :~: delta)
opeEq OZ     OZ      = Just Refl
opeEq (OS r) (OS r') = do
  Refl <- opeEq r r'
  return Refl
opeEq (O' r) (O' r') = do
  Refl <- opeEq r r'
  return Refl
opeEq _ _ = Nothing

class SyntaxEq (f :: Bwd s -> *) where
  eq :: f gamma -> f gamma -> Maybe ()

instance SyntaxEq f => SyntaxEq ((^) f) where
  eq (f :^ r) (g :^ r') = do
    Refl <- opeEq r r'
    eq f g

instance SyntaxEq Unit where
  eq _ _ = return ()

instance (SyntaxEq f, SyntaxEq g) => SyntaxEq (f >< g) where
  eq (Pair c f g) (Pair c' f' g') = do
    eq (f :^ lCoP c) (f' :^ lCoP c')
    eq (g :^ rCoP c) (g' :^ rCoP c')

instance SyntaxEq (This s) where
  eq _ _ = return ()

instance SyntaxEq f => SyntaxEq (s !- f) where
  eq (K t) (K t') = eq t t'
  eq (L _ t) (L _ t') = eq t t'
  eq _ _ = fail "gotcha"

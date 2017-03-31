--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances #-}
module Kernel where

import Utils

data Sort = Chk | Syn | Pnt
{-:: * where
  Chk :: Sort
  Syn :: Sort
  Pnt :: Sort-}

{- TODO report
    • Type constructor ‘Sorts’ cannot be used here
        (Perhaps you intended to use TypeInType)
    • In the kind ‘Sorts -> Sorts -> *’
-}
type Sorts = Bwd Sort

data (<=) :: Bwd Sort -> Bwd Sort -> * where
  OZ :: B0 <= B0
  OS :: gamma <= delta -> (gamma :< s) <= (delta :< s)
  O' :: gamma <= delta -> gamma <= (delta :< s)

class Sorted (gamma :: Bwd Sort) where
  oI :: gamma <= gamma
  oN :: B0 <= gamma

instance Sorted B0 where
  oI = OZ
  oN = OZ

instance Sorted gamma => Sorted (gamma :< s) where
  oI = OS oI
  oN = O' oN

type Holds c = forall t . (c => t) -> t

sortedObj :: gamma <= delta -> Holds (Sorted gamma, Sorted delta)
sortedObj OZ t = t
sortedObj (OS r) t = sortedObj r t
sortedObj (O' r) t = sortedObj r t

(-<=-) :: delta <= theta -> gamma <= delta -> gamma <= theta
OZ -<=- OZ = OZ
OS r -<=- OS r' = OS (r -<=- r')
OS r -<=- O' r' = O' (r -<=- r')
O' r -<=- r' = O' (r -<=- r')
infixr 9 -<=-

data (^) :: (Bwd Sort -> *) -> (Bwd Sort -> *) where
  (:^) :: f gamma -> gamma <= delta -> f ^ delta
infixl 5 :^

instance FunctorIx (^) where
  mapIx f (x :^ r) = f x :^ r

-- not dependent on sort
data CoP :: Bwd Sort -> Bwd Sort -> Bwd Sort -> * where
  CZZ :: CoP B0 B0 B0
  CSS :: CoP gamma delta theta -> CoP (gamma :< s) (delta :< s) (theta :< s) 
  CS' :: CoP gamma delta theta -> CoP (gamma :< s) delta (theta :< s) 
  C'S :: CoP gamma delta theta -> CoP gamma (delta :< s) (theta :< s) 

coP :: gamma <= theta -> delta <= theta -> CoP gamma delta ^ theta
coP OZ OZ = CZZ :^ OZ
coP (OS r) (OS r') = case coP r r' of f :^ t -> CSS f :^ OS t
coP (OS r) (O' r') = case coP r r' of f :^ t -> CS' f :^ OS t
coP (O' r) (OS r') = case coP r r' of f :^ t -> C'S f :^ OS t
coP (O' r) (O' r') = case coP r r' of f :^ t -> f :^ O' t

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

data This :: Sort -> (Bwd Sort -> *) where
  It :: This s (B0 :< s)

data (><) :: (Bwd Sort -> *) -> (Bwd Sort -> *) -> (Bwd Sort -> *) where
  Pair :: CoP gamma delta theta -> f gamma -> g delta -> (f >< g) theta
infixr 8 ><

pair :: f ^ theta -> g ^ theta -> (f >< g) ^ theta
pair (f :^ r) (g :^ r') = case coP r r' of c :^ t -> Pair c f g :^ t 

data (!-) :: Sort -> (Bwd Sort -> *) -> (Bwd Sort -> *) where
  K :: f gamma -> (s !- f) gamma 
  L :: f (gamma :< s) -> (s !- f) gamma
infixr 9 !-

-- these are normal forms
data Term :: Sort -> (Bwd Sort -> *) where
  Star :: Term Chk B0
  Pi :: (Term Chk  ><  Syn !- Term Chk) gamma -> Term Chk gamma
  Lam :: (Syn !- Term Chk) gamma -> Term Chk gamma
  E :: Term Syn gamma -> Term Chk gamma
  V :: This Syn gamma -> Term Syn gamma
  App :: (Term Syn >< Term Chk) gamma -> Term Syn gamma

data Select :: Bwd Sort -> Sort -> Bwd Sort -> * where
  Top :: Select (gamma :< s) s gamma
  Pop  :: Select gamma s delta -> Select (gamma :< t) s (delta :< t)

data Hits :: Sort -> Bwd Sort -> Bwd Sort -> Bwd Sort -> * where
  HLeft  :: Select gamma0' s ^ gamma -> gamma1' <= gamma ->
            Hits s gamma0' gamma1' gamma
  HRight :: Hits s gamma0' gamma1' gamma
  HBoth  :: Hits s gamma0' gamma1' gamma

hits :: CoP gamma0' gamma1' gamma' -> Select gamma' s gamma ->
        Hits s gamma0' gamma1' gamma
hits (CSS c) Top = HBoth
hits (CS' c) Top = HLeft (Top :^ lCoP c) (rCoP c)
hits (C'S c) Top = HRight
hits (CSS c) (Pop x) = case hits c x of
  HLeft (x :^ r) r' -> HLeft (Pop x :^ OS r) (OS r')
  HRight -> HRight
  HBoth  -> HBoth
hits (CS' c) (Pop x) = case hits c x of
  HLeft (x :^ r) r' -> HLeft (Pop x :^ OS r) (O' r')
  HRight -> HRight
  HBoth  -> HBoth
hits (C'S c) (Pop x) = case hits c x of
  HLeft (x :^ r) r' -> HLeft (x :^ O' r) (OS r')
  HRight -> HRight
  HBoth  -> HBoth

class Sub (f :: Bwd Sort -> *) where
  sub :: f gamma' -> Select gamma' Syn ^ delta ->
         Term Chk ^ delta -> f ^ delta

instance Sub (Term Chk) where
  sub (Pi (Pair c _S _T)) (x :^ r) s = case hits c x of
    HLeft (x' :^ r') r'' ->
      mapIx Pi $ pair (sub _S (x' :^ r -<=- r') s) (_T :^ r -<=- r'')

{- TODO
   - [ ] HRight, HBoth
   - [ ] generalize things that return them
   - [ ] sub for not pi
   - [ ] if f and g are Sub then f >< g is too
   - [ ] if f is Sub then s !- f is too
-}

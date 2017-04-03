--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances,
             TypeFamilies, StandaloneDeriving, DeriveFoldable,
             DeriveFunctor, DeriveTraversable #-}
module Kernel where

import Utils
import OPE

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

-- these are normal forms
data Term :: Sort -> (Bwd Sort -> *) where
  Star :: Unit gamma -> Term Chk gamma
  Pi :: (Term Chk  ><  Syn !- Term Chk) gamma -> Term Chk gamma
  Lam :: (Syn !- Term Chk) gamma -> Term Chk gamma
  E :: Term Syn gamma -> Term Chk gamma
  V :: This Syn gamma -> Term Syn gamma
  App :: (Term Syn >< Term Chk) gamma -> Term Syn gamma

class Sub (f :: Bwd Sort -> *) where
  type SubImage f :: Bwd Sort -> *
  image :: f -:> SubImage f
  sub :: f gamma' -> Select gamma' Syn ^ delta ->
         Term Chk ^ delta -> SubImage f ^ delta


instance (Sub f , Sub g) => Sub (f >< g) where
  type SubImage (f >< g) = SubImage f >< SubImage g
  image (Pair c f g) = Pair c (image f) (image g)
  sub (Pair c f g) (z :^ r) s = case hits c z of
    HLeft  x c -> pair (sub f (x :^ r -<=- lCoP c) s) (image g :^ r -<=- rCoP c)
    HRight y c -> pair (image f :^ r -<=- lCoP c) (sub g (y :^ r -<=- rCoP c) s)
    HBoth  x y c ->
      pair (sub f (x :^ r -<=- lCoP c) s) (sub g (y :^ r -<=- rCoP c) s)

instance Sub f => Sub (s !- f) where
  type SubImage (s !- f) = s !- SubImage f
  image (K f) = K (image f)
  image (L x f) = L x (image f)
  sub (K f) xr s = mapIx K $ sub f xr s
  sub (L y f) (x :^ r) (t :^ r') = abstract y (sub f (Pop x :^ OS r) (t :^ O' r'))

instance Sub (Term Chk) where
  type SubImage (Term Chk) = Term Chk
  image = id
  sub (Pi _ST) xr s = mapIx Pi $ sub _ST xr s
  sub (Lam t) xr s = mapIx Lam $ sub t xr s
  sub (E e) xr s = sub e xr s

instance Sub (Term Syn) where
  type SubImage (Term Syn) = Term Chk
  image = E
  sub (V It) xr s = s
  sub (App fa) xr s = app (sub fa xr s)

app :: (Term Chk >< Term Chk) ^ delta -> Term Chk ^ delta
app (Pair c (E e) a :^ r) = E (App (Pair c e a)) :^ r
app (Pair c (Lam (K t)) a :^ r) = t :^ r -<=- lCoP c 
app (Pair c (Lam (L _ t)) a :^ r) =
  sub t (Top :^ r -<=- lCoP c) (a :^ r -<=- rCoP c)

data Env :: Bwd Sort -> * -> * where
  N0 :: Env B0 a
  NS :: Env gamma a -> a -> Env (gamma :< s) a

deriving instance Foldable (Env gamma)
deriving instance Functor (Env gamma)
deriving instance Traversable (Env gamma)

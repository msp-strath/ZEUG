--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances,
             TypeFamilies, StandaloneDeriving, DeriveFoldable,
             DeriveFunctor, DeriveTraversable #-}
module Kernel where

import Utils
import OPE
import Data.Void

------------------------------------------------------------------------------
-- Syntactic Sorts
------------------------------------------------------------------------------

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


------------------------------------------------------------------------------
-- Terms (in normal form)
------------------------------------------------------------------------------

data Term :: Sort -> (Bwd Sort -> *) where
  Star :: Unit gamma -> Term Chk gamma
  Pi :: (Term Chk  ><  Syn !- Term Chk) gamma -> Term Chk gamma
  Lam :: (Syn !- Term Chk) gamma -> Term Chk gamma
  E :: Term Syn gamma -> Term Chk gamma
  V :: This s gamma -> Term s gamma
  App :: (Term Syn >< Term Chk) gamma -> Term Syn gamma


------------------------------------------------------------------------------
-- derived constructors for thinned terms
------------------------------------------------------------------------------

star :: Sorted gamma => Term Chk ^ gamma
star = Star Void :^ oN


------------------------------------------------------------------------------
-- hereditary substitution
------------------------------------------------------------------------------

class Sub (f :: Bwd Sort -> *) where
  sub :: f gamma' -> Select gamma' s ^ delta -> Radical s delta -> f ^ delta

data Radical :: Sort -> Bwd Sort -> * where
  (:::) :: Term Chk ^ delta -> Term Chk ^ delta -> Radical Syn delta
infixr 3 :::

-- We substitute a radical for a variable. Radicals can cause computation.

instance Sub (Term Chk) where
  sub (Pi _ST) xr s = mapIx Pi $ sub _ST xr s
  sub (Lam t)  xr s = mapIx Lam $ sub t xr s
  sub (E e)    xr s = stop $ subSyn e xr s

-- substitution in a Term Syn can radicalise it
subSyn :: Term Syn gamma' ->
          Select gamma' s ^ delta -> Radical s delta ->
          Either (Radical Syn delta) (Term Syn ^ delta)
subSyn (V It) (Top :^ r) s = Left s
subSyn (App (Pair c f a)) (z :^ r) s = case hits c z of
    HRight  y c -> Right . mapIx App $  -- right hit means no radical
      pair (f :^ r -<=- lCoP c) (sub a (y :^ r -<=- rCoP c) s)
      -- left hit means risk of radical
    HLeft x   c -> go (subSyn f (x :^ r -<=- lCoP c) s) (a :^ r -<=- rCoP c)
    HBoth x y c -> go (subSyn f (x :^ r -<=- lCoP c) s)
                      (sub a (y :^ r -<=- rCoP c) s)
  where
    go (Left r)  a = Left (app r a)
    go (Right e) a = Right (mapIx App (pair e a))

-- we can always stop if a Term Chk is wanted, stripping the spent type
stop :: Either (Radical Syn delta) (Term Syn ^ delta) -> Term Chk ^ delta
stop (Left (t ::: _))  = t
stop (Right e)         = mapIx E e

-- structural rule for pairing
instance (Sub f , Sub g) => Sub (f >< g) where
  sub (Pair c f g) (z :^ r) s = case hits c z of
    HLeft  x c -> pair (sub f (x :^ r -<=- lCoP c) s) (g :^ r -<=- rCoP c)
    HRight y c -> pair (f :^ r -<=- lCoP c) (sub g (y :^ r -<=- rCoP c) s)
    HBoth  x y c ->
      pair (sub f (x :^ r -<=- lCoP c) s) (sub g (y :^ r -<=- rCoP c) s)

-- structural rule for binding
instance Sub f => Sub (s !- f) where
  sub (K f) xr s = mapIx K $ sub f xr s
  sub (L y f) (x :^ r) s = abstract y (sub f (Pop x :^ OS r) (radW s)) where
    radW :: Radical t gamma -> Radical t (gamma :< s)
    radW (t :^ r ::: _T :^ _R) = t :^ O' r ::: _T :^ O' _R


------------------------------------------------------------------------------
-- computation is the elimination of radicals
------------------------------------------------------------------------------

app :: Radical Syn delta -> Term Chk ^ delta -> Radical Syn delta
app (f :^ r ::: Pi _ST :^ _R) s = _ST :^ _R >^< \ _S _T ->
  (case f of
    E e   -> mapIx (E . App) (pair (e :^ r) s)
    Lam t -> instantiate (t :^ r) (s ::: _S)
  ) ::: instantiate _T (s ::: _S)
  
instantiate :: (s !- Term Chk) ^ delta -> Radical s delta ->
               Term Chk ^ delta
instantiate (K t :^ r) _ = t :^ r
instantiate (L _ t :^ r) a = sub t (Top :^ r) a


------------------------------------------------------------------------------
-- environments of the unremarkable kind
------------------------------------------------------------------------------

data Env :: Bwd Sort -> * -> * where
  N0 :: Env B0 a
  NS :: Env gamma a -> a -> Env (gamma :< s) a

deriving instance Foldable (Env gamma)
deriving instance Functor (Env gamma)
deriving instance Traversable (Env gamma)


------------------------------------------------------------------------------
-- Singletons for Sorts
------------------------------------------------------------------------------

data Sorty :: Sort -> * where
  Chky :: Sorty Chk
  Syny :: Sorty Syn
  Pnty :: Sorty Pnt

sortEq :: Sorty s -> Sorty s' -> Maybe (s == s')
sortEq Chky Chky = Just Refl
sortEq Syny Syny = Just Refl
sortEq Pnty Pnty = Just Refl
sortEq _    _    = Nothing
  

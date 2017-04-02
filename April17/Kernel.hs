--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances #-}
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
  Star :: Term Chk B0
  Pi :: (Term Chk  ><  Syn !- Term Chk) gamma -> Term Chk gamma
  Lam :: (Syn !- Term Chk) gamma -> Term Chk gamma
  E :: Term Syn gamma -> Term Chk gamma
  V :: This Syn gamma -> Term Syn gamma
  App :: (Term Syn >< Term Chk) gamma -> Term Syn gamma


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

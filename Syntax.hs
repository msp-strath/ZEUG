{-# LANGUAGE KindSignatures, DataKinds, ScopedTypeVariables, GADTs #-}
module Syntax where
import Utils
import Data.Proxy

-- from here for world module? But, Refs have types, so need syntax...

data World = W0 | Bind World

class Worldly (w :: World) where
  next :: Proxy w -> Int

instance Worldly W0 where
  next _ = 0

instance Worldly w => Worldly (Bind w) where
  next (_ :: Proxy (Bind w)) = next (Proxy :: Proxy w) + 1

data Ref w = Ref {refname :: Int , reftype :: TYPE w}
-- export only projection reftype and eq instance defined on ints only

instance Eq (Ref w) where
  Ref i _ == Ref j _ = i == j

-- not used yet?
newtype Fink (n :: Nat)(w :: World) = Fink {fink :: Fin n}

-- to here for world module?

-- syntax

data Hd (n :: Nat)(w :: World) where
  V :: Fin n -> Hd n w
  P :: Ref w -> Hd n w
  (:::) :: Tm n w -> Tm n w -> Hd n w

data En (n :: Nat)(w :: World) = Hd n w :$ Bwd (Tm n w)

data Tm (n :: Nat)(w :: World) where
  En  :: En n w -> Tm n w
  Set :: Tm n w
  Pi  :: Tm n w -> Tm (Suc n) w -> Tm n w
  Lam :: Tm (Suc n) w -> Tm n w

type TYPE = Tm Zero  -- trusted
type TERM = Tm Zero  -- not trusted


{-# LANGUAGE KindSignatures, GADTs, DataKinds, StandaloneDeriving #-}
module NoFree where

import Utils

data Hd (n :: Nat) where
  V :: Fin n -> Hd n
  (:::) :: Tm n -> Tm n -> Hd n
  deriving Show

data En (n :: Nat) = Hd n :$ Bwd (Tm n) deriving Show

data Tm (n :: Nat) where
  En  :: En n -> Tm n
  Set :: Tm n
  Pi  :: Tm n -> Tm (Suc n) -> Tm n
  Lam :: Tm (Suc n) -> Tm n
  deriving Show


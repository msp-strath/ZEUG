{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
module DeBrujnify where

import Utils
import Data.List
import Data.Maybe

data Raw = RLam String Raw
         | RApp Raw    Raw
         | RVar String Nat
         deriving Show

data Tm (n :: Nat) :: * where
  Lam :: Tm (Suc n)         -> Tm n
  App :: Tm n       -> Tm n -> Tm n
  V   :: Fin n              -> Tm n
  P   :: String             -> Tm n

deriving instance Show (Tm n)

type SC = Maybe

deBruijnify :: Vec String n -> Raw -> SC (Tm n)
deBruijnify g (RLam x t) = Lam <$> deBruijnify (VCons x g) t
deBruijnify g (RApp t u) = App <$> deBruijnify g t <*> deBruijnify g u
deBruijnify g (RVar x n) = V   <$> velemIndex' x n g


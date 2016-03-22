{-# LANGUAGE RankNTypes, DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, PolyKinds, UndecidableInstances,
             FlexibleInstances, FlexibleContexts, ScopedTypeVariables, StandaloneDeriving,
             PatternSynonyms, TypeOperators, ConstraintKinds, TupleSections #-}
module PHOAS(
  var,
  var',
  lam,
  pi,
  sg,
  letin
  ) where

import Prelude hiding (pi)
import Data.Proxy
import Utils
import Syntax

newtype Included (m :: Nat) (n :: Nat) = Included { rename :: Fin m -> Fin n }

class CIncluded (m :: Nat) (n :: Nat) (b :: Bool) where
  included :: Proxy b -> Included m n

instance CIncluded m m b where
  included _ = Included id

instance CIncluded m n (NatLT m n) => CIncluded m (Suc n) True where
  included _ = Included $ FSuc . rename (included (Proxy :: Proxy (NatLT m n)))

newtype FreshVar m w = FreshVar { var :: forall n. CIncluded (Suc m) n (NatLT (Suc m) n) => En (Syn n) w }

var' :: forall m n w. CIncluded (Suc m) n (NatLT (Suc m) n) => FreshVar m w -> Tm (Syn n) w
var' = En . var

lam :: forall m w. (FreshVar m w -> Tm (Syn (Suc m)) w) -> Tm (Syn m) w
lam f = Lam (f $ FreshVar freshVar) where

  freshVar :: forall n. CIncluded (Suc m) n (NatLT (Suc m) n) => En (Syn n) w
  freshVar = V $ rename (included (Proxy :: Proxy (NatLT (Suc m) n))) (FZero :: Fin (Suc m))


pi :: forall m w. Tm (Syn m) w -> (FreshVar m w -> Tm (Syn (Suc m)) w) -> Tm (Syn m) w
pi s t = RawPi s $ lam t

sg :: forall m w. Tm (Syn m) w -> (FreshVar m w -> Tm (Syn (Suc m)) w) -> Tm (Syn m) w
sg s t = RawSg s $ lam t

letin :: forall m w. En (Syn m) w -> (FreshVar m w -> Tm (Syn (Suc m)) w) -> Tm (Syn m) w
letin e t = Let e (t $ FreshVar freshVar) where

  freshVar :: forall n. CIncluded (Suc m) n (NatLT (Suc m) n) => En (Syn n) w
  freshVar = V $ rename (included (Proxy :: Proxy (NatLT (Suc m) n))) (FZero :: Fin (Suc m))

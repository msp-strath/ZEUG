{-# LANGUAGE KindSignatures, DataKinds, GADTs #-}
module Start where

import Data.Maybe

data Nat = Zero | Suc Nat

data Fin (n :: Nat) where
  FZero :: Fin (Suc n)
  FSuc  :: Fin n -> Fin (Suc n)

data Bwd x = B0 | Bwd x :< x

data Hd (n :: Nat) where
  V :: Fin n -> Hd n
  P :: Hd n
  (:::) :: Tm n -> Tm n -> Hd n

data En (n :: Nat) = Hd n :$ Bwd (Tm n)

data Tm (n :: Nat) where
  En  :: En n -> Tm n
  Set :: Tm n
  Pi  :: Tm n -> Tm (Suc n) -> Tm n
  Lam :: Tm (Suc n) -> Tm n

type TYPE = Tm Zero  -- trusted
type TERM = Tm Zero  -- not trusted

type TC = Maybe

isType :: TERM -> TC ()
isType (En e) = enType e >> return ()
isType Set    = return ()
isType (Pi sty tty) = do
  isType sty
  undefined
isType _ = error "blerk"

(>:>) :: TYPE -> TERM -> TC ()
(>:>) = undefined

hdType :: Hd Zero -> TC TYPE
hdType = undefined

($:) :: (En Zero, TYPE) -> TERM -> TC TYPE
($:) = undefined

enType :: En Zero -> TC TYPE
enType (h :$ sz) = hdType h >>= \ ty -> go (h,ty) sz where
  go (h,ty) B0        = return ty
  go (h,ty) (sz :< s) = do
    ety <- go (h,ty) sz
    (h :$ sz, ety) $: s

(!-) :: TYPE -> (En Zero -> TC ()) -> TC ()
(!-) = undefined

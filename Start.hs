{-# OPTIONS -Wall -fwarn-incomplete-patterns #-}
{-# LANGUAGE KindSignatures, DataKinds, 
             GADTs, DeriveFunctor, RankNTypes, EmptyCase #-}
module Start where

import Data.Maybe
import Unsafe.Coerce

data World = W0

data Nat = Zero | Suc Nat

data Ref w = Ref (Int , TYPE w)

data Fin (n :: Nat) where
  FZero :: Fin (Suc n)
  FSuc  :: Fin n -> Fin (Suc n)

absurd :: Fin Zero -> a
absurd k = case k of {}

newtype Fink (n :: Nat)(w :: World) = Fink {fink :: Fin n}

data Bwd x = B0 | Bwd x :< x deriving Functor

(+<+) :: Bwd x -> Bwd x -> Bwd x
xs +<+ B0 = xs
xs +<+ (ys :< y) = (xs +<+ ys) :< y

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

data Extended (u :: World)(v :: World) where

data VarOp (n :: Nat)(m :: Nat)(v :: World)(w :: World) where
  IdVO :: VarOp n n v v
  Weak :: VarOp n m v w -> VarOp (Suc n) (Suc m) v w
  Inst :: VarOp n Zero v w -> Hd Zero w -> VarOp (Suc n) Zero v w
  Abst :: VarOp Zero m u w -> Extended u v -> VarOp Zero (Suc m) v w

thicken :: Extended u v -> Ref v -> Maybe (Ref u)
thicken = _

class VarOperable (i :: Nat -> World -> *) where
  varOp :: VarOp n m v w -> i n v -> i m w
  closed :: i Zero w -> i m w
  closed = unsafeCoerce

instance VarOperable En where
  varOp f (hd :$ tl) = varOp f hd :$ fmap (varOp f) tl

instance VarOperable Hd where
  varOp f        (tm ::: ty)  = varOp f tm ::: varOp f ty
  varOp f        (V i) = either closed V (help f i) where
    help :: VarOp n m v w -> Fin n -> Either (Hd Zero w) (Fin m)
    help IdVO       i        = Right i
    help (Weak f)   FZero    = Right FZero
    help (Weak f)   (FSuc i) = fmap FSuc (help f i)
    help (Inst f h) FZero    = Left h
    help (Inst f h) (FSuc i) = help f i
    help (Abst f x) i        = absurd i 
  varOp f (P x) = either closed V (help f x) where
    help :: forall n m v w . VarOp n m v w -> Ref v -> Either (Hd Zero w) (Fin m)
    help IdVO       r = Left (P r)
    help (Weak f)   r = fmap FSuc (help f r)
    help (Inst f h) r = help f r
    help (Abst f x) r = maybe (Right FZero) (fmap FSuc . help f) (thicken x r)
instance VarOperable Tm where
  varOp f (En e)   = En (varOp f e)
  varOp f Set      = Set
  varOp f (Pi s t) = Pi (varOp f s) (varOp (Weak f) t)
  varOp f (Lam t)  = Lam (varOp (Weak f) t)
{-    
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
-- -}

--{-# OPTIONS -Wall -fwarn-incomplete-patterns #-}
{-# LANGUAGE KindSignatures, DataKinds, ScopedTypeVariables, PolyKinds, UndecidableInstances,
             MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances,
             GADTs, DeriveFunctor, RankNTypes, EmptyCase, TypeFamilies #-}
module Start where

import Data.Proxy
import Unsafe.Coerce

data World = W0 | Bind World

class Worldly (w :: World) where
  next :: Proxy w -> Int

instance Worldly W0 where
  next _ = 0

instance Worldly w => Worldly (Bind w) where
  next (_ :: Proxy (Bind w)) = next (Proxy :: Proxy w) + 1

data Nat = Zero | Suc Nat

data Ref w = Ref {refname :: Int , reftype :: TYPE w}
-- export only projection reftype and eq instance defined on ints only

instance Eq (Ref w) where
  Ref i _ == Ref j _ = i == j

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
  EBind :: Ref (Bind u) -> Extended u (Bind u)

extrRef :: Extended u v -> Ref v
extrRef (EBind r) = r

extend :: forall w . Worldly w => TYPE w -> Extended w (Bind w)
extend ty = EBind (Ref (next (Proxy :: Proxy w)) (wk ty))

data VarOp (n :: Nat)(m :: Nat)(v :: World)(w :: World) where
  IdVO :: VarOp n n v v
  Weak :: VarOp n m v w -> VarOp (Suc n) (Suc m) v w
  Inst :: VarOp n Zero v w -> Hd Zero w -> VarOp (Suc n) Zero v w
  Abst :: VarOp Zero m u w -> Extended u v -> VarOp Zero (Suc m) v w

thicken :: Extended u v -> Ref v -> Maybe (Ref u)
thicken (EBind x) y | x == y    = Nothing
                    | otherwise = Just $ unsafeCoerce y

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

class Dischargable (f :: World -> *)(g :: World -> *) | g -> f , f -> g where
  discharge :: Extended u v -> f v -> g u

instance Dischargable (Tm Zero) (Tm (Suc Zero)) where
  discharge x = varOp (Abst IdVO x) 

type family EQ x y where
  EQ x x = True
  EQ x y = False

type family OR x y where
  OR True y = True
  OR x True = True
  OR False y = y
  OR x False = x

type family WorldLT (w :: World)(w' :: World) :: Bool where
  WorldLT w (Bind w') = WorldLE w w'
  WorldLT w w'        = False

type family WorldLE (w :: World)(w' :: World) :: Bool where
  WorldLE w w' = OR (EQ w w') (WorldLT w w')

(!-) :: (Worldly w , Dischargable f g) =>
        TYPE w -> (forall w' . WorldLE w w' ~ True => En Zero w' -> Maybe (f w')) ->
        Maybe (g w)
ty !- f = fmap (discharge x) (f e) where
  x = extend ty
  e = P (extrRef x) :$ B0

wk :: (VarOperable i, WorldLE w w' ~ True) => i n w -> i n w'
wk = unsafeCoerce
  
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

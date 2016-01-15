{-# LANGUAGE KindSignatures, GADTs, DataKinds, StandaloneDeriving #-}
module NoFreeOpen where

import Utils
import Check

data Env :: Nat -> Nat -> * where
  E0 :: Env m Zero 
  ES :: Env m n -> Val m -> Env m (Suc n)

deriving instance Show (Env m n)

data VEn (n :: Nat) where
  (:$$) :: Fin n -> Bwd (Val n) -> VEn n
  deriving Show
  
data Val (n :: Nat) where
  VEn  :: VEn n -> Val n
  VSet :: Val n
  VPi  :: Val n -> Scope n -> Val n
  VLam :: Scope n -> Val n
  deriving Show

data Scope (m :: Nat) where
  Scope :: Env m n -> Tm (Suc n) -> Scope m

deriving instance Show (Scope n)

vapp :: Val n -> Val n -> Val n 
vapp (VLam (Scope g t)) v = eval t (ES g v)
vapp (i :$$ vs)         v = i :$$ (vs :< v)
class Eval (t :: Nat -> *) where
 eval :: t n -> Env m n -> Val m
 
instance Eval Fin where
  eval FZero    (ES _ v) = v
  eval (FSuc i) (ES g _) = eval i g

instance Eval Hd where
 eval (V i)      g = eval i g
 eval (t ::: ty) g = eval t g

instance Eval En where
 eval (hd :$ B0)        g = eval hd g
 eval (hd :$ (ts :< t)) g = vapp (eval (hd :$ ts) g) (eval t g)

instance Eval Tm where
 eval (En e)   g = eval e g
 eval Set      g = VSet
 eval (Pi s t) g = VPi (eval s g) (Scope g t)
 eval (Lam t)  g = VLam (Scope g t)

wk :: Val n -> Val (Suc n)
wk = _

quote :: Val n -> Tm n
quote VSet      = Set
quote (VPi s t) = Pi (quote VSet s) _
quote (Lam t)   = 

-- do I need this?
enquote :: VEn n -> Tm n
enquote (i :$$ vs) = En (V i) (bmap quote vs)
           

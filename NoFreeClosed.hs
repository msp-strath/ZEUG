{-# LANGUAGE KindSignatures, GADTs, DataKinds, StandaloneDeriving #-}
module NoFreeClosed where

import Utils
import Check

-- closed semantics

data Env (n :: Nat) where
  E0 :: Env Zero
  ES :: Env n -> Val -> Env (Suc n)

deriving instance Show (Env n)

data Val where
  VSet :: Val
  VPi :: Val -> Scope -> Val
  VLam :: Scope -> Val
  deriving Show

data Scope where
  Scope :: Env n -> Tm (Suc n) -> Scope

deriving instance Show Scope

vapp :: Val -> Val -> Val
vapp (VLam (Scope g t)) v = eval t (ES g v)

class Eval (t :: Nat -> *) where
 eval :: t n -> Env n -> Val
 
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

test :: Val
test = eval (En (Lam (En (V FZero :$ B0)) ::: Pi Set Set
                :$ (B0 :< En (V FZero :$ B0))))
            (ES E0 VSet)

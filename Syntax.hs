{-# LANGUAGE RankNTypes, DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, PolyKinds, UndecidableInstances,
             FlexibleInstances, ScopedTypeVariables #-}
module Syntax(
  World(),
  Worldly,
  Happy(..),
  Ref(reftype), -- not exporting refname
  Extended(),
  extrRef,
  extend,
  En(..),
  Tm(..),
  wk,
  (!-),
  (//),
  ) where
import Utils
import Unsafe.Coerce
import Data.Proxy
import Data.Maybe

-- contexts of free variables
data World = W0 | Bind World

-- currently unneeded hack:
newtype Fink (n :: Nat)(w :: World) = Fink {fink :: Fin n}

-- world relative unit type
data Happy :: World -> * where
  Happy :: Happy w

-- syntax indexed by contexts of bound and free variables

data En (n :: Nat)(w :: World) where
  V     :: Fin n -> En n w
  P     :: Ref w -> En n w
  (:$)  :: En n w -> Tm n w -> En n w
  (:::) :: Tm n w -> Tm n w -> En n w -- type annotations


data Tm (n :: Nat)(w :: World) where
  -- canonical things
  Set :: Tm n w
  Pi  :: Tm n w -> Tm (Suc n) w -> Tm n w
  Lam :: Tm (Suc n) w -> Tm n w
  -- elimination forms
  En  :: En n w -> Tm n w

-- free variable management

class Worldly (w :: World) where
  next :: Proxy w -> Int 

instance Worldly W0 where
  next _ = 0

instance Worldly w => Worldly (Bind w) where
  next (_ :: Proxy (Bind w)) = next (Proxy :: Proxy w) + 1

data Ref w = Ref {refname :: Int , reftype :: Val w}
-- export only projection reftype and eq instance defined on ints only

instance Eq (Ref w) where
  Ref i _ == Ref j _ = i == j

data Extended :: World -> World -> * where
  EBind :: Ref (Bind u) -> Extended u (Bind u)
  -- one-step extension of u = G ; x : S |- G

-- we don't make fresh variables we make fresh context extensions
extend :: forall w . Worldly w => Val w -> Extended w (Bind w)
extend ty = EBind (Ref (next (Proxy :: Proxy w)) (wk ty))

-- what is the new thing?
extrRef :: Extended u v -> Ref v
extrRef (EBind r) = r

-- are you the new thing or one of the old things?
thicken :: Extended u v -> Ref v -> Maybe (Ref u)
thicken (EBind x) y | x == y    = Nothing
                    | otherwise = Just $ unsafeCoerce y
-- if G ; x : S |- y : S /\ x /= y then G |- y : S

class VarOperable (i :: Nat -> World -> *) where
  varOp :: VarOp n m v w -> i n v -> i m w -- map
  vclosed :: i Zero w -> i m w
  vclosed = unsafeCoerce
  -- vclosed things can trivially weakened
  
data VarOp (n :: Nat)(m :: Nat)(v :: World)(w :: World) where
  IdVO :: WorldLE v w ~ True => VarOp n n v w
  Weak :: VarOp n m v w -> VarOp (Suc n) (Suc m) v w
  Inst :: VarOp n Zero v w -> En Zero w -> VarOp (Suc n) Zero v w
  -- instantiates bound index 0 with a valid neutral term
  Abst :: VarOp Zero m u w -> Extended u v -> VarOp Zero (Suc m) v w
  -- turns the free variable introduced by the extension into a bound
  -- variable

instance VarOperable En where
  varOp f        (tm ::: ty)  = varOp f tm ::: varOp f ty
  varOp f        (V i) = either vclosed V (help f i) where
    help :: VarOp n m v w -> Fin n -> Either (En Zero w) (Fin m)
    help IdVO       i        = Right i
    help (Weak f)   FZero    = Right FZero
    help (Weak f)   (FSuc i) = fmap FSuc (help f i)
    help (Inst f h) FZero    = Left h
    help (Inst f h) (FSuc i) = help f i
    help (Abst f x) i        = absurd i
      -- would have a boundvariable in empty context

  varOp f (P x) = either vclosed V (help f x) where
    help :: forall n m v w . VarOp n m v w -> Ref v ->
            Either (En Zero w) (Fin m)
    help IdVO       r = Left (wk (P r))
    help (Weak f)   r = fmap FSuc (help f r)
    help (Inst f h) r = help f r
    help (Abst f x) r =
      maybe (Right FZero) (fmap FSuc . help f) (thicken x r)
      -- either we have found the right one, or we can run  f on an
      -- old one
  varOp f (hd :$ tl) = varOp f hd :$ varOp f tl
  
instance VarOperable Tm where
  varOp f (En e)   = En (varOp f e)
  varOp f Set      = Set
  varOp f (Pi s t) = Pi (varOp f s) (varOp (Weak f) t)
  varOp f (Lam t)  = Lam (varOp (Weak f) t)

-- how to yank something that's constructed under a binder back out
-- from under that binder turning the free variable into a de Bruijn variable
class Dischargable (f :: World -> *)(g :: World -> *)
  | g -> f , f -> g where
  discharge :: Extended u v -> f v -> g u

instance Dischargable (Tm Zero) (Tm (Suc Zero)) where
  discharge x = varOp (Abst IdVO x)

instance Dischargable Happy Happy where
  discharge _ Happy = Happy -- :)

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

-- this doesn't need to be in this module as it uses extend and extrRef
(!-) :: (Worldly w , Dischargable f g) =>
        Val w -> (forall w' . (Worldly w', WorldLE w w' ~ True) =>
                   Ref w' -> f w') -> g w
ty !- f = discharge x (f e) where
  x = extend ty
  e = extrRef x

(//) :: (WorldLE w w' ~ True, VarOperable t) =>
        t One w -> En Zero w' -> t Zero w'
body // x = varOp (Inst IdVO x) body

class Weakenable (t :: World -> *) where
  wk :: WorldLE w w' ~ True => t w -> t w'
  wk = unsafeCoerce

instance Weakenable Val

instance Weakenable Ne

instance Weakenable Scope

instance Weakenable (Tm n)

instance Weakenable (En n)

-- evaluation
data Env :: Nat -> World -> * where
  E0 :: Env Zero w
  ES :: Env n w -> Val w -> Env (Suc n) w

data Ne :: World -> * where
  NP    :: Ref w -> Ne w
  (:$$) :: Ne w -> Val w -> Ne w
  
data Val :: World -> * where
  Ne    :: Ne w -> Val w
  VSet  :: Val w
  VPi   :: Val w -> Scope w -> Val w
  VLam  :: Scope w -> Val w

data Scope :: World -> * where
  Scope :: Env n w -> Tm (Suc n) w -> Scope w

($/) :: Scope w -> Val w -> Val w
Scope g t $/ v = eval t (ES g v)

($$) :: Val w -> Val w -> Val w
VLam s $$ v = s $/ v
Ne n   $$ v = Ne (n :$$ v)

elookup :: Fin n -> Env n w -> Val w
elookup FZero    (ES g v) = v
elookup (FSuc i) (ES g v) = elookup i g

class Eval t  where
  eval :: t n w -> Env n w -> Val w

instance Eval En where
  eval (V x)      g = elookup x g
  eval (P x)      g = Ne (NP x)
  eval (t ::: ty) g = eval t g
  eval (f :$ s)   g = eval f g $$ eval s g

instance Eval Tm where
  eval (En e)          g = eval e g
  eval Set             g = VSet
  eval (Pi sty tty)    g = VPi (eval sty g) (Scope g tty)
  eval (Lam t)         g = VLam (Scope g t)

etaquote :: Worldly w => Val w -> Val w -> Tm Zero w
etaquote VSet          VSet          = Set
etaquote VSet          (VPi dom cod) =
  Pi (etaquote VSet dom) $ dom !- \ x -> etaquote VSet (wk cod $/ Ne (NP x))
etaquote (VPi dom cod) f             = 
  Lam $ dom !- \ x -> let vx = Ne (NP x) in etaquote (wk cod $/ vx) (wk f $$ vx)
etaquote _            (Ne e) = En $ fst (netaquote e)

netaquote :: Worldly w => Ne w -> (En Zero w, Val w)
netaquote (NP x)    = (P x, reftype x)
netaquote (f :$$ s) = case netaquote f of
  (f', VPi dom cod) -> (f' :$ etaquote dom s, cod $/ s)

idE :: Env n w
idE = undefined

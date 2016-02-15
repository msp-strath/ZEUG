{-# LANGUAGE RankNTypes, DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, PolyKinds, UndecidableInstances,
             FlexibleInstances, ScopedTypeVariables, StandaloneDeriving,
             PatternSynonyms, TypeOperators, ConstraintKinds #-}
module Syntax(
  World(..),
  Worldly,
  Happy(..),
  RefBinder(..),
  Ref(refType), -- not exporting refName
  Extended(),
  extwk,
  extrRef,
  extend,
  En(..),
  Tm(..),
  Global(..),
  KStep(..),
  wk,
  Dischargeable(..),
  TERM,
  ELIM,
  Phase(..),
  Env(..),
  Kind(..),
  (!-),
  (//),
  eval,
  val,
  Val(..),
  Ne(..),
  ($$),
  pattern Pi,pattern Sg,pattern Set,pattern Fst, pattern Snd,
  vfst,
  vsnd,
  ($/),
  etaquote,
  Weakenable,
  type (<=),
  VarOperable(..),
  VarOp(..),
  LongName,
  ($$$)
  ) where
import Utils
import Unsafe.Coerce
import Data.Proxy
import Data.Maybe

type TERM = Tm (Syn Zero)
type ELIM = En (Syn Zero)

-- contexts of free variables
data World = W0 | Bind World

-- syntax indexed by contexts of bound and free variables

data Phase = Syn Nat | Sem

data En (p :: Phase)(w :: World) where
  -- bound variable
  V     :: Fin n -> En (Syn n) w
  -- free variable
  P     :: Ref w -> En p w
  -- application
  (:$)  :: En p w -> Tm p w -> En p w
  -- definition instance
  (:%)  :: Global n -> Env p n w -> En p w
  -- type annotation
  (:::) :: Tm (Syn n) w -> Tm (Syn n) w -> En (Syn n) w

data Tm (p :: Phase)(w :: World) where
  Let  :: En (Syn n) w -> Tm (Syn (Suc n)) w -> Tm (Syn n) w
  -- building blocks
  Atom :: String -> Tm p w
  (:&) :: Tm p w -> Tm p w -> Tm p w
  Lam  :: Body p w -> Tm p w
  -- elimination forms
  En   :: En p w -> Tm p w

-- iterated application
($$$) :: En p w -> [Tm p w] -> En p w
e $$$ xs = foldl (:$) e xs

instance Eq (En (Syn n) w) where
  V x == V y = x == y
  P x == P y = x == y
  (e :$ s) == (e' :$ s') = e == e' && s == s'
  (x :% g) == (x' :% g') = globHetEq x x' && envHetEq g g'
  (t ::: ty) == (t' ::: ty') = ty == ty' && t == t'

--deriving instance Show (En (Syn n) w)

-- hopefully won't need this in a ghc > 8
instance Show (En (Syn m) n) where
  show (P x) = "P " ++ show x
  show (t :$ s) = "(:$) (" ++ show t ++ ") (" ++ show s ++ ")"
  show (glob :% g) = "(:%) " ++ show (globName glob) ++ " " ++ show g

instance Eq (Tm (Syn n) w) where
  Let e t  == Let e' t'  = e == e' && t == t'
  Atom s   == Atom s'    = s == s'
  (t :& s) == (t' :& s') = t == t' && s == s' 
  Lam t    == Lam t'     = t == t'
  En e     == En e'      = e == e'

deriving instance Show (Tm (Syn n) w)
--deriving instance Show (Tm Sem w)

infixr 4 :&

type Val = Tm Sem
type Ne  = En Sem

type family Body (p :: Phase) ::  World -> * where
  Body (Syn n) = Tm (Syn (Suc n))
  Body Sem     = Scope

-- a closed closure
data Scope :: World -> * where
  Scope :: Env Sem n w -> Tm (Syn (Suc n)) w -> Scope w

--deriving instance Show (Scope w)

-- world indexed vectors would also do...
data Env :: Phase -> Nat -> World -> * where
  E0 :: Env p Zero w
  ES :: Env p n w -> Tm p w -> Env p (Suc n) w

deriving instance Show (Env (Syn m) n w)

emap :: (Tm p w -> Tm p' w') -> Env p n w -> Env p' n w'
emap f E0 = E0
emap f (ES g t) = ES (emap f g) (f t)

instance Eq (Env (Syn m) n w) where 
  g == g' = envHetEq g g'

envHetEq :: Env (Syn m) n w -> Env (Syn m) n' w -> Bool
envHetEq E0       E0         = True
envHetEq (ES g t) (ES g' t') = envHetEq g g' && t == t'
envHetEq _        _          = False

--deriving instance Show (Env p n w)

-- canonical things
pattern Nil = Atom ""
pattern Set = Atom "Set"
-- Pi, Sg :: Tm p w -> Body p w -> Tm p w
pattern Pi s t = Atom "Pi" :& s :& Lam t :& Nil
pattern Sg s t = Atom "Sg" :& s :& Lam t :& Nil

-- elimination forms
pattern Fst p = p :$ Atom "Fst"
pattern Snd p = p :$ Atom "Snd"

-- framework kinds
data KStep (m :: Nat) (n :: Nat) where
  KS :: Tm (Syn m) W0 -> KStep m (Suc m)

data Kind (n :: Nat) where
  (:=>) :: LStar KStep Zero n -> Tm (Syn n) W0 -> Kind n

-- global definitions
data Global (n :: Nat) = Glob
  {  globName :: LongName
  ,  globKind :: Kind n
  ,  globDefn :: Maybe (Tm (Syn n) W0)
  }

type LongName = [Int]
instance Eq (Global n) where
  x == y = globHetEq x y

globHetEq ::Global n -> Global n' -> Bool
globHetEq x y = globName x == globName y
-- free variable management
type Name = Int

class WorldLE W0 w ~ True => Worldly (w :: World) where
  next :: Proxy w -> Name

instance Worldly W0 where
  next _ = 0

instance Worldly w => Worldly (Bind w) where
  next (_ :: Proxy (Bind w)) = 1 + next (Proxy :: Proxy w)

data RefBinder w = Decl | Local (Val w)

data Ref w = Ref {refBinder :: RefBinder w, refName :: Name, refType :: Val w}
-- export only projection refType and eq instance defined on ints only

instance Show (Ref w) where
  show = show . refName

instance Eq (Ref w) where
  i == j = refName i == refName j

data Extended :: World -> World -> * where
  EBind :: Ref (Bind u) -> Extended u (Bind u)
  -- one-step extension of u = G ; x : S |- G

extwk :: Weakenable t => Extended u v -> t u -> t v
extwk (EBind r) = wk

-- we don't make fresh variables we make fresh context extensions
extend :: forall w . Worldly w => (RefBinder w, Val w) -> Extended w (Bind w)
extend (rb, ty) = EBind (Ref (wk rb) (next (Proxy :: Proxy w)) (wk ty))

-- what is the new thing?
extrRef :: Extended u v -> Ref v
extrRef (EBind r) = r

-- are you the new thing or one of the old things?
thicken :: Extended u v -> Ref v -> Maybe (Ref u)
thicken (EBind x) y | x == y    = Nothing
                    | otherwise = Just $ unsafeCoerce y
-- if G ; x : S |- y : S /\ x /= y then G |- y : S

class VarOperable (i :: Phase -> World -> *) where
  varOp :: VarOp n m v w -> i (Syn n) v -> i (Syn m) w -- map
  vclosed :: i (Syn Zero) w -> i (Syn m) w
  vclosed = unsafeCoerce
  -- vclosed things can trivially weakened
  
data VarOp (n :: Nat)(m :: Nat)(v :: World)(w :: World) where
  IdVO :: WorldLE v w ~ True => VarOp n n v w
  Weak :: VarOp n m v w -> VarOp (Suc n) (Suc m) v w
  Inst :: VarOp n Zero v w -> En (Syn Zero) w -> VarOp (Suc n) Zero v w
  -- instantiates bound index 0 with a valid neutral term
  Abst :: VarOp Zero m u w -> Extended u v -> VarOp Zero (Suc m) v w
  -- turns the free variable introduced by the extension into a bound
  -- variable

instance VarOperable En where
  varOp f        (tm ::: ty)  = varOp f tm ::: varOp f ty
  varOp f        (V i) = either vclosed V (help f i) where
    help :: VarOp n m v w -> Fin n -> Either (En (Syn Zero) w) (Fin m)
    help IdVO       i        = Right i
    help (Weak f)   FZero    = Right FZero
    help (Weak f)   (FSuc i) = fmap FSuc (help f i)
    help (Inst f h) FZero    = Left h
    help (Inst f h) (FSuc i) = help f i
    help (Abst f x) i        = absurd i
      -- would have a boundvariable in empty context

  varOp f (P x) = either vclosed V (help f x) where
    help :: forall n m v w . VarOp n m v w -> Ref v ->
            Either (En (Syn Zero) w) (Fin m)
    help IdVO       r = Left (wk (P r))
    help (Weak f)   r = fmap FSuc (help f r)
    help (Inst f h) r = help f r
    help (Abst f x) r =
      maybe (Right FZero) (fmap FSuc . help f) (thicken x r)
      -- either we have found the right one, or we can run  f on an
      -- old one
  varOp f (hd :$ tl)  = varOp f hd :$ varOp f tl
  varOp f (glob :% g) = glob :% emap (varOp f) g

instance VarOperable Tm where
  varOp f (Let e t) = Let (varOp f e) (varOp (Weak f) t)
  varOp f (En e)    = En (varOp f e)
  varOp f (Atom s)  = Atom s
  varOp f (t :& u)  = (varOp f t :& varOp f u)
  varOp f (Lam t)   = Lam (varOp (Weak f) t)

-- how to yank something that's constructed under a binder back out
-- from under that binder turning the free variable into a de Bruijn variable
class Dischargeable (f :: World -> *)(g :: World -> *)
  | g -> f , f -> g where
  discharge :: Extended u v -> f v -> g u

instance Dischargeable (Tm (Syn Zero)) (Tm (Syn One)) where
  discharge x = varOp (Abst IdVO x)

instance Dischargeable Happy Happy where
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
  WorldLT w (Bind w')  = WorldLE w w'
  WorldLT w w'         = False

type family WorldLE (w :: World)(w' :: World) :: Bool where
  WorldLE w w' = OR (EQ w w') (WorldLT w w')

type u <= v = WorldLE u v ~ True

class RefEmbeddable t where
  emb :: Ref w -> t w

instance RefEmbeddable Ref where
  emb = id

instance RefEmbeddable (En p) where
  emb = P

instance RefEmbeddable (Tm p) where
  emb = En . emb

-- this doesn't need to be in this module as it uses extend and extrRef
(!-) :: (Worldly w , Dischargeable f g) =>
        (RefBinder w, Val w) -> (forall w' . (Worldly w', WorldLE w w' ~ True) =>
                   (forall r . RefEmbeddable r => r w') -> f w') -> g w
p !- f = discharge x (f (emb (extrRef x))) where
  x = extend p

(//) :: (WorldLE w w' ~ True, VarOperable t) =>
        t (Syn One) w -> En (Syn Zero) w' -> t (Syn Zero) w'
body // x = varOp (Inst IdVO x) body

class Weakenable (t :: World -> *) where
  wk :: WorldLE w w' ~ True => t w -> t w'
  wk = unsafeCoerce

instance Weakenable Scope

instance Weakenable (Tm p)

instance Weakenable (En p)

instance Weakenable (RefBinder)

instance Weakenable Ref

($/) :: Worldly w => Scope w -> Val w -> Val w
Scope g t $/ v = eval t (ES g v)

($$) :: Worldly w => Val w -> Val w -> Val w
En n     $$ v          = En (n :$ v)
Lam s    $$ v          = s $/ v
(v :& w) $$ Atom "Fst" = v
(v :& w) $$ Atom "Snd" = w

vfst, vsnd :: Worldly w => Val w -> Val w
vfst p = p $$ Atom "Fst"
vsnd p = p $$ Atom "Snd"

elookup :: Fin n -> Env p n w -> Tm p w
elookup FZero    (ES g v) = v
elookup (FSuc i) (ES g v) = elookup i g

class Eval t  where
  eval :: Worldly w => t (Syn n) w -> Env Sem n w -> Val w

instance Eval En where
  eval (V x)      g = elookup x g
  eval (P x)      g | Local v <- refBinder x = v
                    | otherwise             = En (P x)
  eval (t ::: ty) g = eval t g
  eval (f :$ s)   g = eval f g $$ eval s g
  eval (glob :% g')    g = case globDefn glob of
    Nothing -> En (glob :% newg')
    Just t  -> eval (wk t) newg'
    where
    newg' = emap (\ t -> eval t g) g'
  
instance Eval Tm where
  eval (Let e t)       g = eval t (ES g (eval e g))
  eval (En e)          g = eval e g
  eval (Atom s)        g = Atom s
  eval (t :& u)        g = eval t g :& eval u g  
  eval (Lam t)         g = Lam (Scope g t)
  
val :: Worldly w => Eval t => t (Syn Zero) w -> Val w
val t = eval t E0

etaquote :: Worldly w => Val w -> Val w -> Tm (Syn Zero) w
etaquote Set          Set          = Set
etaquote Set          (Pi dom cod) =
  Pi (etaquote Set dom) $ (Decl,dom) !- \ x -> etaquote Set (wk cod $/ x)
etaquote Set          (Sg dom cod) =
  Sg (etaquote Set dom) $ (Decl,dom) !- \ x -> etaquote Set (wk cod $/ x)
etaquote (Pi dom cod) f             = 
  Lam $ (Decl,dom) !- \ x -> etaquote (wk cod $/ x) (wk f $$ x)
etaquote (Sg dom cod) p             = let s = vfst p in
  etaquote dom s :& etaquote (cod $/ s) (vsnd p)
etaquote _            (En e) = En $ fst (netaquote e)

netaquote :: Worldly w => Ne w -> (En (Syn Zero) w, Val w)
netaquote (P x)    = (P x, refType x)
netaquote (e :$ s) = case netaquote e of
  (f', Pi dom cod) -> (f' :$ etaquote dom s, cod $/ s)
  (p', Sg dom cod) -> case s of
    Atom "Fst" -> (Fst p', dom)
    Atom "Snd" -> (Snd p', cod $/ En (Fst e))
netaquote (glob :% g) = case globKind glob of
  del :=> t -> (glob :% help del g, eval (wk t) g)
  where
    help :: Worldly w => LStar KStep Zero n -> Env Sem n w -> Env (Syn Zero) n w
    help L0 E0 = E0
    help (del :<: KS s) (ES gamma v) =
      ES (help del gamma) (etaquote (eval (wk s) gamma) v)
   
instance Worldly w => Eq (Ne w) where
  n == n' = fst (netaquote n) == fst (netaquote n')


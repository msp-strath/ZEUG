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
--  vfst,
--  vsnd,
  ($/),
--  etaquote,
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

-- contexts of free variables
data World = W0 | Bind World

data Phase = Syn Nat | Sem

pattern Type = Atom "Type"
pattern El t = Atom "El" :& t 

type TERM = Tm (Syn Zero)
type ELIM = En (Syn Zero)
type Val = Tm Sem
type Kind = Val
type Ne  = En Sem
data THING w =  (::::) {valOf :: Val w, kindOf :: Kind w}

-- syntax indexed by contexts of bound and free variables
data En (p :: Phase)(w :: World) where
  -- bound variable
  V     :: Fin n -> En (Syn n) w
  -- free variable
  P     :: Ref w -> En p w
  -- application
  (:$)  :: En p w -> Tm p w -> En p w
  -- definition instance
  (:%)  :: Global n -> Env (Tm p) n w -> En p w
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
  V x        == V y          = x == y
  P x        == P y          = x == y
  (e :$ s)   == (e' :$ s')   = e == e' && s == s'
  (x :% g)   == (x' :% g')   = globHetEq x x' && envHetEq g g'
  (t ::: ty) == (t' ::: ty') = ty == ty' && t == t'

-- deriving instance Show (En (Syn n) w)
-- hopefully won't need this in a ghc > 8
instance Show (En (Syn m) n) where
  show (V i)       = "V " ++ show i
  show (P x)       = "P " ++ show x
  show (t :$ s)    = "(:$) (" ++ show t ++ ") (" ++ show s ++ ")"
  show (glob :% g) = "(:%) " ++ show (globName glob) ++ " " ++ show g

deriving instance Eq (Tm (Syn n) w)

deriving instance Show (Tm (Syn n) w)

infixr 4 :&

type family Body (p :: Phase) ::  World -> * where
  Body (Syn n) = Tm (Syn (Suc n))
  Body Sem     = Scope

-- a closed closure
data Scope :: World -> * where
  Scope :: Env THING n w -> Tm (Syn (Suc n)) w -> Scope w

-- world indexed vectors would also do...
data Env :: (World -> *) -> Nat -> World -> * where
  E0 :: Env t Zero w
  ES :: Env t n w -> t w -> Env t (Suc n) w

deriving instance Show (Env (Tm (Syn m)) n w)

emap :: (t w -> t' w') -> Env t n w -> Env t' n w'
emap f E0 = E0
emap f (ES g t) = ES (emap f g) (f t)

instance Eq (Env (Tm (Syn m)) n w) where 
  g == g' = envHetEq g g'

envHetEq :: Env (Tm (Syn m)) n w -> Env (Tm (Syn m)) n' w -> Bool
envHetEq E0       E0         = True
envHetEq (ES g t) (ES g' t') = envHetEq g g' && t == t'
envHetEq _        _          = False

-- canonical things
pattern Nil = Atom ""
pattern Set = Atom "Set"
-- Pi, Sg :: Tm p w -> Body p w -> Tm p w
pattern Pi s t = Atom "Pi" :& s :& Lam t :& Nil
pattern Sg s t = Atom "Sg" :& s :& Lam t :& Nil

-- elimination forms
pattern Fst = Atom "Fst"
pattern Snd = Atom "Snd"

-- framework kinds
data KStep (m :: Nat) (n :: Nat) where
   KS :: Tm (Syn m) W0 -> KStep m (Suc m)

data Arity (n :: Nat) where
  (:=>) :: LStar KStep Zero n -> Tm (Syn n) W0 -> Arity n

-- global definitions
data Global (n :: Nat) = Glob
  {  globName :: LongName
  ,  globArity :: Arity n
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
      -- either we have found the right one, or we can run f on an
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

instance RefEmbeddable THING where
  emb x = (:::: refType x) $ case refBinder x of
    Local v -> v
    _       -> En (P x)

instance RefEmbeddable (En p) where
  emb = P

instance RefEmbeddable (Tm p) where
  emb = En . emb

(!-) :: (Worldly w , Dischargeable f g) 
     => (RefBinder w, Val w) 
     -> (forall w' . (Worldly w', WorldLE w w' ~ True) =>
           (forall r . RefEmbeddable r => r w') -> f w') 
     -> g w
p !- f = discharge x (f (emb (extrRef x))) where x = extend p

(//) :: (WorldLE w w' ~ True, VarOperable t) 
     => t (Syn One) w 
     -> En (Syn Zero) w' 
     -> t (Syn Zero) w'
body // x = varOp (Inst IdVO x) body

class Weakenable (t :: World -> *) where
  wk :: WorldLE w w' ~ True => t w -> t w'
  wk = unsafeCoerce

instance Weakenable THING

instance Weakenable Scope

instance Weakenable (Tm p)

instance Weakenable (En p)

instance Weakenable (RefBinder)

instance Weakenable Ref

($/) :: Worldly w => Scope w -> THING w -> Val w
Scope g t $/ v = eval t (ES g v)

($$) :: Worldly w => THING w -> Val w -> THING w
f $$ v = (f $: v) :::: (f $- v)

($:) :: Worldly w => THING w -> Val w -> Val w
(En n   :::: _ ) $: v = En (n :$ v)
(Lam s  :::: Pi dom cod ) $: v = s $/ (v :::: dom)
((v :& w) :::: _ ) $: Fst = v
((v :& w) :::: _ ) $: Snd = w

($-) :: Worldly w => THING w -> Val w -> Kind w
(_ :::: Pi dom cod)   $- v   = cod $/ (v :::: dom)
(_ :::: Sg dom cod)   $- Fst = dom
p@(_ :::: Sg dom cod) $- Snd = cod $/ (p $$ Fst)

elookup :: Fin n -> Env t n w -> t w
elookup FZero    (ES g v) = v
elookup (FSuc i) (ES g v) = elookup i g

class Eval t v  where
  eval :: Worldly w => t (Syn n) w -> Env THING n w -> v w

type family   (n :: Nat) :+ (m :: Nat) :: Nat
type instance Zero    :+ m = m
type instance (Suc n) :+ m = Suc (n :+ m)

instance Eval En THING where
  eval (V x)        g = elookup x g
  eval (P x)        g = emb x
  eval (t ::: ty)   g = eval t g :::: eval ty g
  eval (f :$ s)     g = eval f g $$ eval s g
  eval (glob :% g') g = case globDefn glob of
    Nothing -> En (glob :% emap valOf newg') :::: ty
    Just t  -> eval (wk t) newg' :::: ty
    where
    tele :=> tybody = globArity glob
    ty = eval (wk tybody) newg'
    newg' = instantiateTele tele (emap (\t -> eval t g) g')

instance Eval Tm Val where
  eval (Let e t) g = eval t (ES g (eval e g))
  eval (En e)    g = valOf $ eval e g
  eval (Atom s)  g = Atom s
  eval (t :& u)  g = eval t g :& eval u g  
  eval (Lam t)   g = Lam (Scope g t)
  
val :: Worldly w => Eval t v => t (Syn Zero) w -> v w
val t = eval t E0

instantiateTele :: Worldly w 
                => LStar KStep Zero n 
                -> Env (Tm Sem) n w 
                -> Env THING n w
instantiateTele L0 E0 = E0
instantiateTele (ks :<: KS ty) (ES g v) = 
  let vs = instantiateTele ks g in ES vs (v :::: eval (wk ty) vs)

etaquote :: Worldly w => THING w -> Tm (Syn Zero) w
etaquote (Set :::: Set) = Set
etaquote (Pi dom cod :::: Set) =
  Pi (etaquote (dom :::: Set)) $ (Decl,dom) !- \ x -> 
    etaquote ((wk cod $/ x) :::: Set)
etaquote (Sg dom cod :::: Set) =
  Sg (etaquote (dom :::: Set)) $ (Decl,dom) !- \ x -> 
    etaquote ((wk cod $/ x) :::: Set)
etaquote f@(_ :::: Pi dom cod) = 
  Lam $ (Decl,dom) !- \ x -> 
      etaquote (wk f $$ x)
etaquote p@(_ :::: Sg dom cod) = 
  etaquote (p $$ Fst) :& etaquote (p $$ Snd)
etaquote (En e :::: _) = En $ fst (netaquote e)

netaquote :: Worldly w => Ne w -> (En (Syn Zero) w, Val w)
netaquote (P x)       = (P x, refType x)
netaquote (e :$ s)    = case netaquote e of
  (f', Pi dom cod) -> (f' :$ etaquote (s :::: dom), cod $/ (s :::: dom))
  (p', Sg dom cod) -> case s of
    Atom "Fst" -> (p' :$ Fst, dom)
    Atom "Snd" -> (p' :$ Snd, cod $/ ((En e :::: Sg dom cod) $$ Fst))
netaquote (glob :% g) = case globArity glob of
  del :=> t -> let g' = instantiateTele del g in 
    (glob :% emap etaquote g', eval (wk t) g')

-- We deliberately don't have a syntactic/structural equality for Ne.
-- Also we don't have an Eq instance at all for Val as it is type directed.

instance Worldly w => Eq (Ne w) where
  n == n' = fst (netaquote n) == fst (netaquote n')

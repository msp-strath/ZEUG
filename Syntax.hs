{-# LANGUAGE RankNTypes, DataKinds, KindSignatures, GADTs,
             MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, PolyKinds, UndecidableInstances,
             FlexibleInstances, ScopedTypeVariables, StandaloneDeriving,
             PatternSynonyms, TypeOperators, ConstraintKinds, TupleSections #-}
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
  Act(..),
  pattern Kind,
  pattern Type,
  pattern El,
  pattern Set,
  pattern Level,
  pattern Ze,
  pattern Su,
  pattern Pi,
  pattern Sg,
  pattern Fst,
  pattern Snd,
  pattern Seg,
  pattern Point,
  pattern Lft,
  pattern Rht,
  pattern Dash,
  pattern Weld,
  pattern One,
  pattern Path,
  pattern At,
  Arity(..),
  etaquote,
  Weakenable,
  type (<=),
  VarOperable(..),
  VarOp(..),
  LongName,
  THING(..),
  refThing,
  emap,
  kEq,
  Scope(..),
  ) where

import Utils
import Unsafe.Coerce
import Data.Proxy
import Data.Maybe
import Prelude hiding ((/))

-- contexts of free variables
data World = W0 | Bind World

-- world indexed stuff
data W5Tuple f (w :: World) = W5Tuple (f w, f w, f w, f w, f w)

data WMaybe (f :: World -> *)(w :: World) where
  WJust :: f w -> WMaybe f w
  WNothing :: WMaybe f w

data Phase = Syn Nat | Sem

pattern N = Atom ""
pattern Kind = Atom "Kind" :& N

pattern Type = Atom "Type" :& N
pattern El t = Atom "El" :& t :& N
pattern Level = Atom "Level" :& N
pattern Ze = Atom "zero" :& N
pattern Su n = Atom "suc" :& n :& N
pattern Set l = Atom "Set" :& l :& N

pattern Seg = Atom "Seg" :& N
pattern Dash = Atom "-" :& N
pattern Point s = Atom "Point" :& s :& N
pattern Weld sig _T tau = Atom "Weld" :& sig :& _T :& tau :& N
pattern Lft sig = Atom "Left" :& sig :& N
pattern Rht sig = Atom "Right" :& sig :& N
pattern One = Atom "one" :& N
pattern Op = Atom "Op" :& N
pattern Path _S sig _T = Atom "Path" :& _S :& sig :& _T :& N
pattern At p = Atom "@" :& p :& N
pattern Kink _S sig _T tau _U _P _Q =
  Atom "Kink" :& _S :& sig :& _T :& tau :& _U :& _P :& _Q :& N

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
  (:/)  :: En p w -> Tm p w -> En p w
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

instance Eq (En (Syn n) w) where
  V x        == V y          = x == y
  P x        == P y          = x == y
  (e :/ s)   == (e' :/ s')   = e == e' && s == s'
  (x :% g)   == (x' :% g')   = globHetEq x x' && envHetEq g g'
  (t ::: ty) == (t' ::: ty') = ty == ty' && t == t'

-- deriving instance Show (En (Syn n) w)
-- hopefully won't need this in a ghc > 8
instance Show (En (Syn m) n) where
  show (V i)       = "V " ++ show i
  show (P x)       = "P " ++ show x
  show (t :/ s)    = "(:/) (" ++ show t ++ ") (" ++ show s ++ ")"
  show (t ::: ty)  = "(:::) (" ++ show t ++ ") (" ++ show ty ++ ")"
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
  varOp f (hd :/ tl)  = varOp f hd :/ varOp f tl
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

instance Dischargeable f g => Dischargeable (W5Tuple f) (W5Tuple g) where
  discharge x (W5Tuple (f1,f2,f3,f4,f5)) =
    W5Tuple (discharge x f1,discharge x f2, discharge x f3,discharge x f4,discharge x f5)

instance Dischargeable f g => Dischargeable (WMaybe f) (WMaybe g) where
  discharge x (WJust f) = WJust (discharge x f)
  discharge x WNothing = WNothing

type family WorldLT (w :: World)(w' :: World) :: Bool where
  WorldLT w (Bind w') = WorldLE w w'
  WorldLT w w'        = False

type family WorldLE (w :: World)(w' :: World) :: Bool where
  WorldLE w w' = OR (EQ w w') (WorldLT w w')

type u <= v = WorldLE u v ~ True

refThing :: Ref w -> THING w
refThing x = (:::: refType x) $ case refBinder x of
  Local v -> v
  _       -> En (P x)

(!-) :: (Worldly w , Dischargeable f g)
     => (RefBinder w, Val w)
     -> (forall w' . (Worldly w', w <= w') => Ref w' -> f w')
     -> g w
p !- f = discharge x (f (extrRef x)) where x = extend p

class Weakenable (t :: World -> *) where
  wk :: WorldLE w w' ~ True => t w -> t w'
  wk = unsafeCoerce

instance Weakenable THING

instance Weakenable Scope

instance Weakenable (Tm p)

instance Weakenable (En p)

instance Weakenable (RefBinder)

instance Weakenable Ref

class Act f a t | f -> t where
  (/) :: f -> a -> t
infixl 8 /, //, /:

instance Worldly w => Act (THING w) (Val w) (THING w) where
  f / v = (f /- v) :::: (f /: v)

instance Worldly w => Act (THING w) String (THING w) where
  f / s = f / (Atom s :: Val w)

instance Worldly w => Act (THING w) (Ref w) (THING w) where
  f / x = f / (En (P x) :: Val w)

instance Worldly w => Act (En p w) [Tm p w] (En p w) where
  e / xs = foldl (:/) e xs

instance Worldly w => Act (Scope w) (THING w) (Val w) where
  Scope g t / v = eval t (ES g v)

instance Worldly w => Act (Scope w) (Ref w) (Val w) where
  s / x = s / refThing x

-- given a thing and an action on it, what kind of thing do you get back?
(/:) :: Worldly w => THING w -> Val w -> Kind w
(_   :::: El (Pi dom cod))     /: v   = El (cod / (v :::: El dom))
(_   :::: El (Sg dom cod))     /: Fst = El dom
p@(_ :::: El (Sg dom cod))     /: Snd = El (cod / (p /- Fst :::: El dom))
(_   :::: El (Path _S sig _T)) /: At p = Type
(_   :::: Point sig)           /: Op   = Point (invseg sig)
(_   :::: Point _)             /: path = Type
-- given a thing and an action on it, what value do you get back?
(/-) :: Worldly w => THING w -> Val w -> Val w
(Lam s    :::: El (Pi dom cod ))    /- v    = s / (v :::: El dom)
((v :& w) :::: _               )    /- Fst  = v
((v :& w) :::: _               )    /- Snd  = w

-- a point acts on a path
(_     :::: El path@(Path _S sig _T)) /- At p | Just _X <- canonPoint path p = _X
(Lam _M   :::: El (Path _S sig _T)) /- At p = _M / (p :::: Point sig)

-- inverting points
(Ze    :::: Point _                ) /- Op = One
(Lft p :::: Point (Weld sig _T tau)) /- Op = Rht ((p :::: Point sig) /- Op)
(Rht p :::: Point (Weld sig _T tau)) /- Op = Lft ((p :::: Point tau) /- Op)
(One   :::: Point _                ) /- Op = Ze
-- a path acts on a point
(Ze  :::: Point _) /-  Kink _S sig _T tau _U _P _Q = _S
(Lft p :::: Point _) /- Kink _S sig _T tau _U _P _Q =
  (_P :::: El (Path _S sig _T)) /- At p
(Rht p :::: Point _) /- Kink _S sig _T tau _U _P _Q =
  (_Q :::: El (Path _T sig _U)) /- At p
(One :::: Point _) /- Kink _S sig _T tau _U _P _Q = _U
(En (p :/ Op) :::: Point seg) /- Kink _S sig _T tau _U _P _Q = 
  (En p :::: Point (invseg seg)) /- Kink _U
                                      (invseg tau)
                                      _T
                                      (invseg sig)
                                      _S
                                      (flipPath (_P :::: El (Path _S sig _T)))
                                      (flipPath (_Q :::: El (Path _T tau _U)))
x@(p :::: Point _) /- y@(Kink _S sig _T tau _U _P _Q) | Just _X <- yankLeft x y = _X
x@(p :::: Point _) /- y@(Kink _S sig _T tau _U _P _Q) | Just _X <- yankRight x y = _X
x@(p :::: Point _) /- y@(Kink _S sig _T tau _U _P _Q) | Just _X <- shuffle x y = _X
(En n     :::: _               )    /- v    = En (n :/ v)

canonPoint :: Val w -> Val w -> Maybe (Val w)
canonPoint (Path _S sig _T) Ze  = Just _S
canonPoint (Path _S (Weld sig _M tau) _T) (Lft p) = canonPoint (Path _S sig _M) p
canonPoint (Path _S (Weld sig _M tau) _T) (Rht p) = canonPoint (Path _M tau _T) p
canonPoint (Path _S sig _T) One = Just _T
-- no case for Op as it would have already computed away if the point
-- was canonical

invseg :: Tm p w -> Tm p w
invseg Dash = Dash
invseg (Weld sig _M tau) = Weld (invseg tau) _M (invseg sig)

flipPath :: Worldly w => THING w -> Val w
flipPath p@(_P :::: El (Path _S sig _T)) =
  val $ Lam $ (Decl,Point Dash :: Val w) !- \ (i :: Ref w') -> etaquote (wk p / At ((refThing i /- Op) :: Val w'))

yankLeft :: Worldly w => THING w -> Val w -> Maybe (Val w)
yankLeft (p :::: (Point Dash :: Val w)) (Kink _S sig _T tau _U _P _Q) =
  case ((Decl,(Point Dash :: Val w)) !- \ i -> kEq' Type (wk _S) (wk (_P :::: El (Path _S sig _T)) /- At (En (P i)))) of
    Cheer -> Just $ (_Q :::: El (Path _T tau _U)) /- At p
    Fear  -> Nothing
yankLeft _ _ = Nothing -- not a dash seg

yankRight :: Worldly w => THING w -> Val w -> Maybe (Val w)
yankRight (p :::: (Point Dash :: Val w)) (Kink _S sig _T tau _U _P _Q) =
  case ((Decl,(Point Dash :: Val w)) !- \ i -> kEq' Type (wk (_Q :::: El (Path _T tau _U)) /- At (En (P i))) (wk _U)) of
    Cheer -> Just $ (_P :::: El (Path _S sig _T)) /- At p
    Fear  -> Nothing
yankRight _ _ = Nothing -- not a dash seg
  
shuffle :: Worldly w => THING w -> Val w -> Maybe (Val w)
shuffle thing@(p :::: (Point Dash :: Val w)) (Kink _S sig _T tau _U _P _Q) = case help thing of
  WJust (W5Tuple (sig0,_S',sig1,_P0,_P1)) -> Just $ thing /- Kink
    _S
    (val1 sig0)
    (val1 _S')
    (Weld (val1 sig1) _T tau)
    _U
    (val1 _P0)
    (val (Lam (En (V FZero :/ Kink
       _S'
       sig1
       (vclosed (etaquote (_T :::: Type)))
       (vclosed (etaquote (tau :::: Seg)))
       (vclosed (etaquote (_U :::: Type)))
       _P1
       (vclosed (etaquote (_Q :::: El (Path _T tau _U))))))))
  _ -> Nothing
  where
  val1 t = eval t (ES E0 thing)
  help :: Worldly w => THING w -> WMaybe (W5Tuple (Tm (Syn One))) w
  help p = 
     (Decl,Point Dash) !- \(i :: Ref w') -> case wk p /- At (En (P i) :: Val w') of
      En (P i :/ Kink _S sig0 _S' sig1 _T _P0 _P1) -> WJust $ W5Tuple
        (etaquote (sig0 :::: Seg),
         etaquote (_S' :::: Type),
         etaquote (sig1 :::: Seg),
         etaquote (_P0 :::: El (Path _S sig0 _S')),
         etaquote (_P1 :::: El (Path _S' sig1 _T)))
      _ -> WNothing

focusL :: Worldly w => THING w -> THING w
focusL (_P :::: El (Path _S (Weld sig0 _S' sig1) _T)) = val (Lam $ (Decl,Point sig0) !- \ (i :: Ref w') -> etaquote (wk (_P :::: El (Path _S (Weld sig0 _S' sig1) _T))  / At (Lft (En (P i) :: Val w')))) :::: El (Path _S sig0 _S')

focusR :: Worldly w => THING w -> THING w
focusR (_P :::: El (Path _S (Weld sig0 _S' sig1) _T)) = val (Lam $ (Decl,Point sig1) !- \ (i :: Ref w') -> etaquote (wk (_P :::: El (Path _S (Weld sig0 _S' sig1) _T))  / At (Rht (En (P i) :: Val w')))) :::: El (Path _S' sig1 _T)

-- can't replace with (probably several) Act instance(s)
-- due to fundep (w does not determine w')
(//) :: (w <= w', VarOperable t)
     => t (Syn One) w
     -> En (Syn Zero) w'
     -> t (Syn Zero) w'
body // x = varOp (Inst IdVO x) body

-- terms are to types as 'vectors' (Env Vals) are to telescopes
evalInstance :: Worldly w
             => LStar KStep Zero n
             -> Env Val n w
             -> Env THING n w
evalInstance L0             E0       = E0
evalInstance (ks :<: KS ty) (ES g v) = ES vs (v :::: eval (wk ty) vs)
  where vs = evalInstance ks g

elookup :: Fin n -> Env t n w -> t w
elookup FZero    (ES g v) = v
elookup (FSuc i) (ES g v) = elookup i g

class Eval t v | t -> v where
  eval :: Worldly w => t (Syn n) w -> Env THING n w -> v w

type family   (n :: Nat) :+ (m :: Nat) :: Nat
type instance Zero    :+ m = m
type instance (Suc n) :+ m = Suc (n :+ m)

instance Eval En THING where
  eval (V x)        g = elookup x g
  eval (P x)        g = refThing x
  eval (t ::: ty)   g = eval t g :::: eval ty g
  eval (f :/ s)     g = eval f g / eval s g
  eval (glob :% g') g = (:::: eval (wk tybody) newg') $ case globDefn glob of
    Nothing -> En (glob :% emap valOf newg')
    Just t  -> eval (wk t) newg'
    where
    tel :=> tybody = globArity glob
    newg'          = evalInstance tel (emap (\t -> eval t g) g')

instance Eval Tm Val where
  eval (Let e t) g = eval t (ES g (eval e g))
  eval (En e)    g = valOf $ eval e g
  eval (Atom s)  g = Atom s
  eval (t :& u)  g = eval t g :& eval u g
  eval (Lam t)   g = Lam (Scope g t)

val :: Worldly w => Eval t v => t (Syn Zero) w -> v w
val t = eval t E0

etaquote :: Worldly w => THING w -> TERM w
--etaquote (El ty      :::: Kind           ) = El  (etaquote (ty :::: Type))
etaquote (Ze         :::: Level          ) = Ze
etaquote (Su l       :::: Level          ) = Su  (etaquote (l :::: Level))
etaquote (Set l      :::: Type           ) = Set (etaquote (l :::: Level))
etaquote (Pi dom cod :::: Type           ) = Pi  (etaquote (dom :::: Type)) $
  (Decl,El dom) !- \ x -> etaquote ((wk cod / x) :::: Type)
etaquote (Sg dom cod :::: Type           ) = Sg  (etaquote (dom :::: Type)) $
  (Decl,El dom) !- \ x -> etaquote ((wk cod / x) :::: Type)
etaquote f@(_        :::: El (Pi dom cod)) = Lam $
  (Decl,El dom) !- \ x -> etaquote (wk f / x)
etaquote p@(_        :::: El (Sg dom cod)) =
  etaquote (p / "Fst") :& etaquote (p / "Snd")
etaquote (Ze         :::: Point seg      ) = Ze
etaquote (One        :::: Point seg      ) = One
etaquote (Lft p     :::: Point (Weld sig _ _)) = 
  case etaquote (p :::: Point sig) of
    Ze -> Ze
    One -> Rht Ze -- if you're in the middle you're on the right :)
    p   -> Lft p
etaquote (Rht p    :::: Point (Weld _ _ tau)) = 
  case etaquote (p :::: Point tau) of
    One -> One
    p   -> Rht p
etaquote _Q@(_ :::: Path _S seg _T) = Lam $
  (Decl,Point seg) !- \ (x :: Ref w') -> 
    etaquote (wk _Q / (At (En (P x)) :: Val w'))

etaquote (En e       :::: _              ) = En  (fst (netaquote e))

data Wibble w where
  Cheer :: Wibble w
  Fear  :: Wibble w

instance Dischargeable Wibble Wibble where
  discharge _ Cheer = Cheer
  discharge _ Fear  = Fear

netaquote :: Worldly w => Ne w -> (ELIM w, Val w)
netaquote (P x)       = (P x, refType x)
netaquote (e :/ s)    =
  (, (En e :::: ty) /: s) $ case (ty, s) of
    (El (Pi dom cod), s)   -> e' :/ etaquote (s :::: El dom)
    (El (Sg dom cod), Fst) -> e' :/ Fst
    (El (Sg dom cod), Snd) -> e' :/ Snd
    (El (Path _S seg _T), At p) -> e' :/ At (etaquote (p :::: Point seg))
    (Point _, Kink _S sig _T tau _U _P _Q) -> e' :/ Kink
      (etaquote (_S  :::: Type))
      (etaquote (sig :::: Seg))
      (etaquote (_T  :::: Type))
      (etaquote (tau :::: Seg))
      (etaquote (_U  :::: Type))
      (etaquote (_P  :::: El (Path _S sig _T)))
      (etaquote (_Q  :::: El (Path _T tau _U)))
  where
  (e' , ty) = netaquote e
netaquote (glob :% g) = (glob :% emap etaquote g', eval (wk t) g')
  where
  del :=> t = globArity glob
  g'        = evalInstance del g

-- We deliberately don't have a syntactic/structural equality for Ne.
-- Also we don't have an Eq instance at all for Val as it is type directed.

-- equality test on neutrals
instance Worldly w => Eq (Ne w) where
  n == n' = fst (netaquote n) == fst (netaquote n')

-- type directed equality test on values
kEq :: Worldly w => Kind w -> Val w -> Val w -> Bool
kEq k v v' = etaquote (v  :::: k) == etaquote (v' :::: k)

kEq' :: Worldly w => Kind w -> Val w -> Val w -> Wibble w
kEq' k v v' = if kEq k v v' then Cheer else Fear

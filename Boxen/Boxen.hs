{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving,
    PatternSynonyms, PatternGuards,
    MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

module Boxen where

import Prelude hiding ((/))
import Data.List hiding ((\\))
import Control.Monad
import Control.Applicative


------------------------------------------------------------------------------
-- SYNTAX OF TERMS AND VALUES
------------------------------------------------------------------------------

data Dir   = In  | Ex
data Phase = Val | Cut

data Tm :: Phase -> Dir -> * where
  A     :: String ->                               Tm p In
  (:&)  :: Tm p In -> Tm p In ->                   Tm p In
  L     :: Bd p ->                                 Tm p In
  E     :: Tm p Ex ->                              Tm p In
  V     :: Int ->                                  Tm Cut Ex
  P     :: Ref ->                                  Tm p Ex
  (:/)  :: Tm p Ex -> Tm p In ->                   Tm p Ex
  (:-)  :: Tm Cut In -> Tm Cut In ->               Tm Cut Ex
infixr 6 :&
infixl 8 :/
infixl 9 :-

data Bd :: Phase -> * where
  K     :: Tm p In ->           Bd p
  B     :: Tm Cut In ->         Bd Cut
  (:%)  :: ENV -> Tm Cut In ->  Bd Val

deriving instance Show (Tm p d)
deriving instance Show (Bd p)

type VAL  = Tm Val In
type ENV = [THING]
type KIND = VAL -- for documentary purposes
type THING = (VAL, KIND)
type TERM = Tm Cut In
type CUT = Tm Cut Ex

data Ref = Ref {nom :: String, kind :: KIND}
instance Show Ref  where show = nom
instance Eq Ref    where x == y = nom x == nom y
thing :: Ref -> THING
thing x = (E (P x), kind x)


------------------------------------------------------------------------------
-- COMPUTATION
------------------------------------------------------------------------------

val :: ENV -> TERM -> VAL
val g (A a)      = A a
val g (s :& t)   = val g s :& val g t
val g (L (K t))  = L (K t)
val g (L (B t))  = L (g :% t)
val g (E e)      = fst (evalki g e)

evalki :: ENV -> CUT -> THING
evalki g (V i)      = g !! i
evalki g (P x)      = (E (P x), kind x)
evalki g (f :/ s)   = evalki g f / val g s
evalki g (t :- _T)  = (val g t, val g _T)

class Slash f a t | f -> t where
  (/) :: f -> a -> t
infixl 8 /

instance Slash THING VAL THING where
  f / v = (f // v, f /: v)


------------------------------------------------------------------------------
-- TYPECHECKING WITH A NAME SUPPLY
------------------------------------------------------------------------------

newtype TC x = TC {tc :: Int -> Maybe x}  -- deriving Monoid does just the wrong thing

(!-) :: Syntactic t => KIND -> (Ref -> TC t) -> TC t
_S !- k = TC $ \ i ->
  let x = Ref {nom = show i, kind = _S}
  in  x \\ tc (k x) (i + 1)
infixr 4 !-

va :: (TERM -> TC ()) -> TERM -> TC VAL
va chk t = do
  chk t
  return (val [] t)


------------------------------------------------------------------------------
-- KINDS OF THING
------------------------------------------------------------------------------

pattern N = A ""

pattern Type = A "Type"
pattern El _T = A "El" :& _T :& N
pattern Seg = A "Seg"
pattern Point z = A "Point" :& z :& N

kindly :: TERM -> TC ()
kindly Type        = return ()
kindly (El _T)     = Type >:> _T
kindly Seg         = return ()
kindly (Point z)   = Seg :>: z
kindly _           = fail "unkind"


------------------------------------------------------------------------------
-- CONSTRUCTIONS
------------------------------------------------------------------------------

-- Types
pattern Pi _S _T = A "Pi" :& _S :& L _T :& N
pattern Sg _S _T = A "Sg" :& _S :& L _T :& N

(>:>) :: KIND -> TERM -> TC ()
infix 5 >:>

Type >:> Pi _S _T = do
  _S <- va (Type >:>) _S
  _S !- \ x -> Type >:> _T / x

Type >:> Sg _S _T = do
  _S <- va (Type >:>) _S
  _S !- \ x -> Type >:> _T / x

El (Pi _S _T) >:> L t = do
  _S !- \ x -> _T / x >:> t / x

El (Sg _S _T) >:> s :& t = do
  s <- va (El _S >:>) s
  El (_T / (s, _S)) >:> t

Seg >:> N = return ()

Seg >:> l :& r = do
  Seg >:> l
  Seg >:> r

Point _ >:> A "0" = return ()
Point _ >:> A "1" = return ()

-- are the next two really necessary?
-- Point (l :& r) >:> A "left" :& p   = Point l >:> p
-- Point (l :& r) >:> A "right" :& p  = Point r >:> p

want >:> E e = do
  got <- synth e
  want <<== snd got

_ >:> _ = fail "ill typed"


------------------------------------------------------------------------------
-- ELIMINATION ACTIONS
------------------------------------------------------------------------------

(/:>) :: KIND -> TERM -> TC ()
(El (Pi _S _T)) /:> s        = El _S >:> s
(El (Sg _S _T)) /:> A "car"  = return ()
(El (Sg _S _T)) /:> A "cdr"  = return ()
_               /:> _        = fail "bad action"

(/:) :: THING -> VAL -> KIND
(f, El (Pi _S _T))   /: v        = El (_T / (v, _S))
(p, El (Sg _S _T))   /: A "car"  = El _S
p@(_, El (Sg _S _T)) /: A "cdr"  = El (_T / (p // A "car", _S))

(//) :: THING -> VAL -> VAL
(E f, _)                 // v        = E (f :/ v)
(L b, El (Pi _S _T))     // v        = b / (v, _S)
(u :& v, El (Sg _S _T))  // A "car"  = u
(u :& v, El (Sg _S _T))  // A "cdr"  = v


------------------------------------------------------------------------------
-- SUBKINDING
------------------------------------------------------------------------------

(<<==) :: KIND -> KIND -> TC ()
infix 5 <<==

Type <<== Type = return ()

El (Pi _S _T) <<== El (Pi _S' _T') = do
  _S' <<== _S
  _S' !- \ x -> _T / x <<== _T' / x

El (Sg _S _T) <<== El (Sg _S' _T') = do
  _S <<== _S'
  _S !- \ x -> _T / x <<== _T' / x

Point _ <<== Point N = return ()

Point (l :& r) <<== Point (l' :& r') = do
  Point l <<== Point l'
  Point r <<== Point r'

_ <<== _ = fail "not a subkind"


------------------------------------------------------------------------------
-- VARIABLE OPERATIONS
------------------------------------------------------------------------------

data VarOp = Subs [CUT] | Abst [Ref]

class Syntactic t where
  varOp :: VarOp -> Int -> t -> t

(\\) :: Syntactic t => Ref -> t -> t
x \\ t = varOp (Abst [x]) 0 t
infixr 3 \\

instance Syntactic (Tm Cut d) where
  varOp (Subs es) i (V j) | i <= j                         = es !! (j - i)
  varOp (Abst xs) i (P x) | Just j <- findIndex (x ==) xs  = V (i + j)
  varOp z i (L (B t))  = L (B (varOp z (i + 1) t))
  varOp z i (L (K t))  = L (K (varOp z i t))
  varOp z i (u :& v)   = varOp z i u :& varOp z i v
  varOp z i (E e)      = E (varOp z i e)
  varOp z i (f :/ a)   = varOp z i f :/ varOp z i a
  varOp z i (t :- _T)  = varOp z i t :- varOp z i _T
  varOp z i t                    = t

instance Syntactic () where
  varOp _ _ () = ()

instance Syntactic t => Syntactic (Maybe t) where
  varOp z i = fmap (varOp z i)


------------------------------------------------------------------------------
-- BORING
------------------------------------------------------------------------------

instance Slash (Bd Val) THING VAL where
  K t       / _   = t
  (g :% t)  / vS  = val (vS : g) t

instance Slash (Bd Val) Ref VAL where
  t / x = t / thing x

instance Slash (Bd Cut) CUT TERM where
  K t / _ = t
  B t / s = varOp (Subs [s]) 0 t

instance Slash (Bd Cut) Ref TERM where
  b / x = b / (P x :: CUT)

instance Slash THING Ref THING where
  f / x = f / (E (P x) :: VAL)

instance Monad TC where
  return x = TC $ \ l -> Just x
  TC a >>= k = TC $ \ l -> do
    a <- a l
    tc (k a) l
  fail _ = TC $ \ _ -> Nothing

instance Applicative TC where
  pure = return
  (<*>) = ap

instance Functor TC where
  fmap = ap . return

synth :: CUT -> TC THING
synth (P x) = return (thing x)
synth (f :/ a) = do
  f <- synth f
  a <- va (snd f /:>) a
  return (f / a)
synth (t :- _K) = do
  _K <- va kindly _K
  t <- va (_K >:>) t
  return (t, _K)


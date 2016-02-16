{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving,
    PatternSynonyms, PatternGuards,
    MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances,
    UndecidableInstances #-}

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
  A     :: String ->                   Tm p In    -- atoms
  (:&)  :: Tm p In -> Tm p In ->       Tm p In    -- cons cells
  L     :: Bd p ->                     Tm p In    -- abstractions
  E     :: Tm p Ex ->                  Tm p In    -- eliminations
  V     :: Int ->                      Tm Cut Ex  -- bound variables
  P     :: Ref ->                      Tm p Ex    -- free variables
  (:/)  :: Tm p Ex -> Tm p In ->       Tm p Ex    -- action
  (:<)  :: Tm Cut In -> Tm Cut In ->   Tm Cut Ex  -- cut
infixr 6 :&
infixl 8 :/
infixl 9 :<

pattern N = A "" -- nil is the atom with the empty name

data Bd :: Phase -> * where
  K     :: Tm p In ->           Bd p
  B     :: Tm Cut In ->         Bd Cut
  (:%)  :: ENV -> Tm Cut In ->  Bd Val

deriving instance Show (Tm p d)
deriving instance Show (Bd p)
deriving instance Eq (Tm Cut d)

instance Eq (Bd Cut) where
  K s == K t =  s == t
  B s == B t =  s == t
  K s == B t =  varOp Thin 0 s == t
  B s == K t =  s == varOp Thin 0 t

type VAL   = Tm Val In
type ENV   = [THING]
type KIND  = VAL -- for documentary purposes
data THING = (:::) { valOf :: VAL, kindOf :: KIND } deriving Show
infix 2 :::
type TERM  = Tm Cut In
type CUT   = Tm Cut Ex

data Ref = Ref {nom :: String, kind :: KIND}
instance Show Ref  where show = nom
instance Eq Ref    where x == y = nom x == nom y
thing :: Ref -> THING
thing x = E (P x) ::: kind x


------------------------------------------------------------------------------
-- COMPUTATION
------------------------------------------------------------------------------

class Eval t v | t -> v, v -> t where
  val :: ENV -> t -> v

instance Eval TERM VAL where
  val g (A a)      = A a
  val g (s :& t)   = val g s :& val g t
  val g (L b)      = L (val g b)
  val g (E e)      = valOf (val g e)

instance Eval (Bd Cut) (Bd Val) where
  val g (K t)      = K (val g t)
  val g (B t)      = g :% t

instance Eval CUT THING where
  val g (V i)      = g !! i
  val g (P x)      = thing x
  val g (f :/ s)   = val g f / val g s
  val g (t :< _T)  = val g t ::: val g _T

class Slash f a t | f -> t where
  (/) :: f -> a -> t
infixl 8 /, //, /:

instance Slash THING VAL THING where
  f / v = f // v ::: f /: v


------------------------------------------------------------------------------
-- TYPECHECKING WITH A NAME SUPPLY
------------------------------------------------------------------------------

newtype TC x = TC {tc :: Int -> Maybe x}  -- deriving Monoid is wrong

class Discharge t b | t -> b, b -> t where
  (\\) :: Ref -> t -> b
infix 3 \\

(!-) :: Discharge t b => KIND -> (Ref -> TC t) -> TC b
_S !- k = TC $ \ i ->
  let x = Ref {nom = show i, kind = _S}
  in  x \\ tc (k x) (i + 1)
infixr 4 !-

va :: Eval t v => (t -> TC ()) -> t -> TC v
va chk t = do
  chk t
  return (val [] t)

nil :: Tm p In -> TC ()
nil N = return ()
nil _ = empty


------------------------------------------------------------------------------
-- KINDS OF THING (OR JUDGMENT FORMS, SORT OF)
------------------------------------------------------------------------------

pattern Type             = A "Type"
pattern El _T            = A "El" :& _T :& N
pattern Seg              = A "Seg"
pattern Point z          = A "Point" :& z :& N
pattern Types z          = A "Types" :& z :& N
pattern Path' _S _T      = A "Path" :& _S :& _T :& N

kindly :: TERM -> TC ()
kindly Type               = return ()
kindly (El _T)            = Type >:> _T
kindly Seg                = return ()
kindly (Point z)          = Seg >:> z
kindly (Types z)          = Seg >:> z
kindly (Path' _S _T)      = do
  nil _S <|> Type >:> _S
  nil _T <|> Type >:> _T
kindly _                  = fail "unkind"


------------------------------------------------------------------------------
-- CONSTRUCTIONS
------------------------------------------------------------------------------

pattern Pi _S _T         = A "Pi" :& _S :& L _T :& N
pattern Sg _S _T         = A "Sg" :& _S :& L _T :& N
pattern Path z _S _M _T  = A "Path" :& z :& _S :& _M :& _T :& N
pattern Mid _L _T _R     = _L :& _T :& _R :& N
pattern Fork l r         = A "fork" :& l :& r :& N

(>:>) :: KIND -> TERM -> TC ()
infix 5 >:>

Type >:> Pi _S _T = do
  _S <- va (Type >:>) _S
  _S !- \ x -> Type >:> _T / x

El (Pi _S _T) >:> L t = do
  _S !- \ x -> _T / x >:> t / x

Type >:> Sg _S _T = do
  _S <- va (Type >:>) _S
  _S !- \ x -> Type >:> _T / x

El (Sg _S _T) >:> s :& t = do
  s <- va (El _S >:>) s
  El (_T / (s ::: _S)) >:> t

Type >:> Path z _S _M _T = do
  z <- va (Seg >:>) z
  Type    >:> _S
  Types z >:> _M
  Type    >:> _T

Seg     >:> N = return ()
Types N >:> N = return ()
Point _ >:> A "0" = return ()
Point _ >:> A "1" = return ()

Seg            >:>      l :&  r    = do     Seg >:>  l ;                      Seg >:>  r
Types (l :& r) >:> Mid _L _T _R    = do Types l >:> _L ;  Type  >:> _T ;  Types r >:> _R
Point (l :& r) >:> A "left" :& p   =    Point l >:>  p
Point (l :& r) >:> A "right" :& p  =                                      Point r >:>  p

El (Path N _S N _T) >:> L _ST = do
  _ST <- va (\ _ST -> Point N !- \ i -> Type >:> _ST / i) _ST
  equalAt Type _S (_ST / (A "0" ::: Point N))
  equalAt Type (_ST / (A "1" ::: Point N)) _T

El (Path (l :& r) _S (Mid _L _T _R) _U) >:> Fork f g = do
  Path l _S _L _T >:> f
  Path r _T _R _U >:> g

El (Path N _S N _T) >:> Fork f g = Path' _S _T >:> Fork f g

Path' _S _T >:> Fork f g = do
  f <- va ((Path' _S N) >:>) f
  Path' ((f ::: Path' _S N) // A "1") _T >:> g

want >:> E e = do
  got <- synth e
  want <<== kindOf got

_ >:> _ = fail "ill typed"


------------------------------------------------------------------------------
-- ELIMINATION ACTIONS
------------------------------------------------------------------------------

(/:>) :: KIND -> TERM -> TC ()
El (Pi _S _T)              /:> s          = El _S >:> s
El (Sg _S _T)              /:> A "car"    = return ()
El (Sg _S _T)              /:> A "cdr"    = return ()
El (Path (l :& r) _S _ _T) /:> A "left"   = return ()
El (Path (l :& r) _S _ _T) /:> A "right"  = return ()
El (Path z _S _M _T)       /:> p          = Point z >:> p
El (Point z)               /:> (f :& _T)  = do
  _T <- va (Type >:>) _T
  case _T of
    Path z' _ _ _ -> Point z <<== Point z'
    _ -> empty
  El _T >:> f
_                          /:> _          = fail "bad action"

(/:) :: THING -> VAL -> KIND
(f ::: El (Pi _S _T))   /: v        = El (_T / (v ::: _S))
(p ::: El (Sg _S _T))   /: A "car"  = El _S
p@(_ ::: El (Sg _S _T)) /: A "cdr"  = El (_T / (p // A "car" ::: _S))

(_ ::: El (Path (l :& _) _S (Mid _L _T _) _)) /: A "left"  = El (Path l _S _L _T)
(_ ::: El (Path (_ :& r) _ (Mid _ _S _R) _T)) /: A "right" = El (Path r _S _R _T)
(_ ::: El (Path _ _ _ _))                     /: _         = Type

(//) :: THING -> VAL -> VAL
(L b ::: El (Pi _S _T))      // v          = b / (v ::: _S)
(u :& v ::: El (Sg _S _T))   // A "car"    = u
(u :& v ::: El (Sg _S _T))   // A "cdr"    = v
(_ ::: El (Path _ _S _ _))        // A "0"      = _S
(_ ::: El (Path _ _ _ _T))        // A "1"      = _T
q@(_ ::: El (Path _ _ _ _))       // (a :& p)   = q / a // p
(Fork f g ::: _)  // A "left"   = f
(Fork f g ::: _)  // A "right"  = g
(Fork f g ::: El _T@(Path z _ _ _)) // p = (p ::: Point z) // (Fork f g :& _T)
(L b      ::: Path' _ _)   // p      = b / (p ::: Point N)
(Fork f g ::: Path' _S _)  // A "0"  = (f ::: Path' _S N) // A "0"
(Fork f g ::: Path' _ _T)  // A "1"  = (g ::: Path' N _T) // A "1"
(E f ::: _)                  // v          = E (f :/ v)
(p ::: Point _) // (f :& _T) = (f ::: El _T) // p

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

El (Path N _S N _T) <<== El (Path _ _S' _ _T') = do
  equalAt Type _S _S'
  equalAt Type _T _T'

El (Path (l :& r) _S (Mid _L _T _R) _U) <<==
  El (Path (l' :& r') _S' (Mid _L' _T' _R') _U') = do
  El (Path l _S _L _T) <<== El (Path l' _S' _L' _T')
  El (Path r _T _R _U) <<== El (Path r' _T' _R' _U')

Path' _S _T <<== Path' _S' _T' = do
  nil _S' <|> equalAt Type _S _S'  -- check that _S isn't N?
  nil _T' <|> equalAt Type _T _T'  -- check that _S isn't N?

Point _ <<== Point N = return ()

Point (l :& r) <<== Point (l' :& r') = do
  Point l <<== Point l'
  Point r <<== Point r'

_ <<== _ = fail "not a subkind"


------------------------------------------------------------------------------
-- QUOTATION AND EQUALITY
------------------------------------------------------------------------------

equalAt :: KIND -> VAL -> VAL -> TC ()
equalAt k s t = do
  s' <- quote (s ::: k)
  t' <- quote (t ::: k)
  guard (s' == t')

quote :: THING -> TC TERM

quote (Pi _S _T ::: Type) = do
  _S' <- quote (_S ::: Type)
  _T' <- El _S !- \ x -> quote (_T / x ::: Type)
  return (Pi _S' _T')

quote f@(_ ::: Pi _S _T) = do
  t' <- _S !- \ x -> quote (f / x)
  return (L t')

quote (Sg _S _T ::: Type) = do
  _S' <- quote (_S ::: Type)
  _T' <- El _S !- \ x -> quote (_T / x ::: Type)
  return (Sg _S' _T')

quote p@(_ ::: Sg _S _T) = do
  s' <- quote (p / "car")
  t' <- quote (p / "cdr")
  return (s' :& t')


------------------------------------------------------------------------------
-- VARIABLE OPERATIONS
------------------------------------------------------------------------------

data VarOp = Subs [CUT] | Abst [Ref] | Thin

class Syntactic t where
  varOp :: VarOp -> Int -> t -> t

instance Syntactic (Tm Cut d) where
  varOp Thin      i (V j) | i <= j                         = V (j + 1)
  varOp (Subs es) i (V j) | i <= j                         = es !! (j - i)
  varOp (Abst xs) i (P x) | Just j <- findIndex (x ==) xs  = V (i + j)
  varOp z i (L (B t))  = L (B (varOp z (i + 1) t))
  varOp z i (L (K t))  = L (K (varOp z i t))
  varOp z i (u :& v)   = varOp z i u :& varOp z i v
  varOp z i (E e)      = E (varOp z i e)
  varOp z i (f :/ a)   = varOp z i f :/ varOp z i a
  varOp z i (t :< _T)  = varOp z i t :< varOp z i _T
  varOp z i t                    = t

instance Syntactic () where
  varOp _ _ () = ()

instance Syntactic t => Syntactic (Maybe t) where
  varOp z i = fmap (varOp z i)

instance Discharge () () where
  _ \\ () = ()

instance Discharge TERM (Bd Cut) where
  x \\ t = B (varOp (Abst [x]) 0 t)

instance Discharge t b => Discharge (Maybe t) (Maybe b) where
  x \\ mt = fmap (x \\) mt


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

instance Slash THING String THING where
  f / x = f / (A x :: VAL)

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

instance Alternative TC where
  empty = TC $ \ _ -> empty
  TC a <|> TC b = TC $ \ l -> a l <|> b l

synth :: CUT -> TC THING
synth (P x) = return (thing x)
synth (f :/ a) = do
  f <- synth f
  a <- va (kindOf f /:>) a
  return (f / a)
synth (t :< _K) = do
  _K <- va kindly _K
  t <- va (_K >:>) t
  return (t ::: _K)


--{-# OPTIONS -Wall -fwarn-incomplete-patterns #-}
{-# LANGUAGE KindSignatures, DataKinds, ScopedTypeVariables, PolyKinds,
             UndecidableInstances, MultiParamTypeClasses,
             FunctionalDependencies, TypeOperators,
             FlexibleInstances, GADTs, DeriveFunctor, RankNTypes,
             EmptyCase, TypeFamilies, PatternSynonyms,
             GeneralizedNewtypeDeriving #-}
module TypeCheck where

import Prelude hiding ((/))
import Utils
import Syntax

-- our monad is on world-indexed sets
newtype TC t w = TC (Maybe (t w)) deriving Show

pattern Yes t = TC (Just t)
pattern No    = TC Nothing

instance Weakenable t => Weakenable (TC t)

(>>>=) :: TC s w -> (s w -> TC t w) -> TC t w
Yes s >>>= f = f s
No    >>>= _ = No

(>>>==) :: [TC s w] -> ([s w] -> TC t w) -> TC t w
[]     >>>== k = k []
(x:xs) >>>== k =
  x  >>>=  \ x ->
  xs >>>== \ xs ->
  k (x:xs)

tcBool :: Bool -> TC Happy w
tcBool True = Yes Happy
tcBool False = No

instance Dischargeable f g => Dischargeable (TC f) (TC g) where
  discharge x No      = No
  discharge x (Yes f) = Yes (discharge x f)


-- actionOk
(/:>) :: Worldly w => Kind w -> TERM w -> TC Happy w
El (Pi _S _T) /:> s   = El _S >:> s
El (Sg _S _T) /:> Fst = Yes Happy
El (Sg _S _T) /:> Snd = Yes Happy
El (Path _S sig _T) /:> At p = Point sig >:> p
_             /:> _   = No

-- evaluate action safely
(/:>=) :: Worldly w => Kind w -> TERM w -> TC Val w
k /:>= t = k /:> t >>>= \ _ -> Yes (val t)

-- check a term in a trusted kind
(>:>) :: Worldly w => Kind w -> TERM w -> TC Happy w
Kind            >:> Type       = Yes Happy
Type            >:> Set l      = Level >:> l
Type            >:> Pi dom cod =
  (Type >:>= dom) >>>= \ dom ->
  (Decl,El dom) !- \ x -> Type >:> (cod // P x)
Type            >:> Sg dom cod =
  (Type >:>= dom) >>>= \ dom ->
  (Decl,El dom) !- \ x -> Type >:> (cod // P x)
Kind            >:> El t = Type >:> t
El (Set l')     >:> Set l      =
  Level >:>= l >>>= \l ->
  l' `levelGT` l
El (Set l)      >:> Pi dom cod =
  (El (Set l) >:>= dom) >>>= \ dom ->
  (Decl,El dom) !- \ x -> wk (El (Set l)) >:> (cod // P x)
El (Set l)      >:> Sg dom cod =
  (El (Set l) >:>= dom) >>>= \ dom ->
  (Decl,El dom) !- \ x -> wk (El (Set l)) >:> (cod // P x)
El (Pi dom cod) >:> Lam t      =
  (Decl,El dom) !- \ x -> El (wk cod / x) >:> (t // P x)
El (Sg dom cod) >:> (t :& u)   =
  (El dom >:>= t) >>>= \ t ->
  El (cod / (t :::: El dom)) >:> u
Kind            >:> Level      = Yes Happy
Level           >:> Ze         = Yes Happy
Level           >:> Su n       = Level >:> n

Kind            >:> Seg        = Yes Happy
Seg             >:> Dash       = Yes Happy
Seg             >:> Weld sig _T tau =
  Seg  >:> sig >>>= \ _ ->
  Type >:> _T  >>>= \ _ ->
  Seg  >:> tau
Kind            >:> Point sig  = Seg >:> sig
Point sig       >:> Point Ze   = Yes Happy
Point sig       >:> Point One  = Yes Happy
Point (Weld sig _T tau) >:> Lft p = Point sig >:> p
Point (Weld sig _T tau) >:> Rht p = Point tau >:> p
Type            >:> Path _S sig _T =
  Type >:> _S  >>>= \ _ ->
  Seg  >:> sig >>>= \ _ -> 
  Type >:> _T
El (Path _S sig _T) >:> Lam _M =
  (Decl,Point sig)                                          !-   \ i -> 
  Type >:> (_M // P i)                                      >>>= \ _ ->
  tcBool (kEq Type _S (Scope E0 _M / (Ze  :::: Point sig))) >>>= \ _ ->
  tcBool (kEq Type _T (Scope E0 _M / (One :::: Point sig)))
{-El (Path _S Dash _U) >:> Link _Q _M _Q' = 
  Type                 >:>= _M  >>>= \ _M ->
  El (Path _S Dash _M) >:>  _Q  >>>= \ _ ->
  El (Path _M Dash _U) >:>  _Q' -}

want            >:> En e =
  infer e >>>= \ got ->
  kindOf got `subKind` want
k               >:> Let e t    =
  infer e >>>= \ (v :::: j) ->
  (Local v,j) !- \ x -> wk k >:> (t // P x)
_               >:> _          = No

levelGT :: Worldly w => Val w -> Val w -> TC Happy w
Ze    `levelGT` _    = No
Su l' `levelGT` Ze   = Yes Happy
Su l' `levelGT` Su l = l' `levelGT` l

-- evaluate a term safely
(>:>=) :: Worldly w => Kind w -> TERM w -> TC Val w
k >:>= t = k >:> t >>>= \ _ -> Yes (val t)

-- infer
-- safely evaluate an elim and return a thing (evaluated elim + its kind)
infer :: Worldly w => ELIM w -> TC THING w
infer (P x)     = Yes (refThing x)
infer (e :/ s)  = 
  infer e    >>>= \ e@(v :::: k) ->
  (k /:>= s) >>>= \ s ->
  Yes (e / s)
infer (x :% g)  = case globArity x of
  ks :=> cod ->
    goodInstance ks g >>>= \ vs ->
    Yes $ let k = eval (wk cod) vs in
      case globDefn x of
        Nothing -> En (x :% emap valOf vs) :::: k
        Just t  -> eval (wk t) vs :::: k
infer (t ::: k) =
  (Kind >:>= k) >>>= \ k ->
  (k >:>= t)    >>>= \ t ->
  Yes (t :::: k)

goodInstance :: Worldly w
             => LStar KStep Zero n
             -> Env TERM n w
             -> TC (Env THING n) w
goodInstance L0             E0       = Yes E0
goodInstance (ks :<: KS ty) (ES g t) =
  goodInstance ks g        >>>= \ vs ->
  (eval (wk ty) vs >:>= t) >>>= \ v ->
  Yes (ES vs (v :::: eval (wk ty) vs))

subKind :: Worldly w => Val w -> Val w -> TC Happy w
Type              `subKind` Type              = Yes Happy
El (Pi dom0 cod0) `subKind` El (Pi dom1 cod1) =
  El dom1 `subKind` El dom0 >>>= \ _ ->
  (Decl,El dom1) !- \ x -> El (wk cod0 / x) `subKind` El (wk cod1 / x)
El (Sg dom0 cod0) `subKind` El (Sg dom1 cod1) =
  El dom0 `subKind` El dom1 >>>= \ _ ->
  (Decl,El dom0) !- \ x -> El (wk cod0 / x) `subKind` El (wk cod1 / x)
El (Set _)        `subKind` Type              = Yes Happy
El (Set l)        `subKind` El (Set l')       = levelLEQ l l'
Level             `subKind` Level             = Yes Happy

El (Path _S _ _T) `subKind` El (Path _S' Dash _T') =
  tcBool (kEq Type _S _S') >>>= \ _ ->
  tcBool (kEq Type _T _T') 
El (Path _S (Weld sig _M tau) _T) `subKind` El (Path _S' (Weld sig' _M' tau') _T') =
  El (Path _S sig _M) `subKind` El (Path _S' sig' _M') >>>= \ _ ->
  El (Path _M tau _T) `subKind` El (Path _M' tau' _T')
El this           `subKind` El that           =
  if kEq Type this that then Yes Happy else No
En e0             `subKind` En e1             =
  if e0 == e1 then Yes Happy else No
_                 `subKind` _                 = No

levelLEQ :: Worldly w => Val w -> Val w -> TC Happy w
Ze    `levelLEQ` _    = Yes Happy
Su l' `levelLEQ` Ze   = No
Su l' `levelLEQ` Su l = l' `levelLEQ` l

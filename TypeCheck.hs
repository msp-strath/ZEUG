--{-# OPTIONS -Wall -fwarn-incomplete-patterns #-}
{-# LANGUAGE KindSignatures, DataKinds, ScopedTypeVariables, PolyKinds,
             UndecidableInstances, MultiParamTypeClasses,
             FunctionalDependencies, TypeOperators,
             FlexibleInstances, GADTs, DeriveFunctor, RankNTypes,
             EmptyCase, TypeFamilies #-}
module TypeCheck where

import Utils
import Syntax

-- our monad is on world-indexed sets
data TC t w where
  Yes :: t w -> TC t w
  No  :: TC t w
  deriving Show

instance Weakenable t => Weakenable (TC t)

(>>>=) :: TC s w -> (s w -> TC t w) -> TC t w
Yes s >>>= f = f s
No    >>>= _ = No

instance Dischargeable f g => Dischargeable (TC f) (TC g) where
  discharge x No      = No
  discharge x (Yes f) = Yes (discharge x f)

isType :: Worldly w => TERM w -> TC Happy w
isType (Let e ty) = goodElim e >>>= \ (v :&: vty) ->
  (Local v,vty) !- \ x -> isType (ty // x)
isType (En ety) =
  enType ety >>>= \ ty ->
    case ty of
      Set -> Yes Happy
      _    -> No
isType Set      = Yes Happy
isType (Pi sty tty) = 
  goodType sty >>>= \ sty ->
    (Decl,sty) !- \ x -> isType (tty // x)
isType (Sg sty tty) = 
  goodType sty >>>= \ sty ->
    (Decl,sty) !- \ x -> isType (tty // x)
isType _ = No

goodType :: Worldly w => TERM w -> TC Val w
goodType t = isType t >>>= \ _ -> Yes (val t)

(>:>) :: Worldly w => Val w -> TERM w -> TC Happy w
ty         >:> Let e t  = goodElim e >>>= \ (v :&: vty) ->
  (Local v,vty) !- \ x -> wk ty >:> (t // x)
Set        >:> t        = isType t -- won't work with hierarchy
Pi dom cod >:> Lam t    = (Decl,dom) !- \ x -> (wk cod $/ x) >:> (t // x)
Sg dom cod >:> (t :& u) = dom `goodTerm` t >>>= \ vt -> (cod $/ vt) >:> u
want        >:> En e     = enType e >>>= \ got -> got `subType` want
_           >:> _        = No

goodTerm :: Worldly w => Val w -> TERM w -> TC Val w
ty `goodTerm` t = ty >:> t >>>= \ _ -> Yes (val t)

enType :: Worldly w => ELIM w -> TC Val w
enType (P x)      = Yes (refType x)
enType (e :$ s)   = goodElim e >>>= \ (v :&: ty) -> case ty of
  Pi dom cod -> (dom `goodTerm` s) >>>= \ vs -> Yes (cod $/ vs)
  Sg dom cod -> case s of
    Atom "Fst" -> Yes dom
    Atom "Snd" -> Yes (cod $/ vfst v)
    _ -> No
  _ -> No
enType (x :% g)   = case globKind x of
  ks :=> cod -> goodInstance ks g >>>= \ vs -> Yes $ eval (wk cod) vs
enType (t ::: ty) =
  goodType ty >>>= \ vty -> 
  vty >:> t   >>>= \ _ -> Yes vty 

goodInstance :: Worldly w => 
            LStar KStep Zero n -> Env (Syn Zero) n w -> TC (Env Sem n) w
goodInstance (ks :<: KS ty) (ES g t) = 
  goodInstance ks g >>>= \ vs ->
  eval (wk ty) vs `goodTerm` t >>>= \ v ->
  Yes (ES vs v)
goodInstance L0             E0       = Yes E0

goodElim :: Worldly w => ELIM w -> TC (Val :* Val) w
goodElim e = enType e >>>= \ vty -> Yes (val e :&: vty)

-- subtype is just equality at the mo'
subType :: Worldly w => Val w -> Val w -> TC Happy w
Set `subType` Set = Yes Happy
Pi dom0 cod0 `subType` Pi dom1 cod1 = dom1 `subType` dom0 >>>= \ _ ->
  (Decl,dom1) !- \ x -> (wk cod0 $/ x) `subType` (wk cod1 $/ x)
Sg dom0 cod0 `subType` Sg dom1 cod1 = dom0 `subType` dom1 >>>= \ _ ->
  (Decl,dom0) !- \ x -> (wk cod0 $/ x) `subType` (wk cod1 $/ x)
En e0 `subType` En e1 = if e0 == e1 then Yes Happy else No
_     `subType` _     = No


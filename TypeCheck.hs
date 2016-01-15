--{-# OPTIONS -Wall -fwarn-incomplete-patterns #-}
{-# LANGUAGE KindSignatures, DataKinds, ScopedTypeVariables, PolyKinds,
             UndecidableInstances, MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances, GADTs, DeriveFunctor, RankNTypes, EmptyCase,
             TypeFamilies #-}
module TypeCheck where

import Data.Proxy
import Unsafe.Coerce
import Utils
import Syntax

data TC t w where
  Yes :: t w -> TC t w
  No  :: TC t w
  deriving Show

(>>>=) :: TC s w -> (s w -> TC t w) -> TC t w
Yes s >>>= f = f s
No    >>>= _ = No

instance Dischargeable f g => Dischargeable (TC f) (TC g) where
  discharge x No      = No
  discharge x (Yes f) = Yes (discharge x f)

isType :: Worldly w => TERM w -> TC Happy w
isType (En ety) =
  enType ety >>>= \ ty ->
    case ty of
      VSet -> Yes Happy
      _    -> No
isType Set      = Yes Happy
isType (Pi sty tty) = 
  goodType sty >>>= \ sty ->
    sty !- \ x -> isType (tty // x)
isType _ = No

goodType :: Worldly w => TERM w -> TC Val w
goodType t = isType t >>>= \ _ -> Yes (val t)

(>:>) :: Worldly w => Val w -> TERM w -> TC Happy w
VSet        >:> t     = isType t -- won't work with hierarchy
VPi dom cod >:> Lam t = dom !- \ x -> (wk cod $/ x) >:> (t // x)
want        >:> En e  = enType e >>>= \ got -> got `subType` want
_           >:> _      = No

goodTerm :: Worldly w => Val w -> TERM w -> TC Val w
ty `goodTerm` t = ty >:> t >>>= \ _ -> Yes (val t)

enType :: Worldly w => ELIM w -> TC Val w
enType (P x)      = Yes (reftype x)
enType (f :$ s)   = enType f >>>= \ ty -> case ty of
  VPi dom cod -> (dom `goodTerm` s) >>>= \ vs -> Yes (cod $/ vs)
enType (t ::: ty) = goodType ty >>>= \ vty -> vty >:> t >>>= \ _ -> Yes vty 

subType :: Worldly w => Val w -> Val w -> TC Happy w
VSet `subType` VSet = Yes Happy
VPi dom0 cod0 `subType` VPi dom1 cod1 = dom1 `subType` dom0 >>>= \ _ ->
  dom1 !- \ x -> (wk cod0 $/ x) `subType` (wk cod1 $/ x)
Ne e0 `subType` Ne e1 = if e0 == e1 then Yes Happy else No
_     `subType` _     = No

yestest0 :: TC Val W0                        
yestest0 = enType ((Lam (En (V FZero)) ::: Pi Set Set))

yestest1 :: TC Val W0
yestest1 = enType ((Lam (En (V FZero)) ::: Pi Set Set) :$ Set)

yestest2 :: TC Val W0
yestest2 = enType (Lam (Lam (En (V FZero))) ::: Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))))

yestest3 :: TC Val W0
yestest3 = enType (Lam (Lam (En (V FZero))) ::: Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))) :$ Set)

yestest4 :: TC Val W0
yestest4 = enType (Lam (Lam (En (V FZero))) ::: Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))) :$ Set :$ Set)

notest0 :: TC Val W0
notest0 = enType ((Lam (En (V FZero)) ::: Set) :$ Set)

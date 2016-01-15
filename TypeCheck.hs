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
    sty !- \ x -> isType (tty // P x)
isType _ = No

goodType :: Worldly w => TERM w -> TC Val w
goodType t = isType t >>>= \ _ -> Yes (val t)

(>:>) :: Worldly w => Val w -> TERM w -> TC Happy w
VSet        >:> t     = isType t -- won't work with hierarchy
VPi dom cod >:> Lam t = dom !- \ x -> (wk cod $/ Ne (NP x)) >:> (t // P x)
want        >:> En e  = enType e >>>= \ got -> got `subType` want
_           >:> _      = No

goodTerm :: Worldly w => Val w -> TERM w -> TC Val w
ty `goodTerm` t = ty >:> t >>>= \ _ -> Yes (val t)

enType :: Worldly w => ELIM w -> TC Val w
enType (P x)    = Yes (reftype x)
enType (f :$ s) = enType f >>>= \ ty -> case ty of
  VPi dom cod -> (dom `goodTerm` s) >>>= \ vs -> Yes (cod $/ vs)

subType :: Worldly w => Val w -> Val w -> TC Happy w
VSet `subType` VSet = Yes Happy
VPi dom0 cod0 `subType` VPi dom1 cod1 = dom1 `subType` dom0 >>>= \ _ ->
  dom1 !- \ x -> let vx = Ne (NP x) in (wk cod0 $/ vx) `subType` (wk cod1 $/ vx)
Ne e0 `subType` Ne e1 = if e0 == e1 then Yes Happy else No
_     `subType` _     = No
                                       

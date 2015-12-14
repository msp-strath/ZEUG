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

type TC = Maybe

isType :: Worldly w => TERM w -> TC (Happy w)
isType (En e) = do
  ty <- enType e
  case whnf ty of
    Set -> return Happy
    _   -> fail "barf"
isType Set    = return Happy
isType (Pi sty tty) = do
  isType sty
  sty !- \ x -> isType (tty // x)
isType _ = fail "blerk"

whnf :: TERM w -> TERM w
whnf = id

(>:>) :: TYPE w -> TERM w -> TC ()
(>:>) = undefined

hdType :: Hd Zero w -> TC (TYPE w)
hdType = undefined

($:) :: (En Zero w, TYPE w) -> TERM w -> TC (TYPE w)
($:) = undefined

enType :: En Zero w -> TC (TYPE w)
enType (h :$ sz) = hdType h >>= \ ty -> go (h,ty) sz where
  go (h,ty) B0        = return ty
  go (h,ty) (sz :< s) = do
    ety <- go (h,ty) sz
    (h :$ sz, ety) $: s

--(!-) :: TYPE -> (En Zero -> TC ()) -> TC ()
--(!-) = undefined

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

isType :: TERM w -> TC ()
isType (En e) = enType e >> return ()
isType Set    = return ()
isType (Pi sty tty) = do
  isType sty
  undefined
isType _ = error "blerk"

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

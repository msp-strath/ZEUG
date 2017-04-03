-- mind your...
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures, TypeFamilies #-}
module DefEq where

import Data.Void
import Utils
import OPE
import Kernel

data Context :: Bwd Sort -> * where
  C0 :: Context B0
  (:\) :: Sorted gamma => Context gamma -> (Sorty s , String , Info s ^ gamma) ->
          Context (gamma :< s)

type family Info (s :: Sort) :: Bwd Sort -> * where
  Info Syn = Term Chk
  Info Chk = Got Void
  Info Pnt = Got ()

defEq :: Sorted gamma =>
         Context gamma ->
         Term Chk ^ gamma -> Term Chk ^ gamma -> Term Chk ^ gamma ->
         Maybe ()
defEq _ _ _ _ = Just ()

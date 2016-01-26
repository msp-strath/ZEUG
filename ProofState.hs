{-# LANGUAGE KindSignatures, PolyKinds, GADTs, DataKinds #-}

module ProofState where

import Utils
import Syntax

type Naming = String

type PZ = LStar PZStep

data PZStep (v :: World) (w :: World) where
  Param   :: Naming -> Extended v w -> PZStep v w
  Module  :: Naming -> Ex Global -> Dot (PZ w) PTip -> PZStep w w
  Middle  :: Naming -> Dot (PZ w) PTip -> PZStep w w

data PTip (w :: World) where
  P0 :: PTip w



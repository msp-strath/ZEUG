{-# LANGUAGE KindSignatures, PolyKinds, GADTs, DataKinds #-}

module ProofState where

import Utils
import Syntax
import TypeCheck

type Naming = String

type NameStep = (Naming, Int)
type RawLongName = (NameStep, [NameStep])

type PZ = LStar PZStep

data PZStep (v :: World) (w :: World) where
  Param   :: Naming -> Extended v w -> PZStep v w
  Module  :: Naming -> Maybe (Ex Global) -> Dot (PZ w) PTip -> PZStep w w
  Middle  :: Naming -> Dot (PZ w) PTip -> PZStep w w

data PTip (w :: World) where
  P0 :: PTip w

data Resolution (w :: World) where
  RParam :: Ref w -> Resolution w
  RGlob  :: Global n -> Env (Syn Zero) m w -> RStar KStep m n -> Resolution w

instance Weakenable Resolution 

stripParams :: PZ v w -> Bwd (Ref w)
stripParams L0                 = B0
stripParams (pz :<: Param y e) = 
  -- fmapping weakening costs
  fmap (extwk e) (stripParams pz) :< extrRef e

resolve :: RawLongName -> PZ v w -> TC Resolution w
resolve ((x,i),nsteps) = help i 
  where 
  help :: Int -> PZ v w -> TC Resolution w
  help i L0                    = No
  help i (pz :<: Param  y e  ) = case (x == y, i, nsteps) of
    (True, 0, []) -> Yes $ RParam (extrRef e)
    (True, 0, _ ) -> No -- looking for module components inside a param
    (True, i, _ ) -> extwk e $ help (i-1) pz
    (False, _, _) -> extwk e $ help i pz
  help i (pz :<: Module y mglob (Wit (pz' :&: _))) = case (x == y, i) of
    (True, 0) -> help2 nsteps mglob pz'
    (True, i) -> help (i-1) pz
    (False, _) -> help i pz
  help i (pz :<: Middle _ _  ) = help i pz

  help2 :: [NameStep] -> Maybe (Ex Global) -> PZ v w -> TC Resolution u
  help2 [] Nothing     pz = No
  help2 [] (Just glob) pz = undefined

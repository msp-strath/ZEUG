{-# LANGUAGE KindSignatures, PolyKinds, GADTs, DataKinds, TypeOperators #-}

module ProofState where

import Utils
import Syntax
import TypeCheck

type Naming = String

type NameStep = (Naming, Int)
type RawLongName = (NameStep, [NameStep])

-- b : Bool signifies if Middle is allowed
type PZ b = LStar (PZStep b)

data PZStep (b :: Bool)(v :: World) (w :: World) where
  Param   :: Naming -> Extended v w -> PZStep b v w
  Module  :: Naming -> Maybe (Ex Global) -> Dot (PZ False w) PTip ->
             PZStep b w w
  -- middle is a back pointer
  Middle  :: Naming -> Dot (PZ False w) PTip -> PZStep True w w

data PTip (w :: World) where
  P0 :: PTip w

data Resolution (w :: World) where
  RParam :: Ref w -> Resolution w
  RGlob  :: Global n -> Env (Syn Zero) m w -> Resolution w

instance Weakenable Resolution 

stripParams :: PZ True v w -> Ex2 (Env (Syn Zero)) w
stripParams = stripParams' id where
  stripParams' :: (TERM u -> TERM w) -> PZ True v u -> Ex2 (Env (Syn Zero)) w
  stripParams' w L0                    = Wit2 E0
  stripParams' w (pz :<: Param y e)    = case stripParams' (w . extwk e) pz of
      Wit2 g -> Wit2 (ES g (w (En (P (extrRef e)))))
  stripParams' w (pz :<: Module _ _ _) = stripParams' w pz
  stripParams' w (pz :<: Middle _ _)   = stripParams' w pz

resolve :: RawLongName -> PZ True v w -> TC Resolution w
resolve ((x,i),nsteps) = help i 
  where 
  help :: Int -> PZ True v w -> TC Resolution w
  help i L0                                        = No
  help i (pz :<: Param  y e)                       = case (x == y, i, nsteps) of
    (True, 0, []) -> Yes $ RParam (extrRef e)
    (True, 0, _ ) -> No -- looking for module components inside a param
    (True, i, _ ) -> extwk e $ help (i-1) pz
    (False, _, _) -> extwk e $ help i pz
  help i (pz :<: Module y mglob (Wit (pz' :&: _))) = case (x == y, i) of
    (True,  0) -> case (help2 nsteps mglob pz', stripParams pz) of
      (Just (Wit glob), Wit2 g) -> Yes (RGlob glob g)
      _                         -> No
    (True,  i) -> help (i-1) pz
    (False, _) -> help i pz
  help i (pz :<: Middle _ _  )                     = help i pz

  help2 :: [NameStep] -> Maybe (Ex Global) -> PZ False v w -> Maybe (Ex Global)
  help2 []       mglob pz = mglob
  help2 ((x,i) : xs) _ pz = help2' i pz
    where
    help2' :: Int -> PZ False v w -> Maybe (Ex Global)
    help2' i (pz :<: Param y e) = help2' i pz
    help2' i (pz :<: Module y mglob (Wit (pz' :&: _))) = case (x == y, i) of
      (True,  0) -> help2 xs mglob pz'
      (True,  i) -> help2' (i-1) pz
      (False, _) -> help2' i pz
    

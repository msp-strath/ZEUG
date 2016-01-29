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


eqNameStep :: Naming -> NameStep -> Either NameStep ()
eqNameStep y xi@(x,i) = case (x == y, i) of
   (True,  0) -> Right ()
   (True,  i) -> Left (x,i-1)
   (False, _) -> Left xi 

resolve :: RawLongName -> PZ True v w -> TC Resolution w
resolve (xi,nsteps) = lookOut xi
  where 
  lookOut :: NameStep -> PZ True v w -> TC Resolution w
  lookOut xi L0                                        = No
  lookOut xi (pz :<: Param  y e)                       =
    case eqNameStep y xi of
       -- found it!
      Right _ | null nsteps -> Yes $ RParam (extrRef e)
              -- looking for module components inside a param
              | otherwise   -> No
       -- carry on looking
      Left xi -> extwk e $ lookOut xi pz
  lookOut xi (pz :<: Module y mglob (Wit (pz' :&: _))) =
    case eqNameStep y xi of
      -- found the 'corner'; look inside
      Right _ -> case (lookInside nsteps mglob pz', stripParams pz) of 
        (Just (Wit glob), Wit2 g) -> Yes (RGlob glob g)
        _                         -> No
      -- carry on looking
      Left xi -> lookOut xi pz
  lookOut i (pz :<: Middle _ _  )                     = lookOut i pz

  lookInside :: [NameStep] -> Maybe (Ex Global) -> PZ False v w ->
                Maybe (Ex Global)
  lookInside []           mglob pz = mglob -- found it!
  lookInside (xi : xs) _     pz = lookInside' xi pz
    where
    lookInside' :: NameStep -> PZ False v w -> Maybe (Ex Global)
    lookInside' _ L0 = Nothing
    lookInside' xi (pz :<: Param _ _) = lookInside' xi pz
      -- parameters are not in scope
    lookInside' xi (pz :<: Module y mglob (Wit (pz' :&: _))) =
      case eqNameStep y xi of
        -- found the next step
        Right _ -> lookInside xs mglob pz'
        -- carry on looking
        Left xi -> lookInside' xi pz

    

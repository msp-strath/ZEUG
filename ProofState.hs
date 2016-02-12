{-# LANGUAGE KindSignatures, PolyKinds, GADTs, DataKinds, TypeOperators, ScopedTypeVariables #-}

module ProofState where

import Control.Newtype
import Utils
import Layout
import Raw
import Syntax
import TypeCheck

type Supply = (Bwd Int, Int)

supply0 :: Supply
supply0 = (B0, 0)
supplySuc :: Supply -> Supply
supplySuc (is, i) = (is,i+1)
supplySic :: Supply -> Supply
supplySic (is, i) = (is :< i,0)
supply :: Supply -> LongName
supply (is, i) = is <>> [i]


data ProofState (b :: Bool)(u :: World) where
  (:!-:) :: Worldly w => (PZ b u w, Supply) -> PTip w -> ProofState b u

ugly :: Int -> ProofState b u -> String
ugly i ((ps,_) :!-: tip) = uglies ps ++ "\n" ++ replicate i ' ' ++  uglytip tip
  where
  uglies :: PZ b u w -> String
  uglies L0 = ""
  uglies (ps :<: step) = uglies ps ++ "\n" ++ replicate i ' ' ++ uglyStep step

  uglyStep :: PZStep b v w -> String
  uglyStep (Param n e ty)   = concat ["(",n," : ",show ty,")"]
  uglyStep (Module n mg ps) = concat ["{",n,"\n",ugly (i+2) ps,"}"]
  uglyStep (Middle n ln ps) = concat ["after ",n,"\n",ugly i ps]

  uglytip :: PTip w -> String
  uglytip P0           = ""
  uglytip (PDef mt ty) = maybe "?" show mt ++ " : " ++ show ty
  uglytip (PRaw rm)    = "Raw..."

type PROOFSTATE = ProofState True W0

ambulando :: PROOFSTATE -> PROOFSTATE
ambulando ((ps,sup) :!-: PRaw (_ := RawTip (_ := RawBlank)))              = ambulando ((ps,sup) :!-: P0)
ambulando ((ps,sup) :!-: (PRaw (_ := RawTip (_ := RawDefn t (_ := ty))) :: PTip w)) = case help of
    No         -> ambulando ((ps,sup) :!-: P0)
    Yes (TC t :&: ty) -> ambulando ((ps,sup) :!-: PDef t ty)
  where
  help :: TC (TC TERM :* TERM) w
  help = bake ps VNil ty >>>= \ ty -> goodType ty >>>= \ vty -> case t of
    Left _ -> Yes (No :&: ty)
    Right (_ := t) -> Yes ((bake ps VNil t >>>= \ t -> vty >:> t >>>= \ _ -> Yes t) :&: ty) 
    
ambulando ((ps,sup) :!-: PRaw (_ := RawParam (x,_ := rs) m)) = case bake ps VNil rs >>>= \ bs -> goodType bs >>>= \ vs -> Yes (bs :&: vs) of
  Yes (bs :&: vs) -> ambulando ((ps :<: Param x (extend (Decl,vs)) bs,sup) :!-: PRaw m)
  No    -> ambulando ((ps,sup) :!-: P0) 
ambulando ((ps,sup) :!-: PRaw (_ := RawSubMod (x,m) m')) =
  ambulando ((ps :<: Middle x (supply sup) ((L0,supplySuc sup) :!-: PRaw m'), supplySic sup) :!-: PRaw m)
ambulando ((ps,sup) :!-: PRaw (_ := RawModComm mrs m))   = ambulando ((ps,sup) :!-: PRaw m) -- bad: binning the comment
ambulando prfst@((ps,supi) :!-: tipi) = case help ps of
    Wit (L0 :&: _) -> prfst
    Wit ((pso :<: Middle x ln ((psu,supu) :!-: tipu)) :&: Flip psi) -> case lifter ps of
      Lifting del rho -> ambulando (((pso :<: Module x (globber ln prfst) ((psi,supi) :!-: tipi)) >>> lmap annoying psu,supu) :!-: tipu)
      -- should cache a thing rather just sticking in a Nothing
    where
    globber :: LongName -> PROOFSTATE -> Maybe (Ex Global)
    globber ln ((ps,_) :!-: PDef mt ty) = case lifter ps of
      Lifting del rho -> Just (Wit (Glob ln (del :=> varOp rho ty) (fmap (varOp rho) mt)))
    globber ln _ = Nothing
    
    annoying :: PZStep False u w -> PZStep True u w
    annoying (Param n e ty) = Param n e ty
    annoying (Module n g p) = Module n g p

    help :: PZ True u w -> RC (PZ True) (PZ False) u w
    help L0                        = Wit (L0 :&: Flip L0)
    help ps@(_ :<: Middle _ _ _)     = Wit (ps :&: Flip L0)
    help (ps :<: Param n e ty)        = case help ps of
      Wit (ps :&: Flip ps') -> Wit (ps :&: Flip (ps' :<: Param n e ty))
    help (ps :<: Module n mg x) = case help ps of
      Wit (ps :&: Flip ps') -> Wit (ps :&: Flip (ps' :<: Module n mg x))

-- b : Bool signifies if Middle is allowed
type PZ b = LStar (PZStep b)

data PZStep (b :: Bool)(v :: World) (w :: World) where
  Param   :: Naming -> Extended v w -> TERM v -> PZStep b v w
  Module  :: Naming -> Maybe (Ex Global) -> ProofState False w ->
             PZStep b w w
  -- middle is a back pointer
  Middle  :: Naming -> LongName -> ProofState False w -> PZStep True w w

data PTip (w :: World) where
  P0   :: PTip w
  PDef :: Maybe (TERM w) -> TERM w -> PTip w
  PRaw :: Sub RawModule -> PTip w
  
data Resolution (w :: World) where
  RParam :: Ref w -> Resolution w
  RGlob  :: Global n -> Bwd (TERM w) -> Resolution w

instance Weakenable Resolution

stripParams :: PZ True v w -> Bwd (TERM w)
stripParams = stripParams' id where
  stripParams' :: (TERM u -> TERM w) -> PZ True v u -> Bwd (TERM w)
  stripParams' w L0                    = B0
  stripParams' w (pz :<: Param y e _)  = stripParams' (w . extwk e) pz :< w (En (P (extrRef e)))
  stripParams' w (pz :<: Module _ _ _) = stripParams' w pz
  stripParams' w (pz :<: Middle _ _ _) = stripParams' w pz

data Lifting (w :: World) where
  Lifting :: LStar KStep Zero n -> VarOp Zero n w W0 -> Lifting w

lifter :: PZ True W0 w -> Lifting w
lifter L0 = Lifting L0 IdVO
lifter (ps :<: Param x e ty) = case lifter ps of
  Lifting del rho -> Lifting (del :<: KS (varOp rho ty)) (Abst rho e)
lifter (ps :<: Module _ _ _) = lifter ps
lifter (ps :<: Middle _ _ _) = lifter ps

eqNameStep :: Naming -> NameStep -> Either NameStep ()
eqNameStep y xi@(x,i) = case (x == y, i) of
   (True,  0) -> Right ()
   (True,  i) -> Left (x,i-1)
   (False, _) -> Left xi 

bake :: PZ True v w -> Vec Naming n -> RawTm -> TC (Tm (Syn n)) w
bake ps ns (RawAtom x)                               = Yes (Atom x)
bake ps ns (RawList []              Nothing)         = Yes (Atom "")
bake ps ns (RawList []              (Just (_ := t))) = bake ps ns t
bake ps ns (RawList ((_ := t) : ts) mt) =
  bake ps ns t               >>>= \ t ->
  bake ps ns (RawList ts mt) >>>= \ ts ->
  Yes (t :& ts)
bake ps ns (RawLam x (_ := t))                       = bake ps (VCons x ns) t >>>= \ t -> Yes (Lam t)
bake ps ns (RawEn (_ := hd) tl)                      =
  map (bake ps ns . subproj) tl >>>== boil ps ns hd
bake ps ns (RawComm (_ := t) _)                      = bake ps ns t -- should deal with the comments...

boil :: PZ True v w -> Vec Naming n -> RawHd -> [Tm (Syn n) w] -> TC (Tm (Syn n)) w
boil ps ns (RawTy (_ := t) (_ := ty)) ts = bake ps ns t >>>= \ t -> bake ps ns ty >>>= \ ty ->
  Yes (En (foldl (:$) (t ::: ty) ts))
boil ps ns (RawVar (x,xs)) ts = case blah x ns of
  Left x  -> resolve (x,xs) ps >>>= \ res -> case res of
      RParam x   -> Yes (En (foldl (:$) (P x) ts))
      RGlob f tz -> case globKind f of
        (sz :=> _) -> case help sz (fmap vclosed tz <>> ts) of
          Nothing -> No
          Just (g,ts) -> Yes (En (foldl (:$) (f :% g) ts))
          where
          help :: LStar KStep Zero m -> [Tm (Syn n) w] -> Maybe (Env (Syn n) m w, [Tm (Syn n) w])
          help L0 ts = return (E0, ts)
          help (sz :<: KS _) ts = do
            (g,t:ts) <- help sz ts
            return (ES g t,ts)
  Right i -> if null xs then Yes (En (foldl (:$) (V i) ts)) else No

blah :: NameStep -> Vec Naming n -> Either NameStep (Fin n)
blah x VNil = Left x
blah x (VCons y ys) = case eqNameStep y x of
  Left x   -> fmap FSuc $ blah x ys
  Right () -> Right FZero

resolve :: RawLongName -> PZ True v w -> TC Resolution w
resolve (xi,nsteps) = lookOut xi
  where 
  lookOut :: NameStep -> PZ True v w -> TC Resolution w
  lookOut xi L0                                        = No
  lookOut xi (pz :<: Param  y e _)                       =
    case eqNameStep y xi of
       -- found it!
      Right _ | null nsteps -> Yes $ RParam (extrRef e)
              -- looking for module components inside a param
              | otherwise   -> No
       -- carry on looking
      Left xi -> extwk e $ lookOut xi pz
  lookOut xi (pz :<: Module y mglob ((pz',_) :!-: _)) =
    case eqNameStep y xi of
      -- found the 'corner'; look inside
      Right _ -> case lookInside nsteps mglob pz' of 
        (Just (Wit glob)) -> Yes (RGlob glob (stripParams pz))
        _                 -> No
      -- carry on looking
      Left xi -> lookOut xi pz
  lookOut i (pz :<: Middle _ _ _)                = lookOut i pz

  lookInside :: [NameStep] -> Maybe (Ex Global) -> PZ False v w ->
                Maybe (Ex Global)
  lookInside []           mglob pz = mglob -- found it!
  lookInside (xi : xs) _     pz = lookInside' xi pz
    where
    lookInside' :: NameStep -> PZ False v w -> Maybe (Ex Global)
    lookInside' _ L0 = Nothing
    lookInside' xi (pz :<: Param _ _ _) = lookInside' xi pz
      -- parameters are not in scope
    lookInside' xi (pz :<: Module y mglob ((pz',_) :!-: _)) =
      case eqNameStep y xi of
        -- found the next step
        Right _ -> lookInside xs mglob pz'
        -- carry on looking
        Left xi -> lookInside' xi pz

testRig :: String -> String
testRig s = ugly 0 (ambulando ((L0,supply0) :!-: PRaw (snd (head (parses (sub bigMod) (headline (layout s)))))))

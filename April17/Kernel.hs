--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances,
             TypeFamilies, StandaloneDeriving, DeriveFoldable,
             DeriveFunctor, DeriveTraversable, FlexibleContexts #-}
module Kernel where

import Prelude hiding ((^^))
import Utils
import OPE
import Data.Void
import Control.Monad


------------------------------------------------------------------------------
-- Syntactic Sorts
------------------------------------------------------------------------------

data Sort = Chk | Syn | Pnt

{- TODO report
    • Type constructor ‘Sorts’ cannot be used here
        (Perhaps you intended to use TypeInType)
    • In the kind ‘Sorts -> Sorts -> *’
-}
type Sorts = Bwd Sort


------------------------------------------------------------------------------
-- Terms (in normal form)
------------------------------------------------------------------------------

data Term :: Sort -> (Bwd Sort -> *) where
  Star :: Unit gamma -> Term Chk gamma
  Pi :: (Term Chk  ><  Syn !- Term Chk) gamma -> Term Chk gamma
  Lam :: (Syn !- Term Chk) gamma -> Term Chk gamma
  E :: Term Syn gamma -> Term Chk gamma
  V :: This Syn gamma -> Term Syn gamma
  App :: (Term Syn >< Term Chk) gamma -> Term Syn gamma
  Hole :: Meta delta s -> Env delta gamma -> Term s gamma

data Meta delta s = Meta {metaSort :: Sorty s
                         ,metaName :: [String]
                         ,metaContext :: Context delta
                         ,metaInfo :: Info s ^ delta
                         }

data Env :: Bwd Sort -> Bwd Sort -> * where
  E0 :: Unit gamma -> Env B0 gamma
  ES :: (Env delta >< Instance s) gamma -> Env (delta :< s) gamma

-- what an environment will use to instantiate a parameter of a given sort
data Instance :: Sort -> Bwd Sort -> * where
  IS :: Term Chk gamma -> Instance Syn gamma
  IP :: Term Pnt gamma -> Instance Pnt gamma


------------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------------

data Context :: Bwd Sort -> * where
  C0 :: Context B0
  (:\) :: Sorted gamma =>
          Context gamma -> (Sorty s , String , Info s ^ gamma) ->
          Context (gamma :< s)

-- what the context will tell you about a parameter of a given sort
type family Info (s :: Sort) :: Bwd Sort -> * where
  Info Syn = Term Chk -- the type of the variable
  Info Chk = Got Void
  Info Pnt = Unit -- nothing else to know about a coordinate

lookupC :: Context gamma -> (B0 :< s) <= gamma -> Info s ^ gamma
lookupC (_ :\ (_,_,i)) (OS _) = wk i
lookupC (gamma :\ _) (O' r) = wk (lookupC gamma r)
  

------------------------------------------------------------------------------
-- derived constructors for thinned terms
------------------------------------------------------------------------------

star :: Sorted gamma => Term Chk ^ gamma
star = Star Void :^ oN

freshVar :: Sorted gamma => Term Chk ^ (gamma :< Syn)
freshVar = E (V It) :^ OS oN


------------------------------------------------------------------------------
-- substitution is hereditary 
------------------------------------------------------------------------------

class Sub (f :: Bwd Sort -> *) where
  sub' :: f gamma' ->
          Select gamma' theta ^ delta -> ALL (Radical delta) theta ->
          f ^ delta
  solve :: Sorted gamma =>
           f gamma -> Meta delta s -> Instance s ^ delta -> f ^ gamma

sub :: Sub f =>
       f gamma' -> Select gamma' theta ^ delta -> ALL (Radical delta) theta ->
       f ^ delta
sub f (s :^ r) A0 = case missAll s of Refl -> f :^ r
sub f s gamma = sub' f s gamma

data Radical :: Bwd Sort -> Sort -> * where
  (:::) :: Term Chk ^ delta -> Term Chk ^ delta -> Radical delta Syn
  RP    :: Term Pnt ^ delta -> Radical delta Pnt
infixr 3 :::

radTm :: Radical gamma Syn -> Term Chk ^ gamma
radTm (t ::: _) = t

mkRadical :: Sorty s -> Instance s ^ gamma -> Info s ^ gamma -> Radical gamma s
mkRadical Syny (IS t :^ r) _T = t :^ r ::: _T
mkRadical Pnty (IP p :^ r) _  = RP $ p :^ r

data Subst :: Bwd Sort -> Bwd Sort -> * where

-- We substitute a radical for a variable. Radicals can cause computation.
instance Sub (Term Chk) where
  sub' (Pi _ST) xr s = mapIx Pi $ sub' _ST xr s
  sub' (Lam t)  xr s = mapIx Lam $ sub' t xr s
  sub' (E e)    xr s = stop $ subSyn e xr s

  solve (Pi _ST) m s = mapIx Pi $ solve _ST m s
  solve (Lam t)  m s = mapIx Lam $ solve t m s
  solve (E e)    m s = stop $ solveSyn e m s

-- substitution in a Term Syn can radicalise it
type Activist s delta = Either (Radical delta s) (Term s ^ delta)

subSyn :: Term Syn gamma' ->
          Select gamma' theta ^ delta -> ALL (Radical delta) theta ->
          Activist Syn delta
subSyn t (s :^ r) A0 = case missAll s of Refl -> Right $ t :^ r
subSyn (V It) (Hit None :^ r) (AS A0 s) = Left s
subSyn (App (Pair c f a)) (z :^ r) theta = case hits z c of
    Hits z0 z1 ctheta cgamma ->
      let theta0 = discard (lCoP ctheta) theta
          theta1 = discard (rCoP ctheta) theta
          r0 = r -<=- lCoP cgamma
          r1 = r -<=- rCoP cgamma
      in radicalAct (subSyn f (z0 :^ r0) theta0) (sub a (z1 :^ r1) theta1)

subSyn (Hole meta gamma) xr s = Right (mapIx (Hole meta) (sub gamma xr s))

solveSyn :: Sorted gamma =>
            Term Syn gamma -> Meta theta s -> Instance s ^ theta ->
            Activist Syn gamma 
solveSyn (V It) _ _ = Right (V It :^ oI)
solveSyn (App (Pair c f a)) m s = sortedCoP c $
  radicalAct (thinActivist (solveSyn f m s) (lCoP c))
             (solve a m s ^^ rCoP c)
solveSyn (Hole m' theta) m@(Meta _ _ _Theta (_T :^ _R)) s@(t :^ r) =
  case (metaEq m' m , solve theta m s, t) of
    (Just (Refl,Refl), theta :^ r' , IS t) ->
      sortedObj r $ sortedObj _R $ sortedObj r' $ Left $
        let fs = zippy _Theta (theta :^ r')
        in sub t (hitter :^ oN) (discard r fs) :::
             sub _T (hitter :^ oN) (discard _R fs)
    (Nothing, theta :^ r, _) -> Right $ Hole m' theta :^ r

zippy :: Context theta -> Env theta ^ gamma -> ALL (Radical gamma) theta
zippy C0 (E0 Void :^ r) = A0
zippy (_Theta :\ (s,_,_I :^ _R)) (ES p :^ r) = p :^ r >^< \theta i ->
  let fs = zippy _Theta theta
  in sortedObj _R $ sortedObj r $
       AS fs (mkRadical s i (subInfo s $ sub _I (hitter :^ oN) (discard _R fs)))

subInfo :: Sorty s -> Holds (Sub (Info s))
subInfo Syny t = t
subInfo Chky t = t
subInfo Pnty t = t

thinRadical :: Radical delta s -> delta <= delta' -> Radical delta' s
thinRadical (t ::: _T) r = t ^^ r ::: _T ^^ r
thinRadical (RP p) r = RP (p ^^ r)
                                          
thinActivist :: Activist s delta -> delta <= delta' -> Activist s delta'
thinActivist  (Right t) r = Right (t ^^ r)
thinActivist  (Left f) r = Left (thinRadical f r)

radicalAct :: Activist Syn delta -> Term Chk ^ delta -> Activist Syn delta
radicalAct (Left r)  a = Left (app r a)
radicalAct (Right e) a = Right (mapIx App (pair e a))

-- we can always stop if a Term Chk is wanted, stripping the spent type
stop :: Activist Syn delta -> Term Chk ^ delta
stop (Left t) = radTm t
stop (Right e) = mapIx E e

instance Sub Unit where
  sub' Void (None :^ r) A0 = Void :^ r
  solve Void _ _ = Void :^ oN
  
instance Sub (Got Void) where
  sub' (Got z) = Data.Void.absurd z
  solve (Got z) = Data.Void.absurd z

-- structural rule for pairing
instance (Sub f , Sub g) => Sub (f >< g) where
  sub' (Pair c f g) (z :^ r) theta = case hits z c of
    Hits z0 z1 ctheta cgamma ->
      let theta0 = discard (lCoP ctheta) theta
          theta1 = discard (rCoP ctheta) theta
          r0 = r -<=- lCoP cgamma
          r1 = r -<=- rCoP cgamma
      in pair (sub f (z0 :^ r0) theta0) (sub g (z1 :^ r1) theta1)

  solve (Pair c f g) m s = sortedCoP c $
    pair (solve f m s ^^ lCoP c) (solve g m s ^^ rCoP c)

-- structural rule for binding
instance Sub f => Sub (s !- f) where
  sub' (K f) xr theta = mapIx K $ sub' f xr theta
  sub' (L y f) (x :^ r) theta =
    abstract y (sub' f (Miss x :^ OS r) (mapIx radWk theta))

  solve (K f) m s = mapIx K $ solve f m s
  solve (L y f) m s = abstract y (solve f m s)

radWk :: Radical gamma t -> Radical (gamma :< s) t
radWk (t ::: _T) = wk t ::: wk _T

instance Sub (Env delta) where
  sub' (ES p) xr s = mapIx ES (sub' p xr s)

  solve (ES p) m s = mapIx ES (solve p m s)

instance Sub (Instance s) where
  sub' (IS t) xr s = mapIx IS (sub' t xr s)
  sub' (IP p) xr s = mapIx IP (sub' p xr s)

  solve (IS t) m s = mapIx IS (solve t m s)
  solve (IP p) m s = mapIx IP (solve p m s)

instance Sub (Term Pnt) where
  sub' (Hole meta gamma) xr s = mapIx (Hole meta) (sub' gamma xr s)
  -- TODO worry here

  solve (Hole m' gamma) m s = mapIx (Hole m') (solve gamma m s)
  -- TODO worry a lot - what if m is m'?

------------------------------------------------------------------------------
-- computation is the elimination of radicals
------------------------------------------------------------------------------

app :: Radical delta Syn -> Term Chk ^ delta -> Radical delta Syn
app (f :^ r ::: Pi _ST :^ _R) s = _ST :^ _R >^< \ _S _T ->
  (case f of
    E e   -> mapIx (E . App) (pair (e :^ r) s)
    Lam t -> instantiate (t :^ r) (s ::: _S)
  ) ::: instantiate _T (s ::: _S)
  
instantiate :: (s !- Term Chk) ^ delta -> Radical delta s ->
               Term Chk ^ delta
instantiate (K t :^ r) _ = t :^ r
instantiate (L _ t :^ r) a = sortedObj r $ sub t (Hit misser :^ r) (AS A0 a)
                                  
------------------------------------------------------------------------------
-- environments of the unremarkable kind
------------------------------------------------------------------------------

data NameEnv :: Bwd Sort -> * -> * where
  N0 :: NameEnv B0 a
  NS :: NameEnv gamma a -> a -> NameEnv (gamma :< s) a

deriving instance Foldable (NameEnv gamma)
deriving instance Functor (NameEnv gamma)
deriving instance Traversable (NameEnv gamma)


------------------------------------------------------------------------------
-- Singletons for Sorts
------------------------------------------------------------------------------

data Sorty :: Sort -> * where
  Chky :: Sorty Chk
  Syny :: Sorty Syn
  Pnty :: Sorty Pnt

------------------------------------------------------------------------------
-- Equality testing
------------------------------------------------------------------------------

sortEq :: Sorty s -> Sorty s' -> Maybe (s == s')
sortEq Chky Chky = Just Refl
sortEq Syny Syny = Just Refl
sortEq Pnty Pnty = Just Refl
sortEq _    _    = Nothing

instance SyntaxEq (Term s) where
  eq (Star t) (Star t') = eq t t' 
  eq (Pi   t) (Pi   t') = eq t t'
  eq (Lam  t) (Lam  t') = eq t t'
  eq (E    t) (E    t') = eq t t'
  eq (V    t) (V    t') = eq t t'
  eq (App  t) (App  t') = eq t t'
  eq _        _         = fail "gotcha"

conSortEq :: Context delta -> Context delta' -> Maybe (delta == delta')
conSortEq C0 C0 = return Refl
conSortEq (delta :\ (s,_,_)) (delta' :\ (s',_,_)) = do
  Refl <- sortEq s s'
  Refl <- conSortEq delta delta'
  return Refl
conSortEq _ _ = error "we did a bad"

metaEq :: Meta delta s -> Meta delta' s' -> Maybe (delta == delta', s == s')
metaEq (Meta s n delta _) (Meta s' n' delta' _) = do
  guard (n == n')
  -- invariant: if the guard succeeds the rest should succeed, cos
  -- holes have unique names
  Refl <- sortEq s s'
  Refl <- conSortEq delta delta'
  return (Refl, Refl)

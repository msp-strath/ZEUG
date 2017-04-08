--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances,
             TypeFamilies, StandaloneDeriving, DeriveFoldable,
             DeriveFunctor, DeriveTraversable, FlexibleContexts,
             GeneralizedNewtypeDeriving #-}
module Kernel where

import Data.List
import Prelude hiding ((^^))
import Data.Void
import Data.Type.Equality((:~:)(Refl))
import Control.Monad
import Control.Newtype
import Data.Monoid

import Utils
import OPE


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

newtype LongName = LongName {longName :: [String]} deriving (Eq,Monoid)

instance Show LongName where
  show (LongName xs) = intercalate "/" xs

data Meta delta s = Sorted delta =>
                    Meta {metaSort :: Sorty s
                         ,metaName :: LongName
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

idEnv :: Context gamma -> Env gamma gamma
idEnv C0 = E0 Void
idEnv (_Gamma :\ (Syny,_,_)) =
  ES (Pair (C'S copL) (idEnv _Gamma) (IS (E (V It))))
idEnv (_Gamma :\ (Pnty,_,_)) = undefined -- FIXME
  

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
  update :: Sorted gamma => f gamma -> [Update] ->f ^ gamma

sub :: Sub f =>
       f gamma' -> Select gamma' theta ^ delta -> ALL (Radical delta) theta ->
       f ^ delta
sub f (s :^ r) A0 = case missAll s of Refl -> f :^ r
sub f s gamma = sub' f s gamma

data Updata :: Bwd Sort -> Sort -> * where
  Solve :: Instance s ^ delta  -> Updata delta s
  Renew :: Meta delta s        -> Updata delta s

data Update :: * where
  (:=>) :: Meta delta s -> Updata delta s -> Update

updateMe :: Meta delta s -> Update -> Maybe (Updata delta s)
updateMe (Meta s x _Theta _) (Meta s' x' _Theta' _ :=> u) = do
  guard (x == x')
  Refl <- sortEq s s'
  Refl <- conSortEq _Theta _Theta'
  return u

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

  update (Star v) us = mapIx Star $ update v us
  update (Pi _ST) us = mapIx Pi   $ update _ST us
  update (Lam t)  us = mapIx Lam  $ update t us
  update (E e)    us = stop $ updateSyn e us

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

updateSyn :: Sorted gamma => Term Syn gamma -> [Update] ->
             Activist Syn gamma 
updateSyn (V It) _ = Right (V It :^ oI)
updateSyn (App (Pair c f a)) us = sortedCoP c $
  radicalAct (thinActivist (updateSyn f us) (lCoP c))
             (update a us ^^ rCoP c)
updateSyn (Hole m@(Meta _ _ _Theta _T) theta) us =
  case (ala' First foldMap (updateMe m) us, update theta us) of
    (Nothing                   , theta :^ r) -> Right $ Hole m theta :^ r
    (Just (Renew m)            , theta :^ r) -> Right $ Hole m theta :^ r
    (Just (Solve (IS t :^ r')) , theta :^ r) -> sortedObj r' $ Left $
      -- could abstract this pattern if it gets more use
      subRadical (t :^ r' ::: _T) (hitter :^ oN) (zippy _Theta (theta :^ r))

subRadical :: Radical gamma s -> Select gamma theta ^ delta ->
              ALL (Radical delta) theta -> Radical delta s
subRadical (t ::: _T) z theta = joinH (sub t z theta) ::: joinH (sub _T z theta)
subRadical (RP p)     z theta = RP (joinH (sub p z theta))

updateRadical :: Sorted gamma => Radical gamma s -> [Update] -> Radical gamma s
updateRadical (t ::: _T) us = joinH (update t us) ::: joinH (update _T us)
updateRadical (RP p)     us = RP (joinH (update p us))

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
  update Void _ = Void :^ oN
  
instance Sub (Got Void) where
  sub' (Got z) = Data.Void.absurd z
  update (Got z) = Data.Void.absurd z

instance Sub f => Sub ((^) f) where
  sub' (f :^ r) (z :^ r') theta = sortedObj r' $ case thickSelect r z of
    ThickSelect z rtheta rgamma ->
      sub f (z :^ r' -<=- rgamma) (discard rtheta theta) :^ oI
  update (f :^ r) us = sortedObj r $ update f us :^ r

-- structural rule for pairing
instance (Sub f , Sub g) => Sub (f >< g) where
  sub' (Pair c f g) (z :^ r) theta = case hits z c of
    Hits z0 z1 ctheta cgamma ->
      let theta0 = discard (lCoP ctheta) theta
          theta1 = discard (rCoP ctheta) theta
          r0 = r -<=- lCoP cgamma
          r1 = r -<=- rCoP cgamma
      in pair (sub f (z0 :^ r0) theta0) (sub g (z1 :^ r1) theta1)

  update (Pair c f g) us = sortedCoP c $
    pair (update f us ^^ lCoP c) (update g us ^^ rCoP c)

-- structural rule for binding
instance Sub f => Sub (s !- f) where
  sub' (K f) xr theta = mapIx K $ sub' f xr theta
  sub' (L y f) (x :^ r) theta =
    abstract y (sub' f (Miss x :^ OS r) (mapIx radWk theta))

  update (K f) us = mapIx K $ update f us
  update (L y f) us = abstract y (update f us)

radWk :: Radical gamma t -> Radical (gamma :< s) t
radWk (t ::: _T) = wk t ::: wk _T

instance Sub (Env delta) where
  sub' (ES p) xr s = mapIx ES (sub' p xr s)

  update (E0 v) us = mapIx E0 (update v us)
  update (ES p) us = mapIx ES (update p us)

instance Sub (Instance s) where
  sub' (IS t) xr s = mapIx IS (sub' t xr s)
  sub' (IP p) xr s = mapIx IP (sub' p xr s)

  update (IS t) us = mapIx IS (update t us)
  update (IP p) us = mapIx IP (update p us)

instance Sub (Term Pnt) where
  sub' (Hole meta gamma) xr s = mapIx (Hole meta) (sub' gamma xr s)
  -- TODO worry here

  update (Hole m' gamma) us = mapIx (Hole m') (update gamma us)
  -- TODO worry a lot - what if m is m'?

updateContext :: Context gamma -> [Update] ->
                 (Sorted gamma => Context gamma -> t) -> t
updateContext C0                   us t = t C0
updateContext (gamma :\ (s, x, i)) us t = subInfo s $
  updateContext gamma us $ \ gamma -> t (gamma :\ (s, x, joinH (update i us)))


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

sortEq :: Sorty s -> Sorty s' -> Maybe (s :~: s')
sortEq Chky Chky = Just Refl
sortEq Syny Syny = Just Refl
sortEq Pnty Pnty = Just Refl
sortEq _    _    = Nothing

instance SyntaxEq (Term s) where
  eq (Star       t) (Star        t') = eq t t' 
  eq (Pi         t) (Pi          t') = eq t t'
  eq (Lam        t) (Lam         t') = eq t t'
  eq (E          t) (E           t') = eq t t'
  eq (V          t) (V           t') = eq t t'
  eq (App        t) (App         t') = eq t t'
  eq (Hole m theta) (Hole m' theta') = do
    (Refl,Refl) <- metaEq m m'
    eq theta theta'
  eq _              _                = fail "gotcha"

instance SyntaxEq (Env gamma) where
  eq (E0 v) (E0 v') = eq v v'
  eq (ES p) (ES p') = eq p p'

instance SyntaxEq (Instance s) where
  eq (IS t) (IS t') = eq t t'
  eq (IP p) (IP p') = eq p p'
  
conSortEq :: Context delta -> Context delta' -> Maybe (delta :~: delta')
conSortEq C0 C0 = return Refl
conSortEq (delta :\ (s,_,_)) (delta' :\ (s',_,_)) = do
  Refl <- sortEq s s'
  Refl <- conSortEq delta delta'
  return Refl
conSortEq _ _ = error "we did a bad"

metaEq :: Meta delta s -> Meta delta' s' -> Maybe (delta :~: delta', s :~: s')
metaEq (Meta s n delta _) (Meta s' n' delta' _) = do
  guard (n == n')
  -- invariant: if the guard succeeds the rest should succeed, cos
  -- holes have unique names
  Refl <- sortEq s s'
  Refl <- conSortEq delta delta'
  return (Refl, Refl)

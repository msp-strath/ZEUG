--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances,
             TypeFamilies, StandaloneDeriving, DeriveFoldable,
             DeriveFunctor, DeriveTraversable #-}
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
  sub :: f gamma' -> Select gamma' s ^ delta -> Radical s delta -> f ^ delta
  solve :: f gamma -> Meta delta s -> Instance s ^ delta -> f ^ gamma
    
data Radical :: Sort -> Bwd Sort -> * where
  (:::) :: Term Chk ^ delta -> Term Chk ^ delta -> Radical Syn delta
  RP    :: Term Pnt ^ delta -> Radical Pnt delta
infixr 3 :::

radTm :: Radical Syn gamma -> Term Chk ^ gamma
radTm (t ::: _) = t

mkRadical :: Sorty s -> Instance s ^ gamma -> Info s ^ gamma -> Radical s gamma
mkRadical Syny (IS t :^ r) _T = t :^ r ::: _T
mkRadical Pnty (IP p :^ r) _  = RP $ p :^ r

-- We substitute a radical for a variable. Radicals can cause computation.
instance Sub (Term Chk) where
  sub (Pi _ST) xr s = mapIx Pi $ sub _ST xr s
  sub (Lam t)  xr s = mapIx Lam $ sub t xr s
  sub (E e)    xr s = stop $ subSyn e xr s

  solve (Pi _ST) m s = mapIx Pi $ solve _ST m s
  solve (Lam t)  m s = mapIx Lam $ solve t m s
  solve (E e)    m s = stop $ solveSyn e m s

-- substitution in a Term Syn can radicalise it
type Activist s delta = Either (Radical s delta) (Term s ^ delta)

subSyn :: Term Syn gamma' ->
          Select gamma' s ^ delta -> Radical s delta ->
          Activist Syn delta
subSyn (V It) (Top :^ r) s = Left s
subSyn (App (Pair c f a)) (z :^ r) s = case hits c z of
    HRight  y c -> Right . mapIx App $  -- right hit means no radical
      pair (f :^ r -<=- lCoP c) (sub a (y :^ r -<=- rCoP c) s)
      -- left hit means risk of radical
    HLeft x   c ->
      radicalAct (subSyn f (x :^ r -<=- lCoP c) s) (a :^ r -<=- rCoP c)
    HBoth x y c ->
      radicalAct (subSyn f (x :^ r -<=- lCoP c) s)
                 (sub a (y :^ r -<=- rCoP c) s)

subSyn (Hole meta gamma) xr s = Right (mapIx (Hole meta) (sub gamma xr s))

solveSyn :: Term Syn gamma -> Meta delta s -> Instance s ^ delta ->
            Activist Syn gamma 
solveSyn (V It) _ _ = Right (V It :^ oI)
solveSyn (App (Pair c f a)) m s =
  radicalAct (thinActivist (solveSyn f m s) (lCoP c))
             (solve a m s ^^ rCoP c)
solveSyn (Hole m' delta) m s = case (metaEq m' m , solve delta m s) of
  (Just (Refl,Refl), delta) -> 
    Left $ subs (mkRadical Syny s (metaInfo m)) (metaContext m) delta
  (Nothing, delta :^ r) -> Right $ Hole m' delta :^ r

subs :: Radical s delta -> Context delta -> Env delta ^ gamma -> Radical s gamma
subs f C0 (E0 Void :^ r) = thinRadical f r
subs f (_Delta :\ (_,_,_I)) (ES p :^ r) = p :^ r >^< \delta i ->
  undefined

thinRadical :: Radical s delta -> delta <= delta' -> Radical s delta'
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

-- structural rule for pairing
instance (Sub f , Sub g) => Sub (f >< g) where
  sub (Pair c f g) (z :^ r) s = case hits c z of
    HLeft  x c -> pair (sub f (x :^ r -<=- lCoP c) s) (g :^ r -<=- rCoP c)
    HRight y c -> pair (f :^ r -<=- lCoP c) (sub g (y :^ r -<=- rCoP c) s)
    HBoth  x y c ->
      pair (sub f (x :^ r -<=- lCoP c) s) (sub g (y :^ r -<=- rCoP c) s)

  solve (Pair c f g) m s = pair (solve f m s ^^ lCoP c) (solve g m s ^^ rCoP c)

-- structural rule for binding
instance Sub f => Sub (s !- f) where
  sub (K f) xr s = mapIx K $ sub f xr s
  sub (L y f) (x :^ r) s = abstract y (sub f (Pop x :^ OS r) (radWk s))

  solve (K f) m s = mapIx K $ solve f m s
  solve (L y f) m s = abstract y (solve f m s)

radWk :: Radical t gamma -> Radical t (gamma :< s)
radWk (t ::: _T) = wk t ::: wk _T

instance Sub (Env delta) where
  sub (ES p) xr s = mapIx ES (sub p xr s)

  solve (ES p) m s = mapIx ES (solve p m s)

instance Sub (Instance s) where
  sub (IS t) xr s = mapIx IS (sub t xr s)
  sub (IP p) xr s = mapIx IP (sub p xr s)

  solve (IS t) m s = mapIx IS (solve t m s)
  solve (IP p) m s = mapIx IP (solve p m s)

instance Sub (Term Pnt) where
  sub (Hole meta gamma) xr s = mapIx (Hole meta) (sub gamma xr s)
  -- TODO worry here

  solve (Hole m' gamma) m s = mapIx (Hole m') (solve gamma m s)
  -- TODO worry a lot - what if m is m'?

------------------------------------------------------------------------------
-- computation is the elimination of radicals
------------------------------------------------------------------------------

app :: Radical Syn delta -> Term Chk ^ delta -> Radical Syn delta
app (f :^ r ::: Pi _ST :^ _R) s = _ST :^ _R >^< \ _S _T ->
  (case f of
    E e   -> mapIx (E . App) (pair (e :^ r) s)
    Lam t -> instantiate (t :^ r) (s ::: _S)
  ) ::: instantiate _T (s ::: _S)
  
instantiate :: (s !- Term Chk) ^ delta -> Radical s delta ->
               Term Chk ^ delta
instantiate (K t :^ r) _ = t :^ r
instantiate (L _ t :^ r) a = sub t (Top :^ r) a
                                  
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

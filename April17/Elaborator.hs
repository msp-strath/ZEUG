{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures, TypeFamilies #-}
module Elaborator where

import Data.Type.Equality((:~:)(Refl))
import Control.Monad.RWS

import Utils
import Raw
import OPE
import Kernel
import DefEq
import ProofState

data Elaborator :: (Bwd Sort -> *) -> (Bwd Sort -> *) where
  Reject :: String -> Elaborator p gamma
  Under :: (Sorty s, String, Info s ^ gamma) ->
           ELAB (f ^ (gamma :< s)) (gamma :< s) ->
           Elaboratkey ((s !- f) ^ gamma) gamma
  Fetch :: Sorty s -> String -> Elaboratkey (Fetching gamma s) gamma
--  Context :: Elaborator (Context gamma @= gamma) gamma
  DefEq :: Term Chk ^ gamma -> Term Chk ^ gamma -> Term Chk ^ gamma ->
           Elaboratkey () gamma
  Query :: String -> Term Chk ^ gamma ->
           Elaboratkey (Term Chk ^ gamma) gamma
  Define :: Radical gamma Syn -> Elaboratkey (Unit ^ gamma) gamma

data Fetching :: Bwd Sort -> Sort -> * where
  FDefn  :: Defn theta s -> Fetching gamma s
  FHole  :: Meta theta s -> Fetching gamma s
  FCtxt  :: (This s ^ gamma, Info s ^ gamma) -> Fetching gamma s

type Elaboratkey a gamma = Elaborator (a @= gamma) gamma
type ELAB a gamma = Prog Elaborator (a @= gamma) gamma

chkBind :: Sorted gamma =>
           Sorty s -> Info s ^ gamma ->
           (s !- Term Chk) ^ gamma -> Raw c ->
           ELAB ((s !- Term Chk) ^ gamma) gamma
chkBind s _S _T (RB _ x t) =
  cmd $ Under (s , x , _S) $ chk (dive _T) t
chkBind s _S _T t =
  cmd $ Under (s , "" , _S) $ chk (dive _T) t

chk :: Sorted gamma =>
       Term Chk ^ gamma -> Raw c ->
       ELAB (Term Chk ^ gamma) gamma
chk _T (RA _ ('?':xs)) = cmd $ Query xs _T
chk (Star Void :^ r) (RA _ "Type") = raturn $ Star Void :^ r 
chk (Star Void :^ r) (RC (RA _ "Pi") (_S :-: Only _T)) = 
  chk star _S @>= \_S -> 
  chkBind Syny _S (mapIx K star) _T @>= \_T ->
  raturn $ mapIx Pi (pair _S _T )
chk (Pi _ST :^ r) (RC (RA _ "\\") (Only t)) = _ST :^ r >^< \ _S _T ->
  chkBind Syny _S _T t @>= \t -> 
  raturn $ mapIx Lam t
chk _T t = 
  syn t Nothing @>= \(s ::: _S) -> 
  cmd (DefEq star _S _T) @>
  raturn s

syn :: Sorted gamma => Raw c -> Maybe (NEL (Raw c)) ->
       ELAB (Radical gamma Syn) gamma
syn (RC t (RA _ ":" :-: Only _T)) rs =
  chk star _T @>= \_T -> 
  chk _T t @>= \t -> 
  spine (t ::: _T) rs
syn (RA _ x) rs =
  cmd (Fetch Syny x) @>= \ f -> case f of
    FCtxt (x , _S) -> spine (mapIx (E . V) x ::: _S) rs
    FHole m@(Meta Syny _ _Theta _T) ->
      params _Theta rs @>= \ (theta :^ r, sbst, rs) ->
      spine (E (Hole m theta) :^ r ::: joinH (sub _T (hitter :^ oN) sbst)) rs
    FDefn m@(Defn Syny _ _Theta tT) ->
      params _Theta rs @>= \ (_, sbst, rs) ->
      spine (subRadical tT (hitter :^ oN) sbst) rs
syn (RC f as) bs = syn f (Just (nconc as bs))
syn _ _ = cmd $ Reject "raised eyebrow"

spine :: Sorted gamma => Radical gamma Syn ->
         Maybe (NEL (Raw c)) -> ELAB (Radical gamma Syn) gamma
spine h Nothing = raturn h
spine h@(f ::: Pi _ST :^ r) (Just (s :- rs)) = _ST :^ r >^< \ _S _T -> 
  chk _S s @>= \s ->
  spine (app h s) rs
spine _ _ = cmd $ Reject "raised eyebrow"

params :: Sorted gamma => Context theta -> Maybe (NEL (Raw c)) ->
          ELAB ( Env theta ^ gamma          -- for a Hole
               , ALL (Radical gamma) theta  -- for substitution
               , Maybe (NEL (Raw c))        -- unconsumed
               ) gamma
params C0 rs = raturn (E0 Void :^ oN, A0, rs)
params (_Theta :\ (s, _, _I)) rs =
  params _Theta rs @>= \ (theta, sbst, rs) ->
  case rs of
    Nothing        -> cmd $ Reject "Underinstantiation!"
    Just (r :- rs) -> case s of
      Syny ->
        let _T = joinH (sub _I (hitter :^ oN) sbst)
        in chk _T r @>= \ t ->
           raturn (mapIx ES (pair theta (mapIx IS t)), AS sbst (t ::: _T), rs)
      Pnty -> cmd $ Reject "We can't see the point yet!"
        -- FIXME
        

define :: Sorted gamma => Raw c -> ELAB (Unit ^ gamma) gamma
define (RC (RA _ "=") (Only t)) =
  syn t Nothing @>= \ t ->
  cmd (Define t)
define (RC _S (Only (RB _ x t))) =
  chk star _S @>= \ _S ->
  cmd (Under (Syny, x, _S) (define t)) @>
  raturn (Void :^ oN)
define _ = cmd $ Reject "I didn't think much of that definition"


------------------------------------------------------------------------------
-- Implementation of Elaborator Interface
------------------------------------------------------------------------------

type Elab gamma =
  RWST (ProofState, Context gamma, LongName) [Entity] Int Maybe

elab :: Sorted gamma => ELAB a gamma -> Elab gamma a
elab (RET (At a)) = return a
elab (DO (Reject s) _) = fail s
elab (DO (Under b@(_,x,_) p) k) = do
  (ps, gamma, y) <- ask
  i <- get
  (t, i', w) <- lift $ runRWST (elab p) (ps, gamma :\ b, y) i
  tell w
  put i'
  elab (k RET (At (abstract x t)))
elab (DO (Fetch s x) k) = do
    (ps@(Cur ez _ _), gamma, _) <- ask
    let   (x', h) = parseName ps x
          glo B0 = Nothing
          glo (ez :< EHole m) | h && metaName m == x' = do
            Refl <- sortEq (metaSort m) s
            return (FHole m)
          glo (ez :< EDefn m) | not h && defnName m == x' = do
            Refl <- sortEq (defnSort m) s
            return (FDefn m)
          glo (ez :< _) = glo ez
          fetch :: Sorty s -> Context gamma ->
                   Maybe (This s ^ gamma, Info s ^ gamma)
          fetch s C0 = Nothing
          fetch s (gamma :\ (s',y,i :^ r)) =
            if x == y then
              do Refl <- sortEq s s'
                 return $ (It :^ OS oN, i :^ O' r)
            else
              do (x :^ r, i :^ r') <- fetch s gamma
                 return $ (x :^ O' r, i :^ O' r')
    case fetch s gamma of
      Just a  -> elab (k RET (At (FCtxt a)))
      Nothing -> case glo ez of
        Just f  -> elab (k RET (At f))
        Nothing -> fail ("Can't find " ++ x)
elab (DO (DefEq _T t t') k) = do
    (ps, gamma, y) <- ask
    lift $ defEq gamma _T t t'
    elab (k RET (At ()))
elab (DO (Query x _T) k) = do
  (ps, gamma, y) <- ask
  i <- get
  put (i + 1)
  let m = Meta Syny (mappend y (LongName [show i])) gamma _T
  tell [EHole m]
  elab (k RET (At (E (Hole m (idEnv gamma)) :^ oI)))
elab (DO (Define tT) k) = do
  (ps, gamma, y) <- ask
  tell [EDefn (Defn Syny y gamma tT)]
  elab (k RET (At (Void :^ oN)))

tryElab :: Sorted gamma => (ProofState, Context gamma, LongName) ->
           ELAB a gamma -> Maybe (a, ProofState)
tryElab stuff@(Cur bef u aft, _, _) p = do
  (a, _, w) <- runRWST (elab p) stuff 0
  let (ez, es) = fishFace B0 w
  return (a, Cur (bef +<+ ez) u (es ++ aft))

fishFace :: Bwd Entity -> [Entity] -> (Bwd Entity, [Entity])
fishFace ez []               = (ez, [])
fishFace ez es@(EHole _ : _) = (ez, es)
fishFace ez (e : es)         = fishFace (ez :< e) es


-- :l Elaborator Render
-- :m Elaborator Render Raw OPE Kernel
-- render N0 <$> (chk C0 (Star Void :^ OZ) =<< rawString "Pi Type X. Pi X x. X")
-- let Just idtype = (chk C0 (Star Void :^ OZ) =<< rawString "Pi Type X. Pi X x. X")
-- render N0 <$> (chk C0 idtype =<< rawString "\\ X. \\ x. x")

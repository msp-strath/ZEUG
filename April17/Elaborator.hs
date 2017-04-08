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
  Fetch :: Sorty s -> String ->
           Elaboratkey (This s ^ gamma, Info s ^ gamma) gamma
--  Context :: Elaborator (Context gamma @= gamma) gamma
  DefEq :: Term Chk ^ gamma -> Term Chk ^ gamma -> Term Chk ^ gamma ->
           Elaboratkey () gamma
  Query :: String -> Term Chk ^ gamma ->
           Elaboratkey (Term Chk ^ gamma) gamma
  Define :: Radical gamma Syn -> Elaboratkey (Unit ^ gamma) gamma

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
  syn t @>= \(s ::: _S) -> 
  cmd (DefEq star _S _T) @>
  raturn s

syn :: Sorted gamma => Raw c -> ELAB (Radical gamma Syn) gamma
syn (RA _ x) =
  cmd (Fetch Syny x) @>= \(x , _S) -> 
  raturn (mapIx (E . V) x ::: _S)
syn (RC t (RA _ ":" :-: Only _T)) =
  chk star _T @>= \_T -> 
  chk _T t @>= \t -> 
  raturn (t ::: _T)
syn (RC f as) =
  syn f @>= \f -> 
  spine f as
syn _ = cmd $ Reject "raised eyebrow"

spine :: Sorted gamma => Radical gamma Syn ->
         NEL (Raw c) -> ELAB (Radical gamma Syn) gamma
spine h@(f ::: Pi _ST :^ r) (s :- as) = _ST :^ r >^< \ _S _T -> 
  chk _S s @>= \s ->
  raturn (app h s)
spine _ _ = cmd $ Reject "raised eyebrow"

define :: Sorted gamma => Raw c -> ELAB (Unit ^ gamma) gamma
define (RC (RA _ "=") (Only t)) =
  syn t @>= \ t ->
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
    (ps, gamma, y) <- ask
    a <- lift $ fetch gamma s x
    elab (k RET (At a))
  where
  fetch :: Context gamma -> Sorty s -> String ->
           Maybe (This s ^ gamma, Info s ^ gamma)
  fetch C0 s x = Nothing
  fetch (gamma :\ (s',y,i :^ r)) s x =
    if x == y then
      do Refl <- sortEq s s'
         return $ (It :^ OS oN, i :^ O' r)
    else
      do (x :^ r, i :^ r') <- fetch gamma s x
         return  (x :^ O' r, i :^ O' r')    
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

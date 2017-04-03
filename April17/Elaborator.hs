{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures, TypeFamilies #-}
module Elaborator where

import Utils
import Raw
import OPE
import Kernel
import DefEq

chkBind :: Sorted gamma =>
           Context gamma -> Sorty s -> Info s ^ gamma ->
           (s !- Term Chk) ^ gamma -> Raw ->
           Maybe ((s !- Term Chk) ^ gamma)
chkBind gamma s _S _T (RB x t) =
  abstract x <$> chk (gamma :\ (s , x , _S)) (dive _T) t
chkBind gamma s _S _T t = abstract "" <$> chk (gamma :\ (s , "" , _S)) (dive _T) t

chk :: Sorted gamma =>
       Context gamma -> Term Chk ^ gamma -> Raw -> Maybe (Term Chk ^ gamma)
chk gamma (Star Void :^ r) (RA "Type") = return $ Star Void :^ r 
chk gamma star@(Star Void :^ r) (RC (RA "Pi") (_S :-: Only _T)) = do
  _S <- chk gamma star _S
  _T <- chkBind gamma Syny _S (K (Star Void) :^ r) _T
  return $ mapIx Pi (pair _S _T )
chk gamma (Pi (Pair c _S _T) :^ r) (RC (RA "\\") (Only t)) = do
  t <- chkBind gamma Syny (_S :^ r -<=- lCoP c) (_T :^ r -<=- rCoP c) t
  return $ mapIx Lam t
chk gamma _T t = do
  (s , _S) <- syn gamma t
  defEq gamma (Star Void :^ oN) _S _T
  return s

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

syn :: Sorted gamma =>
       Context gamma -> Raw -> Maybe (Term Chk ^ gamma , Term Chk ^ gamma)
syn gamma (RA x) = do
  (x , _S) <- fetch gamma Syny x
  return (mapIx (E . V) x, _S)

-- render N0 <$> (chk C0 (Star Void :^ OZ) =<< rawString "Pi Type X. Pi X x. X")
-- let Just idtype = (chk C0 (Star Void :^ OZ) =<< rawString "Pi Type X. Pi X x. X")
-- chk C0 idtype =<< rawString "\\ X. \\ x. x"

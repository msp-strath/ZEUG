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
chk gamma (Pi _ST :^ r) (RC (RA "\\") (Only t)) = _ST :^ r >^< \_S _T -> do
  t <- chkBind gamma Syny _S _T t
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
       Context gamma -> Raw ->
       Maybe (Term Chk ^ gamma , Term Chk ^ gamma) -- thing followed by its type 
syn gamma (RA x) = do
  (x , _S) <- fetch gamma Syny x
  return (mapIx (E . V) x, _S)
syn gamma (RC (RA "the") (_T :-: Only t)) = do
  _T <- chk gamma (Star Void :^ oN) _T
  t <- chk gamma _T t
  return (t , _T)
syn gamma (RC f as) = do
  f <- syn gamma f
  spine gamma f as
syn _ _ = fail "raised eyebrow"

spine :: Sorted gamma => Context gamma -> (Term Chk ^ gamma, Term Chk ^ gamma) ->
         NEL Raw -> Maybe (Term Chk ^ gamma , Term Chk ^ gamma)
spine gamma (f , Pi _ST :^ r) (a :- as) = _ST :^ r >^< \_S _T -> do
  a <- chk gamma _S a
  let faT' = (app (pair f a), instantiate _T a)
  case as of
    Nothing -> return faT'
    Just as -> spine gamma faT' as
spine gamma _ _ = fail "raised eyebrow"
         
-- render N0 <$> (chk C0 (Star Void :^ OZ) =<< rawString "Pi Type X. Pi X x. X")
-- let Just idtype = (chk C0 (Star Void :^ OZ) =<< rawString "Pi Type X. Pi X x. X")
-- chk C0 idtype =<< rawString "\\ X. \\ x. x"
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures #-}

module Render where

import Utils
import OPE
import Raw
import Kernel

type Namings gamma = NameEnv gamma String

renderBinder :: Namings gamma -> (s !- Term Chk) ^ gamma -> Raw
renderBinder ns (K t :^ r) = render ns (t :^ r)
renderBinder ns (L x t :^ r) = RB y (render (NS ns y) (t :^ OS r)) where
  y = head (dropWhile (`elem` ns) (x : [x ++ show i | i <- [0 :: Integer ..]]))

render :: Namings gamma -> Term Chk ^ gamma -> Raw
render ns (Star _ :^ _) = RA "Type"
render ns (Pi _ST :^ r) = _ST :^ r >^< \ _S _T -> 
  RC (RA "Pi") (render ns _S :-: Only (renderBinder ns _T))
render ns (Lam t :^ r) = RC (RA "\\") (Only (renderBinder ns (t :^ r)))
render ns (E e :^ r) = renderSyn ns (e :^ r) Nothing

itsName :: Namings gamma -> (B0 :< s) <= gamma -> String
itsName (NS _ x) (OS _) = x
itsName (NS ns _) (O' r) = itsName ns r

renderSyn :: Namings gamma -> Term Syn ^ gamma -> Maybe (NEL Raw) -> Raw
renderSyn ns (V It :^ r) Nothing = RA (itsName ns r)
renderSyn ns (V It :^ r) (Just rs) = RC (RA (itsName ns r)) rs
renderSyn ns (App fa :^ r) rs = fa :^ r >^< \f a ->
  renderSyn ns f (Just (render ns a :- rs))
renderSyn ns (Hole m theta :^ r) rs =
  renderHole ns (show $ metaName m) (metaContext m) (theta :^ r) rs

renderHole :: Namings gamma ->
              String -> Context theta -> Env theta ^ gamma ->
              Maybe (NEL Raw) -> Raw
renderHole ns h C0 _ Nothing = RA h
renderHole ns h C0 _ (Just rs) = RC (RA h) rs
renderHole ns h (_Theta :\ _) (ES p :^ r) rs = p :^ r >^< \theta i ->
  renderHole ns h _Theta theta (Just (renderInstance ns i :- rs))

renderInstance :: Namings gamma -> Instance s ^ gamma -> Raw
renderInstance ns (IS s :^ r) = render ns (s :^ r)
renderInstance ns (IP p :^ r) = renderPnt ns (p :^ r)

renderPnt :: Namings gamma -> Term Pnt ^ gamma -> Raw
renderPnt ns (Hole m theta :^ r) =
  renderHole ns (show $ metaName m) (metaContext m) (theta :^ r) Nothing

-- render N0 (Star Void)
-- render N0 (Pi (Pair CZZ (Star Void) (K (Star Void))))
-- render N0 (Pi (Pair CZZ (Star Void) (L "X" (Pi (Pair (CSS CZZ) (E (V It)) (K (E (V It))))))))

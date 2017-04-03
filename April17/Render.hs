{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures #-}

module Render where

import Utils
import OPE
import Raw
import Kernel

type Namings gamma = Env gamma String

renderBinder :: Namings gamma -> (s !- Term Chk) ^ gamma -> Raw
renderBinder ns (K t :^ r) = render ns (t :^ r)
renderBinder ns (L x t :^ r) = RB y (render (NS ns y) (t :^ OS r)) where
  y = head (dropWhile (`elem` ns) (x : [x ++ show i | i <- [0 :: Integer ..]]))

render :: Namings gamma -> Term Chk ^ gamma -> Raw
render ns (Star _ :^ _) = RA "Type"
render ns (Pi (Pair c _S _T) :^ r) =
  RC (RA "Pi")
     (render ns (_S :^ r -<=- lCoP c) :-:
      Only (renderBinder ns (_T :^ r -<=- rCoP c)))
render ns (Lam t :^ r) = RC (RA "\\") (Only (renderBinder ns (t :^ r)))
render ns (E e :^ r) = renderSyn ns (e :^ r) Nothing

itsName :: Namings gamma -> (B0 :< s) <= gamma -> String
itsName (NS _ x) (OS _) = x
itsName (NS ns _) (O' r) = itsName ns r

renderSyn :: Namings gamma -> Term Syn ^ gamma -> Maybe (NEL Raw) -> Raw
renderSyn ns (V It :^ r) Nothing = RA (itsName ns r)
renderSyn ns (V It :^ r) (Just rs) = RC (RA (itsName ns r)) rs
renderSyn ns (App (Pair c f a) :^ r) rs = renderSyn ns (f :^ r -<=- lCoP c) (Just (render ns (a :^ r -<=- rCoP c) :- rs))

-- render N0 (Star Void)
-- render N0 (Pi (Pair CZZ (Star Void) (K (Star Void))))
-- render N0 (Pi (Pair CZZ (Star Void) (L "X" (Pi (Pair (CSS CZZ) (E (V It)) (K (E (V It))))))))

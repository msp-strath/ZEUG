{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             StandaloneDeriving, DeriveFoldable #-}

module Render where

import Utils
import OPE
import Raw
import Kernel
import Control.Arrow

data Whatever :: Bwd Sort -> * -> * where
  N0 :: Whatever B0 a
  NS :: Whatever gamma a -> a -> Whatever (gamma :< s) a
  N' :: Whatever gamma a -> a -> Whatever gamma a

deriving instance Foldable (Whatever gamma)

type Namings gamma = Whatever gamma String

coPNamings :: Namings theta -> CoP gamma delta theta ->
              (Namings gamma,Namings delta)
coPNamings N0 CZZ = (N0,N0)
coPNamings (NS ns x) (CSS r) = ((`NS` x) *** (`NS` x)) $ coPNamings ns r
coPNamings (NS ns x) (CS' r) = ((`NS` x) *** (`N'` x)) $ coPNamings ns r
coPNamings (NS ns x) (C'S r) = ((`N'` x) *** (`NS` x)) $ coPNamings ns r
coPNamings (N' ns x) r = ((`N'` x) *** (`N'` x)) $ coPNamings ns r

renderBinder :: Namings gamma -> (s !- Term Chk) gamma -> Raw
renderBinder ns (K t) = render ns t
renderBinder ns (L x t) = RB y (render (NS ns y) t) where
  y = head (dropWhile (`elem` ns) (x : [x ++ show i | i <- [0 :: Integer ..]]))

render :: Namings gamma -> Term Chk gamma -> Raw
render ns (Star _) = RA "Type"
render ns (Pi (Pair c _S _T)) =
  RC (RA "Pi") (render ns' _S :-: Only (renderBinder ns'' _T))
  where (ns',ns'') = coPNamings ns c
render ns (Lam t) = RC (RA "\\") (Only (renderBinder ns t))
render ns (E e) = renderSyn ns e Nothing

itsName :: Namings (B0 :< s) -> String
itsName (N' ns _) = itsName ns
itsName (NS _ x) = x

renderSyn :: Namings gamma -> Term Syn gamma -> Maybe (NEL Raw) -> Raw
renderSyn ns (V It) Nothing = RA (itsName ns)
renderSyn ns (V It) (Just rs) = RC (RA (itsName ns)) rs
renderSyn ns (App (Pair c f a)) rs = renderSyn ns' f (Just (render ns'' a :- rs))
  where (ns',ns'') = coPNamings ns c

-- render N0 (Star Void)
-- render N0 (Pi (Pair CZZ (Star Void) (K (Star Void))))
-- render N0 (Pi (Pair CZZ (Star Void) (L "X" (Pi (Pair (CSS CZZ) (E (V It)) (K (E (V It))))))))

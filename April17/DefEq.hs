-- mind your...
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures, TypeFamilies #-}
module DefEq where

import Data.Void
import Utils
import OPE
import Kernel

data Context :: Bwd Sort -> * where
  C0 :: Context B0
  (:\) :: Sorted gamma =>
          Context gamma -> (Sorty s , String , Info s ^ gamma) ->
          Context (gamma :< s)

type family Info (s :: Sort) :: Bwd Sort -> * where
  Info Syn = Term Chk
  Info Chk = Got Void
  Info Pnt = Got ()

lookupC :: Context gamma -> (B0 :< s) <= gamma -> Info s ^ gamma
lookupC (_ :\ (_,_,i)) (OS _) = wk i
lookupC (gamma :\ _) (O' r) = wk (lookupC gamma r)
                                  

etaExpand :: Sorted gamma =>
             Context gamma -> Radical Syn gamma -> Term Chk ^ gamma
etaExpand gamma f@(_ ::: Pi _ST :^ _R) = _ST :^ _R >^< \_S _T ->
  mapIx Lam $ abstract "YKW" (etaExpand (gamma :\ (Syny,"YKW",_S)) 
                                        (app (radWk f) freshVar))
etaExpand gamma (Star Void :^ _ ::: Star Void :^ _) = star
etaExpand gamma (Pi _ST :^ _R ::: Star Void :^ _) = _ST :^ _R >^< \_S _T ->
  let _S' = etaExpand gamma (_S ::: star)
      _T' = instantiate (wk _T) (freshVar ::: wk _S)
  in mapIx Pi (pair _S' (abstract "YKW" (etaExpand (gamma :\ (Syny,"YKW",_S))
                                                   (_T' ::: star))))
etaExpand gamma (E e :^ r ::: _) =
  mapIx E (fst $ neutExpand gamma (e :^ r))

neutExpand :: Sorted gamma =>
              Context gamma ->   
              Term Syn ^ gamma ->
              (Term Syn ^ gamma,  -- eta expanded term
               Term Chk ^ gamma)  -- its reconstructed type (not expanded)
neutExpand gamma e@(V It :^ r) = (e , lookupC gamma r)
neutExpand gamma (App fs :^ r) = fs :^ r >^< \f s ->
  case neutExpand gamma f of
    (f , Pi _ST :^ _R) -> _ST :^ _R >^< \_S _T ->
      (mapIx App (pair f (etaExpand gamma (s ::: _S))),
       instantiate _T  (s ::: _S))
  

defEq :: Sorted gamma =>
         Context gamma ->
         Term Chk ^ gamma -> Term Chk ^ gamma -> Term Chk ^ gamma ->
         Maybe ()
defEq gamma ty t t' =
  eq (etaExpand gamma (t ::: ty)) (etaExpand gamma (t' ::: ty))


------------------------------------------------------------------------------
-----                                                                    -----
-----     The Proof State                                                -----
-----                                                                    -----
------------------------------------------------------------------------------

{-# LANGUAGE KindSignatures, GADTs, DataKinds, DeriveFunctor,
    DeriveFoldable, DeriveTraversable #-}

module ProofState where

import Data.Maybe
import Data.List
import Data.List.Split

import Utils
import OPE
import Kernel
import Raw
import Render

data Cursor u x = Cur (Bwd x) u [x] deriving (Functor, Foldable, Traversable)

data Defn (delta :: Bwd Sort) (s :: Sort)
  = Defn {defnSort :: Sorty s
         ,defnName :: LongName
         ,defnContext :: Context delta
         ,defnRadical :: Radical delta s
         }

data Entity :: * where
  EHole :: Meta delta s -> Entity
  EDefn :: Defn delta s -> Entity

nameOf :: Entity -> LongName
nameOf (EHole m) = metaName m
nameOf (EDefn d) = defnName d

type Prefix = LongName
type Range = (Maybe LongName, Maybe LongName)

type ProofState = Cursor (Prefix, Range) Entity

initialProofState :: ProofState
initialProofState = Cur B0 (mempty,(Nothing,Nothing)) []

texas :: ProofState -> [String]
texas _ =  -- art by Joan Stark
  ["            ___"
  ,"           |   |"
  ,"           |   '._   _"
  ,"           |      ``` '|"
  ,"       ____|           \\"
  ,"      `-.               |"
  ,"         \\ _           /"
  ,"          ` `\\       /`"
  ,"              \\   .'`"
  ,"        jgs    \\  \\ "
  ,"                '-;"
  ]

prompt :: ProofState -> String
prompt (Cur _ (p,r) _) = show p ++ case r of
  (Nothing,Nothing) -> ""
  (Nothing,Just y) -> " (^ " ++ show y ++ ")"
  (Just x,Nothing) -> " (" ++ show x ++ " ^)"
  (Just x,Just y) -> " (" ++ show x ++ " ^ " ++ show y ++ ")"

newName :: ProofState -> String -> Maybe LongName
newName ps@(Cur _ (p, _) _) x = case x of
    '/' : x  -> good (segs x)
    x        -> good (mappend p (segs x))
  where
    segs x = LongName (filter (not . null) (splitWhen (== '/') x))
    good x = if any (isPrefixOf (longName x) . longName . nameOf) ps
      then Nothing else Just x

inView :: (LongName, Maybe LongName) -> Entity -> Bool
inView (p, n) e = isPrefixOf (longName p) x && not (isPrefixOf b x) where
  x = longName (nameOf e)
  b = maybe [""] (longName . mappend p) n -- [""] cannot prefix a name

viewPort :: ProofState -> ProofState
viewPort (Cur ez u@(p, (n0, n1)) es) = Cur (findz ez) u (finds es) where
  findz (ez :< e) | inView (p, n0) e  = findz ez :< e
  findz _                             = B0
  finds (e : es)  | inView (p, n1) e  = e : finds es
  finds _                             = []

displayContext :: Context gamma -> ([String], Namings gamma)
displayContext C0 = ([], N0)
displayContext (gamma :\ (s, x, i)) = (bs ++ [b], NS nz x) where
  (bs, nz) = displayContext gamma
  b = "  " ++ case s of
    Syny -> show (RA Vrble x) ++ " : " ++ show (render nz i)
    Pnty -> show (RA Vrble x)

displayEntity :: Char -> Entity -> [String]
displayEntity c (EHole m) = ("" : bs ++ [rule, h]) where
  (bs, nz) = displayContext (metaContext m)
  h = "  " ++ show (RA Holey (show (metaName m) ++ "?")) ++ case metaSort m of
    Pnty -> ""
    Syny -> " : " ++ show (render nz (metaInfo m))
  rule = replicate (2 + maximum [mylen x | x <- h : bs]) c
displayEntity c (EDefn m) = ("" : bs ++ rule : hs) where
  (bs, nz) = displayContext (defnContext m)
  x = show (defnName m)
  hs = case (defnSort m, defnRadical m) of
    (Pnty, RP p)     ->  ["  " ++ show (RA Defin x)
                          ++ " = " ++ show (renderPnt nz p)]
    (Syny, t ::: _T) ->
      [  "  " ++ show (RA Defin x) ++ " = " ++ show (render nz t)
      ,  replicate (2 + mylen x) ' ' ++ " : " ++ show (render nz _T)
      ]
  rule = replicate (2 + maximum [mylen x | x <- hs ++ bs]) c

display :: ProofState -> [String]
display ps = case viewPort ps of
  Cur ez _ (e : es) -> foldMap (displayEntity '-') ez ++
                       displayEntity '=' e ++
                       foldMap (displayEntity '-') es
  Cur ez _ []       -> foldMap (displayEntity '-') ez ++
                       ["", "==========================="]

updates :: [Update] -> [Entity] -> [Entity]
updates us [] = []
updates us (EHole m@(Meta s x _Theta _I) : es) = subInfo s $
  updateContext _Theta us $ \ _Theta ->
  let m' = Meta s x _Theta (joinH (update _I us))
  in EHole m' : updates ((m :=> Renew m') : us) es
updates us (EDefn (Defn s x _Theta r) : es) =
  updateContext _Theta us $ \ _Theta ->
  EDefn (Defn s x _Theta (updateRadical r us)) : updates us es

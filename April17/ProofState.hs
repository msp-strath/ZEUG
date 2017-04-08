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
import Control.Monad

import Utils
import OPE
import Kernel
import Raw
import Render

data Cursor u x = Cur (Bwd x) u [x] deriving (Functor, Foldable, Traversable)

data Defn (delta :: Bwd Sort) (s :: Sort)
  = Sorted delta =>
    Defn {defnSort :: Sorty s
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
type ViewPort = Cursor (Prefix, Range) (LongName, Entity)

initialProofState :: ProofState
initialProofState = Cur B0 zoomedOut []

zoomedOut :: (Prefix, Range)
zoomedOut = (mempty, (Nothing, Nothing))

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

parseName :: ProofState -> String -> (LongName, Bool {-holey ?-})
parseName (Cur _ (p, _) _) x = case x of
    '/' : _ -> (s, h)
    _       -> (mappend p s, h)
  where
    (qs, y) = partition (== '?') x
    s = LongName (filter (not . null) (splitWhen (== '/') y))
    h = not (null qs)

newName :: ProofState -> String -> Maybe LongName
newName ps x = do
  let (y, _) = parseName ps x
  guard . not $ any (isPrefixOf (longName y) . longName . nameOf) ps
  return y

inView :: (LongName, Maybe LongName) -> Entity -> Maybe (LongName, Entity)
inView (p, n) e = do
    m <- stripPrefix (longName p) (longName (nameOf e))
    guard . not $ isPrefixOf (maybe [""] longName n) m
      -- [""] cannot prefix a name
    return (LongName m, e)

viewPort :: ProofState -> ViewPort
viewPort (Cur ez u@(p, (n0, n1)) es) = Cur (findz ez) u (finds es) where
  findz (ez :< e) = case inView (p, n0) e of
    Nothing -> B0
    Just me -> findz ez :< me
  findz _         = B0
  finds (e : es)  = case inView (p, n1) e of
    Nothing -> []
    Just me -> me : finds es
  finds _         = []

displayContext :: Context gamma -> ([String], Namings gamma)
displayContext C0 = ([], N0)
displayContext (gamma :\ (s, x, i)) = (bs ++ [b], NS nz x) where
  (bs, nz) = displayContext gamma
  b = "  " ++ case s of
    Syny -> show (RA Vrble x) ++ " : " ++ show (render nz i)
    Pnty -> show (RA Vrble x)

displayEntity :: Char -> (LongName, Entity) -> [String]
displayEntity c (y, EHole m) = ("" : bs ++ [rule, h]) where
  (bs, nz) = displayContext (metaContext m)
  h = "  " ++ show (RA Holey (show y ++ "?")) ++ case metaSort m of
    Pnty -> ""
    Syny -> " : " ++ show (render nz (metaInfo m))
  rule = replicate (2 + maximum [mylen x | x <- h : bs]) c
displayEntity c (y, EDefn m) = ("" : bs ++ rule : hs) where
  (bs, nz) = displayContext (defnContext m)
  x = show y
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

fwdToGoal :: ProofState -> ProofState
fwdToGoal (Cur ez u@(p, (_, n)) (e@(EDefn _) : es))
  | Just _ <- inView (p, n) e
  = fwdToGoal (Cur (ez :< e) u es)
fwdToGoal ps = ps

fwdToView :: ProofState -> ProofState
fwdToView ps@(Cur ez u@(p, (n, _)) (e : es))
  | Nothing <- inView (p, n) e = fwdToView (Cur (ez :< e) u es)
fwdToView ps = ps


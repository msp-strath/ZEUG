------------------------------------------------------------------------------
-----                                                                    -----
-----     The Proof State                                                -----
-----                                                                    -----
------------------------------------------------------------------------------

{-# LANGUAGE KindSignatures, GADTs, DataKinds, DeriveFunctor,
    DeriveFoldable, DeriveTraversable #-}

module ProofState where

import Data.List
import Data.List.Split

import Utils
import Kernel

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

type ProofState = Cursor (Prefix,Range) Entity

initialProofState :: ProofState
initialProofState = Cur B0 (mempty,(Nothing,Nothing)) []

display :: ProofState -> [String]
display _ =  -- art by Joan Stark
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

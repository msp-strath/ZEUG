------------------------------------------------------------------------------
-----                                                                    -----
-----     The Proof State                                                -----
-----                                                                    -----
------------------------------------------------------------------------------

{-# LANGUAGE KindSignatures, GADTs, DataKinds #-}

module ProofState where

import Utils
import Kernel

data Cursor x u = Cur (Bwd x) u [x]

data Defn (delta :: Bwd Sort) (s :: Sort)
  = Defn {defnSort :: Sorty s
         ,defnName :: LongName
         ,defnContext :: Context delta
         ,defnRadical :: Radical delta s
         }

data Entity :: * where
  EHole :: Meta delta s -> Entity
  EDefn :: Defn delta s -> Entity

type Prefix = LongName
type Range = (Maybe LongName, Maybe LongName)

type ProofState = Cursor Entity (Prefix,Range)

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


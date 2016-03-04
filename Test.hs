--{-# OPTIONS -Wall -fwarn-incomplete-patterns #-}
{-# LANGUAGE KindSignatures, DataKinds, ScopedTypeVariables, PolyKinds,
             UndecidableInstances, MultiParamTypeClasses,
             FunctionalDependencies, PatternSynonyms,
             FlexibleInstances, GADTs, DeriveFunctor, RankNTypes, EmptyCase,
             TypeFamilies, StandaloneDeriving #-}
module Test where

import Utils
import Syntax
import TypeCheck

import Layout
import Raw
import ProofState


data Test where
  PARSE  :: String -> Test
  ISKIND :: TERM W0 -> Test
  CHECK  :: TERM W0 -> TERM W0 -> Test
  NORM   :: ELIM W0 -> TERM W0 -> Test
  FAILS  :: Test -> Test

deriving instance Show Test

pattern INFER e t = CHECK t (En e)

runTest :: Test -> TC Happy W0
runTest (PARSE s) = 
  if length (parses bigMod (headline (layout s))) == 1 then Yes Happy else No
runTest (ISKIND ty)  = Kind >:> ty
runTest (CHECK k t) = (Kind >:>= k) >>>= \ vty -> vty >:> t
runTest (NORM e nf) =
  enType e >>>= \ (v :::: vty) ->
    if etaquote (v :::: vty) == nf then Yes Happy else No
runTest (FAILS test) = case runTest test of
  No -> Yes Happy
  Yes _ -> No

testReport :: (String,Test) -> IO ()
testReport (name,test) = case runTest test of
  Yes _ -> putStrLn (name ++ ": PASSED")
  No    -> putStrLn (name ++ ": FAILED:") >> print test

passtests = 
 [("test-1",ISKIND (El (Pi Set Set)))
 ,("test0",CHECK (El (Pi Set Set)) (Lam (En (V FZero))))
 ,("test1",INFER ((Lam (En (V FZero)) ::: El (Pi Set Set)) :/ Set) (El Set))
 ,("test1.5",ISKIND (El (Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))))))
 ,("test2",CHECK (El (Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))))) (Lam (Lam (En (V FZero)))))
 ,("test3",INFER (Lam (Lam (En (V FZero))) ::: El (Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero)))))) :/ Set) (El (Pi Set Set)))
 ,("test4",INFER (Lam (Lam (En (V FZero))) ::: El (Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero)))))) :/ Set :/ Set) (El Set))
 ,("test5",CHECK (El (Sg Set Set)) (Set :& Set))
 ,("test6",INFER (((Set :& Set) ::: El (Sg Set Set)) :/ Fst) (El Set))
 ,("test7",INFER (((Set :& Set) ::: El (Sg Set Set)) :/ Snd) (El Set))
 ,("test8",CHECK (El (Sg Set (En (V FZero)))) (Set :& Set))
 ,("test9",CHECK (El (Pi (Sg Set Set) Set)) (Lam (En ((V FZero) :/ Fst))))
 ,("test0",NORM (Lam (En (V FZero)) ::: El (Pi (Sg Set Set) (Sg Set Set)))
                   (Lam (En ((:/) (V FZero) (Atom "Fst")) :& En ((:/) (V FZero) (Atom "Snd")))))
 ,("testLet",CHECK (El Set) (Let (Set ::: El Set) (En (Set ::: El (En (V FZero))))))
 ]

failtests = map (fmap FAILS)
 [("test0",NORM ((Lam (En (V FZero)) ::: Set) :/ Set) Set)
 ,("testLet",CHECK Set (En ((Lam (En (Set ::: En (V FZero))) ::: Pi Set Set) :/ Set)))
 ]

blerk2 :: TC Happy W0
blerk2 = Type >:> Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero)))))
--  (Lam (Lam (En (V FZero)))))
-- raw tests (checks for an unambiguous parse)

rawTests = 
 [("rawtest0",PARSE "")
 ,("rawtest1",PARSE "(x : S)")
 ,("rawtest2",PARSE "(x : S){x}")
 ,("rawtest3",PARSE "(x : S){x = hello : world}")]

-- proof state tests
testRig :: String -> String
testRig s = ugly 0 (ambulando ((L0,supply0) 
  :!-: PRaw (snd (head (parses (sub bigMod) (headline (layout s)))))))

ftestRig :: String -> IO ()
ftestRig s = do
  x <- readFile s
  putStrLn (testRig x)

main = do 
  mapM_ testReport ({- rawTests ++ -} passtests ++ failtests)
  -- can't do much else until we have a pretty printer
  ftestRig "tests/tests.zoig"


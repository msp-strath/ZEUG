--{-# OPTIONS -Wall -fwarn-incomplete-patterns #-}
{-# LANGUAGE KindSignatures, DataKinds, ScopedTypeVariables, PolyKinds,
             UndecidableInstances, MultiParamTypeClasses,
             FunctionalDependencies, PatternSynonyms,
             FlexibleInstances, GADTs, DeriveFunctor, RankNTypes, EmptyCase,
             TypeFamilies #-}
module Test where

import Utils
import Syntax
import TypeCheck

import Layout
import Raw
import ProofState

-- type checker tests
data Test where
  ISTYPE :: TERM W0 -> Test
  CHECK :: TERM W0 -> TERM W0 -> Test
  NORM  :: ELIM W0 -> TERM W0 -> Test
  FAILS :: Test -> Test
  deriving Show


pattern INFER e t = CHECK t (En e)

runTest :: Test -> TC Happy W0
runTest (ISTYPE ty)  = isType ty
runTest (CHECK ty t) = goodType ty >>>= \ vty -> vty >:> t
runTest (NORM e nf) =
  goodElim e >>>= \ (v :&: vty) ->
    if etaquote vty v == nf then Yes Happy else No
runTest (FAILS test) = case runTest test of
  No -> Yes Happy
  Yes _ -> No

testReport :: (String,Test) -> IO ()
testReport (name,test) = case runTest test of
  Yes _ -> putStrLn (name ++ ": PASSED")
  No    -> putStrLn (name ++ ": FAILED:") >> print test

passtests = 
 [("test0",CHECK (Pi Set Set) (Lam (En (V FZero))))
 ,("test1",INFER ((Lam (En (V FZero)) ::: Pi Set Set) :$ Set) Set)
 ,("test2",CHECK (Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero)))))) (Lam (Lam (En (V FZero)))))
 ,("test3",INFER (Lam (Lam (En (V FZero))) ::: Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))) :$ Set) (Pi Set Set))
 ,("test4",INFER (Lam (Lam (En (V FZero))) ::: Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))) :$ Set :$ Set) Set)
 ,("test5",CHECK (Sg Set Set) (Set :& Set))
 ,("test6",INFER (Fst ((Set :& Set) ::: Sg Set Set)) Set)
 ,("test7",INFER (Snd ((Set :& Set) ::: Sg Set Set)) Set)
 ,("test8",CHECK (Sg Set (En (V FZero))) (Set :& Set))
 ,("test9",CHECK (Pi (Sg Set Set) Set) (Lam (En (Fst (V FZero)))))
 ,("test0",NORM (Lam (En (V FZero)) ::: Pi (Sg Set Set) (Sg Set Set))
                   (Lam (En ((:$) (V FZero) (Atom "Fst")) :& En ((:$) (V FZero) (Atom "Snd")))))
 ,("testLet",CHECK Set (Let (Set ::: Set) (En (Set ::: En (V FZero)))))
 ]

failtests = map (fmap FAILS)
 [("test0",NORM ((Lam (En (V FZero)) ::: Set) :$ Set) Set)
 ,("testLet",CHECK Set (En ((Lam (En (Set ::: En (V FZero))) ::: Pi Set Set) :$ Set)))
 ]

-- proof state tests
testRig :: String -> String
testRig s = ugly 0 (ambulando ((L0,supply0) 
  :!-: PRaw (snd (head (parses (sub bigMod) (headline (layout s)))))))

ftestRig :: String -> IO ()
ftestRig s = do
  x <- readFile s
  putStrLn (testRig x)

main = do 
  mapM_ testReport (passtests ++ failtests)
  -- can't do much else until we have a pretty printer
  ftestRig "tests/tests.zoig"


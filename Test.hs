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

tests = 
 [("yestest0",CHECK (Pi Set Set) (Lam (En (V FZero))))
 ,("yestest1",INFER ((Lam (En (V FZero)) ::: Pi Set Set) :$ Set) Set)
 ,("yestest2",CHECK (Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero)))))) (Lam (Lam (En (V FZero)))))
 ,("yestest3",INFER (Lam (Lam (En (V FZero))) ::: Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))) :$ Set) (Pi Set Set))
 ,("yestest4",INFER (Lam (Lam (En (V FZero))) ::: Pi Set (Pi (En (V FZero)) (En (V (FSuc (FZero))))) :$ Set :$ Set) Set)
 ,("yestest5",CHECK (Sg Set Set) (Set :& Set))
 ,("yestest6",INFER (Fst ((Set :& Set) ::: Sg Set Set)) Set)
 ,("yestest7",INFER (Snd ((Set :& Set) ::: Sg Set Set)) Set)
 ,("yestest8",CHECK (Sg Set (En (V FZero))) (Set :& Set))
 ,("yestest9",CHECK (Pi (Sg Set Set) Set) (Lam (En (Fst (V FZero)))))
 ,("valtest0",NORM (Lam (En (V FZero)) ::: Pi (Sg Set Set) (Sg Set Set))
                   (Lam (En ((:$) (V FZero) (Atom "Fst")) :& En ((:$) (V FZero) (Atom "Snd")))))
 ,("notest0",FAILS (NORM ((Lam (En (V FZero)) ::: Set) :$ Set) Set))
 ]

main = mapM_ testReport tests

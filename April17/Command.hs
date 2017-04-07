{-# LANGUAGE GADTs #-}

module Command where

import Utils
import Raw
import Kernel
import ProofState
import Elaborator

command :: ProofState -> Raw -> ([String], Maybe ProofState)
command ps (RC (RA x) (Only b)) | isDefBody b = case newName ps x of
  Nothing -> (["I don't like the name " ++ x], Nothing)
  Just x -> case tryElab (ps, C0, x) (define b) of
    Just (_, ps)  -> (["Aye."], Just ps)
    Nothing       -> (["Naw."], Nothing)
command ps c = (["Try doing something else."], Nothing)

isDefBody :: Raw -> Bool
isDefBody (RC (RA "=") (Only s))    = True
isDefBody (RC _S (Only (RB x _T)))  = isDefBody _T
isDefBody (RC _S (Only _T))         = isDefBody _T
isDefBody _                         = False

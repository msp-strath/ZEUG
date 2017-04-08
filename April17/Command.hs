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
command (Cur ez u (EHole m@(Meta s x _Theta _I) : es)) (RC (RA "=") (Only b))
  = case s of
    Pnty -> (["Try points another day."], Nothing)
    Syny -> case tryElab (Cur ez u es, _Theta, x) (chk _I b) of
      Nothing -> (["Naw."], Nothing)
      Just (t, Cur ez u es) ->
        ( ["Aye."]
        , Just (Cur ez u (updates [m :=> Solve (mapIx IS t)] es))
        )
command ps c = (["Try doing something else."], Nothing)

isDefBody :: Raw -> Bool
isDefBody (RC (RA "=") (Only s))    = True
isDefBody (RC _S (Only (RB x _T)))  = isDefBody _T
isDefBody (RC _S (Only _T))         = isDefBody _T
isDefBody _                         = False
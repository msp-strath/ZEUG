{-# LANGUAGE GADTs, PatternGuards #-}

module Command where

import Utils
import Raw
import Kernel
import ProofState
import Elaborator

command :: ProofState -> Raw c -> ([String], Maybe ProofState)
command ps (RC (RA _ x) (Only b)) | isDefBody b = case newName ps x of
  Nothing -> (["I don't like the name " ++ x], Nothing)
  Just x -> case tryElab (ps, C0, x) (define b) of
    Just (_, ps)  -> (["Aye."], Just ps)
    Nothing       -> (["Naw."], Nothing)
command (Cur ez u (EHole m@(Meta s x _Theta _I) : es))
  (RC (RA _ "=") (Only b)) = case s of
  Pnty -> (["Try points another day."], Nothing)
  Syny -> case tryElab (Cur ez u es, _Theta, x) (chk _I b) of
    Nothing -> (["Naw."], Nothing)
    Just (t, Cur ez u es) ->
      ( ["Aye."]
      , Just (fwdToGoal $ Cur ez u (updates [m :=> Solve (mapIx IS t)] es))
      )
command ps@(Cur ez u es) (RC (RA _ "/") (Only (RA _ x))) =
  case fwdToView (Cur B0 (fst (parseName ps x), (Nothing, Nothing))
                      (ez <>> es)) of
    Cur _ (LongName (_ : _), _) [] -> (["Where's " ++ x ++ "?"], Nothing)
    ps -> ([], Just (fwdToGoal ps))
command ps c = (["Try doing something else."], Nothing)

isDefBody :: Raw c -> Bool
isDefBody (RC (RA _ "=") (Only s))    = True
isDefBody (RC _S (Only (RB _ x _T)))  = isDefBody _T
isDefBody (RC _S (Only _T))           = isDefBody _T
isDefBody _                           = False

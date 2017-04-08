{-# LANGUAGE GADTs, PatternGuards #-}

module Command where

import Data.List

import Utils
import Raw
import Kernel
import ProofState
import Elaborator

command :: ProofState -> Raw c -> ([String], Maybe ProofState)

-- MAKING A DEFINITION
command ps (RC (RA _ x) (Only b)) | isDefBody b = case newName ps x of
  Nothing -> (["I don't like the name " ++ x], Nothing)
  Just x -> case tryElab (ps, C0, x) (define b) of
    Just (_, ps)  -> (["Aye."], Just ps)
    Nothing       -> (["Naw."], Nothing)

-- GIVING A REFINEMENT
command (Cur ez u (EHole m@(Meta s x _Theta _I) : es))
  (RC (RA _ "=") (Only b)) = case s of
  Pnty -> (["Try points another day."], Nothing)
  Syny -> case tryElab (Cur ez u es, _Theta, x) (chk _I b) of
    Nothing -> (["Naw."], Nothing)
    Just (t, Cur ez u es) ->
      ( ["Aye."]
      , Just (fwdToGoal $ Cur ez u (updates [m :=> Solve (mapIx IS t)] es))
      )

-- ZOOMING TO A NAME
command ps@(Cur ez u es) (RC (RA _ "/") (Only (RA _ x))) =
  case fwdToView (Cur B0 (fst (parseName ps x), (Nothing, Nothing))
                      (ez <>> es)) of
    Cur _ (LongName (_ : _), _) [] -> (["Where's " ++ x ++ "?"], Nothing)
    ps -> ([], Just (fwdToGoal ps))

-- ZOOMING OUT
command (Cur ez u@(LongName p@(_ : _), _) es) (RA _ "<") =
  ([], Just (Cur ez (LongName (init p), (Nothing, Nothing)) es))

-- DOWN ONE
command (Cur ez u@(p, (_, n)) (e : es)) (RA _ "next")
  | Just _ <- inView (p, n) e = ([], Just (Cur (ez :< e) u es))
  | otherwise                 = (["Bump!"], Nothing)

-- UP ONE
command (Cur (ez :< e) u@(p, (n, _)) es) (RA _ "prev")
  | Just _ <- inView (p, n) e = ([], Just (Cur ez u (e : es)))
  | otherwise                 = (["Bump!"], Nothing)

-- SETTING A RANGE
command ps (RC (RA _ x) (RA _ "^" :-: Only (RA _ y)))
  = rerange ps (Just (fst (parseName ps x)), Just (fst (parseName ps y)))
command ps (RC (RA _ x) (Only (RA _ "^")))
  = rerange ps (Just (fst (parseName ps x)), Nothing)
command ps (RC (RA _ "^") (Only (RA _ y)))
  = rerange ps (Nothing, Just (fst (parseName ps y)))
command (Cur ez (p, _) es) (RA _ "^")
  = ([], Just (Cur ez (p, (Nothing, Nothing)) es))

-- BARF!
command ps c = (["Try doing something else."], Nothing)

isDefBody :: Raw c -> Bool
isDefBody (RC (RA _ "=") (Only s))    = True
isDefBody (RC _S (Only (RB _ x _T)))  = isDefBody _T
isDefBody (RC _S (Only _T))           = isDefBody _T
isDefBody _                           = False

rerange :: ProofState -> (Maybe LongName, Maybe LongName) ->
  ([String], Maybe ProofState)
rerange ps@(Cur ez (p@(LongName x), _) es) (a, b) =
  ([], Just (Cur ez (p, (a >>= tidy, b >>= tidy)) es)) where
  tidy (LongName y) = LongName <$> stripPrefix x y

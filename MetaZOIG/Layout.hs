{-# LANGUAGE PatternGuards, GADTs #-}

module Layout where

import Data.Maybe
import Control.Applicative
import Control.Monad

data Token
  = Spc Int
  | EoL
  | Sym String
  | Grp String [Token] String
  | Sub
  deriving (Show, Eq, Ord)

tokens :: String -> [Token]
tokens [] = []
tokens (c : s)
  | elem c solo  = Sym [c] : tokens s
  | elem c spc   = let (i, b) = space 1 s in Spc i : tokens b
  | c == '\n'    = EoL : tokens s
  | otherwise    = let (a, b) = symb s in Sym (c : a) : tokens b
  where  
    spc = " \t"
    solo = "()[]{},;"
    symb = break (`elem` ('\n' : spc ++ solo))
    space i (c : s)  | elem c spc   = space (i + 1) s
    space i s                       = (i, s)

data Line
  = [Token] :-: Maybe [Line]
  deriving Show

groupify :: [Token] -> [Token]
groupify = fst . chomp (const False) where
  groupers = [("(", ")"), ("[", "]"), ("{", "}")]
  fcons t (ts, z) = (t : ts, z)
  chomp p [] = ([], Nothing)
  chomp p (t : ts) | p t = ([], Just ts)
  chomp p (t@(Sym x) : ts)
    | Just y <- lookup x groupers
    = case chomp (Sym y ==) ts of
        (ss, Just ts) -> fcons (Grp x ss y) (chomp p ts)
        (ss, Nothing) -> (t : ss, Nothing)
  chomp p (t : ts) = fcons t (chomp p ts)
  
tokLines :: Int -> [Token] -> ([Line], [Token])
tokLines i []         = ([], [])
tokLines i ts@(t : _)
  | j <= i     = ([], ts)
  | otherwise  =
    let  ((us :-: m),  ts1) = tokLine ts
         (ls, ts2) = tokLines i ts1
    in   ((groupify us :-: m) : ls, ts2)
  where
    dent EoL      = maxBound
    dent (Spc i)  = i
    dent _        = 0
    j = dent t
    tokLine (Sym "-:" : ts) = ([] :-: Just ls, ts') where
      (ls, ts') = tokLines j ts
    tokLine (EoL : ts@(t : _)) | dent t <= j = ([EoL] :-: Nothing, ts)
    tokLine (t : ts) = ((t : ts1) :-: mls, ts2) where
      (ts1 :-: mls, ts2) = tokLine ts
    tokLine [] = ([] :-: Nothing, [])

layout :: String -> [Line]
layout = fst . tokLines (negate 1) . tokens

tuoyal :: [Line] -> String
tuoyal ls = foldr lineOut [] ls where
  lineOut (ts :-: mls) s = foldr tokOut (layoutOut mls s) ts
  layoutOut Nothing    s = s
  layoutOut (Just ls)  s = "-:" ++ foldr lineOut s ls
  tokOut (Sym x)       s = x ++ s
  tokOut EoL           s = '\n' : s
  tokOut (Spc i)       s = replicate i ' ' ++ s
  tokOut (Grp x ts y)  s = x ++ foldr tokOut (y ++ s) ts

newtype ParseTokens a = ParseTokens
  {parseTokens :: [Token] -> [(a, [Token], [Token])]}

instance Monoid (ParseTokens a) where
  mempty = ParseTokens mempty
  mappend (ParseTokens a) (ParseTokens b) = ParseTokens (mappend a b)

instance Monad ParseTokens where
  return x = ParseTokens $ \ ts -> [(x, [], ts)]
  pa >>= k = ParseTokens $ \ ts ->
    [  (b, ats ++ bts, vs)
    |  (a, ats, us) <- parseTokens pa ts
    ,  (b, bts, vs) <- parseTokens (k a) us
    ]

instance Applicative ParseTokens where
  pure = return
  pf <*> pa = pf >>= \ f -> pa >>= \ a -> return (f a)

instance Functor ParseTokens where
  fmap = (<*>) . pure

instance Alternative ParseTokens where
  empty = mempty
  (<|>) = mappend

parses :: ParseTokens a -> [Token] -> [a]
parses p ts = [a | (a, _, []) <- parseTokens p ts]

data Sub x = [Token] := x deriving Show

sub :: ParseTokens a -> ParseTokens (Sub a)
sub p = ParseTokens $ \ ts ->
  [(ss := a, [Sub], ts) | (a, ss, ts) <- parseTokens p ts]

sym :: ParseTokens String
sym = ParseTokens $ \ ts -> case ts of
  t@(Sym x) : ts -> [(x, [t], ts)]
  _ -> []

eat :: String -> ParseTokens ()
eat x = do s <- sym; guard (x == s)

gap :: ParseTokens ()
gap = ParseTokens $ \ ts -> let (ss, us) = span (<= EoL) ts in [((), ss, us)]

gapMany :: ParseTokens a -> ParseTokens [a]
gapMany p = gap *> many (p <* gap)

grp :: String -> ParseTokens a -> String -> ParseTokens a
grp x p y = ParseTokens $ \ ts -> case ts of
  t@(Grp x' ss y') : ts | x == x' && y == y' -> 
    [(a, [Grp x ss' y], ts) | (a, ss', []) <- parseTokens p ss]
  _ -> []

grow :: Int -> ParseTokens x -> (Sub x -> ParseTokens x) -> ParseTokens x
grow i p k = ParseTokens $ \ ts -> extend i (parseTokens p ts) where
  extend 0 zs = (zs >>= more 0) ++ zs
  extend i zs = zs >>= more (i - 1)
  more i (x, ss, ts) = extend i
    [(a, Sub : ss, ts) | (a, ss, ts) <- parseTokens (k (ss := x)) ts]


data Format x where
  Format :: (a -> [b] -> x) -> ParseTokens a -> Format b -> Format x

formatLine :: Format x -> Line -> [x]
formatLine (Format f h l) (ts :-: mtss) =
  f <$> parses h ts <*> traverse (formatLine l) (fromMaybe [] mtss)


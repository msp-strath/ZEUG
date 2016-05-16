{-# LANGUAGE PatternGuards, GADTs, GeneralizedNewtypeDeriving #-}

module Layout where

-- This file is intended as a not especially ZEUG specific manager for the
-- lexical and layout structure of text, with an associated parser
-- combinator library for the lexical structure thus emerging.
--
-- Crucially, the analysis rejects no inputs and preserves the information
-- content of the text (apart from turning any tabs into spaces, which,
-- frankly is more than they deserve).

import Data.Maybe
import Control.Applicative
import Control.Monad


------------------------------------------------------------------------------
-- LEXICAL STRUCTURE
------------------------------------------------------------------------------

-- Where you might be used to thinking of tokens as being other than
-- whitespace, we are keen to preserve it. Also, we are not averse to
-- tokens having interesting internal structure, e.g. when they
-- represent valid groupings of some sort.

data Token
  = Spc Int                     -- horizontal space of positive length
  | EoL                         -- line break
  | Sym String                  -- one contiguous nonspace symbol
  | Grp String [Token] String   -- a valid bracketing of more tokens
  | Sub [Token]                 -- a substructure found by parsing
  deriving (Eq, Ord)            -- anything <= EoL is whitespace

-- Invariants:
--   we never have two consecutive Spc tokens

-- We should say what tokens look like by saying how to print them.

nekot :: Token -> String -> String  -- a difference-String
nekot (Sym x)       s = x ++ s
nekot EoL           s = '\n' : s
nekot (Spc i)       s = replicate i ' ' ++ s
nekot (Grp x ts y)  s = x ++ foldr nekot (y ++ s) ts
nekot (Sub ts)      s = foldr nekot s ts

-- Now we can say how to look for them. Lexical structure is very
-- simple. Lexing is done by this thing:

tokens :: String -> [Token]

-- A few characters form tokens by themselves, namely ()[]{},;
-- (proposal 1: add .) (proposal 2: don't add . and remove ,;)
-- Apart from that, no attempt is made to split contiguous nonwhitespace,
-- so you just get to shove more spaces in. That'll be an Agda thing.

tokens [] = []
tokens (c : s)
  | elem c solo  = Sym [c] : tokens s
  | elem c spc   = let (i, b) = space 1 s in Spc i : tokens b
  | c == '\n'    = EoL : tokens s
  | otherwise    = let (a, b) = symb s in Sym (c : a) : tokens b
  where  
    spc = " \t"
    solo = "()[]{},;`"
    symb = break (`elem` ('\n' : spc ++ solo))
    space i (c : s)  | elem c spc   = space (i + 1) s
    space i s                       = (i, s)

-- You will note that we deliver only Spc, EoL and Sym tokens at this
-- stage. More structure comes later.

-- For diagnostic purposes, let us give a show instance for Token.
instance Show Token where
  show (Spc i)
    | i < 4      = replicate i ' '
    | otherwise  = "[" ++ show i ++ ">"
  show EoL = "\n"
  show (Sym x) = x
  show (Grp x ts y) = x ++ show ts ++ y
  show (Sub ts) = "-"


------------------------------------------------------------------------------
-- LAYOUT STRUCTURE
------------------------------------------------------------------------------

-- A document is a sequence of blocks. A block consists of a headline
-- (being a list of tokens), and the possibility of a subordinated
-- document, introduced by the one and only layout herald
--   -:
-- which looks like a horizontal thing followed by some vertical things.

type Document = [Block]
data Block
  = [Token] :-:          -- the headline
      Maybe Document     -- the subordinated document, if present
  deriving Show

headline :: Document -> [Token]
headline ((ts :-: _) : _) = ts
headline _                = []

-- The main interface to the layout machinery is via these operations
-- which are total. Moreover, for tab-free input
--   tuoyal . layout = id

layout :: String -> Document
tuoyal :: Document -> String

-- The purpose of layout is to discover useful structure, given the
-- constraints of the forgetful operation, tuoyal, implemented thus:

tuoyal ls = foldr blockOut [] ls where
  blockOut (ts :-: mls) s = foldr nekot (subDocOut mls s) ts
  subDocOut Nothing    s = s
  subDocOut (Just ls)  s = "-:" ++ foldr blockOut s ls

-- The key operation grabs the subdocument appropriate to the current
-- indentation level. It should be called only at start of line.

tokDoc  ::  Int          -- seek a document indented this much...
        ->  [Token]      -- ...from this token stream;
        ->  (  Document  -- return the document...
            ,  [Token]   -- ...and the unconsumed tokens
            )

-- We may then give the implementation of layout.

layout  =  fst        -- just the document, please! no tokens unused...
        .  tokDoc 0   -- ...making a document indented by 0, from...
        .  tokens     -- ... the tokens you get from the input

-- Now, to implement tokDoc, we need to detect indentation level,
-- just by a little lookahead. PROVIDED WE'RE AT BEGINNING OF LINE.

dent :: [Token] -> Int
dent []                 = maxBound  -- end of file, maximally indented
dent (EoL : _)          = maxBound  -- blank line, maximally indented
dent (Spc i : EoL : _)  = maxBound  -- trailing spaces only, same again
dent (Spc i : _)        = i         -- can't be followed by more space
dent _                  = 0         -- isn't space

tokDoc i ts | j < i      = ([], ts)  -- stop if we're outdented
            | otherwise  = moreDoc i ts where
  j = dent ts  -- makes sense only at start of line
  -- for moreDoc, we know that what we see belongs to us
  moreDoc i [] = ([], [])  -- end of file
  moreDoc i ts = ((groupify us :-: m) : ls, ts2) where
    --             ^^^^^^^^^^^ find bracket structure
    ((us :-: m),  ts1) = tokBlock ts   -- get the first block
    (ls,          ts2) = tokDoc i ts1  -- then the rest
  -- tokBlock gets us to the end of the current block, i.e., the
  -- start of the line after the current block
  tokBlock []              = ([] :-: Nothing, [])
    -- end of file is end of block
  tokBlock (EoL      : ts) | dent ts < j = ([EoL] :-: Nothing, ts)
    -- stop after EoL when what follows is an outdent
  tokBlock (Sym "-:" : ts) = ([] :-: Just ls, ts') where
    (ls, ts') = moreDoc (j + 1) ts
    -- we've seen the layout herald; anything right of it belongs
    -- to the subdoc, and anything below it indented strictly more
    -- than this line
  tokBlock (t        : ts) = ((t : ts1) :-: mls, ts2) where
    (ts1 :-: mls, ts2) = tokBlock ts
    -- otherwise keep grabbing more tokens

-- We're looking for opportunities to package token sequences in
-- group tokens. When you find an open, try to grab tokens until
-- the corresponding close. If you don't find it, don't panic...
-- ...but don't make a group.

groupify :: [Token] -> [Token]
groupify = fst . chomp (const False) where
  groupers = [("(", ")"), ("[", "]"), ("{", "}"), ("`", "`")]
  fcons t (ts, z) = (t : ts, z)
  -- chomp keeps making groups but stops at its caller's closer
  chomp  :: (Token -> Bool)  -- is this my caller's closer?
         -> [Token]          -- input stream
         -> ( [Token]        -- grouped inputs before the closer
            , Maybe [Token]  -- ungrouped inputs after the closer
            )                -- or Nothing, if we didn't find it
  chomp p []             = ([], Nothing)  -- didn't find closer
  chomp p (t : ts) | p t = ([], Just ts)  -- have found closer
  chomp p (t@(Sym x) : ts)  -- is this the start of a subgroup?
    | Just y <- lookup x groupers   -- if so, y closes x
    = case chomp (Sym y ==) ts of
        (ss, Just ts) -> fcons (Grp x ss y) (chomp p ts)
          -- we found the closer, so we can make a group
        (ss, Nothing) -> (t : ss, Nothing)
          -- we didn't find the closer, so we stay flat
  chomp p (t : ts) = fcons t (chomp p ts)  -- if not, chomp on
  

------------------------------------------------------------------------------
-- PARSING TOKENS (LIST OF SUCCESSES STYLE)
------------------------------------------------------------------------------

newtype ParseTokens a = ParseTokens
  {parseTokens :: [Token]                -- inputs
               -> [( [Token] -> [Token]  -- difference-list of consumed input
                   , a                   -- thing constructed
                   , [Token]             -- unused inputs
                   )]}
  deriving Monoid  -- why keep a dog and bark yourself?

-- Let us have a datatype for substructures carrying the token sequence
-- from which they were parsed. The purpose of Sub tokens is to mark
-- the corresponding discovered structure in the token sequence. As a
-- result, the consumed input may contain Sub tokens where the unconsumed
-- input may not.

data Sub x = [Token] := x deriving Show

subproj :: Sub x -> x
subproj (_ := x) = x


sub :: ParseTokens a -> ParseTokens (Sub a)
sub ap = ParseTokens $ \ ts -> do
  (ad, a, ts) <- parseTokens ap ts    -- parse the substructure
  let ats = ad []                     -- reify the difference-list...
  return ((Sub ats :), ats := a, ts)  -- ...and share it!
  
-- We can collect the parses which eat the input and reify their
-- difference lists. Note that ad [] will be ts with added structure.
parses :: ParseTokens a -> [Token] -> [([Token], a)]
parses ap ts = [(ad [], a) | (ad, a, []) <- parseTokens ap ts]

-- The Monad instance is standard.
instance Monad ParseTokens where
  return x = ParseTokens $ \ ts -> return (id, x, ts)
  pa >>= k = ParseTokens $ \ ts -> do     -- thread by shadowing
    (ad, a, ts) <- parseTokens pa ts
    (bd, b, ts) <- parseTokens (k a) ts
    return (ad . bd, b, ts)

-- boilerplate
instance Applicative ParseTokens where
  pure = return
  pf <*> pa = pf >>= \ f -> pa >>= \ a -> return (f a)
-- boilerplate
instance Functor ParseTokens where
  fmap = (<*>) . pure
-- boilerplate
instance Alternative ParseTokens where
  empty = mempty
  (<|>) = mappend

-- get the next token
tok :: ParseTokens Token
tok = ParseTokens $ \ ts -> case ts of
  t : ts -> [((t :), t, ts)]
  _ -> []

-- get the next symbol
sym :: ParseTokens String
sym = tok >>= \x -> case x of
  Sym x -> return x
  _     -> empty

-- demand a particular next symbol
eat :: String -> ParseTokens ()
eat x = do s <- sym; guard (x == s)

-- discard whitespace
gap :: ParseTokens ()
gap = ParseTokens $ \ ts ->
  let (ss, us) = span (<= EoL) ts in [((ss ++), (), us)]

-- grab a possibly empty sequence, allowing whitespace
gapMany :: ParseTokens a -> ParseTokens [a]
gapMany ap = gap *> many (ap <* gap)

-- parse a group with specific delimiters
grp :: String -> ParseTokens a -> String -> ParseTokens a
grp x ap y = ParseTokens $ \ ts -> case ts of
  t@(Grp x' gts y') : ts | x == x' && y == y' -> 
    [((Grp x ats y :), a, ts) | (ats, a) <- parses ap gts]
  _ -> []
-- (proposal: insist on the group delivering exactly one parse)

-- how to grow left-recursive stuff
grow  ::  Int                        -- minimum number of growings
      ->  ParseTokens a              -- what to grow
      ->  (Sub a -> ParseTokens a)   -- how to grow it
      ->  ParseTokens a              -- the fully grown thing
grow i ap kp = ParseTokens $ \ ts -> extend i (parseTokens ap ts) where
  extend 0 triples = (triples >>= more 0) ++ triples
  extend i triples = triples >>= more (i - 1)
  more i (ad, a, ts) = extend i
    [ ((Sub ats :) . bd, ab, ts)
    | (bd, ab, ts) <- parseTokens (kp (ats := a)) ts
    ] where ats = ad []

refine :: (a -> Maybe b) -> ParseTokens a -> ParseTokens b
refine f p = p >>= \a -> case f a of
  Nothing -> empty
  Just b  -> return b

------------------------------------------------------------------------------
-- PARSING DOCUMENTS
------------------------------------------------------------------------------

document :: Format x -> Document -> [[x]]  -- list of possible parses
document = traverse . formatBlock

data Format x where  -- this is a bit too uniform
  Format  :: (([Token], a) -> [b] -> x)  -- semantics
          -> ParseTokens a   -- parser for headlines
          -> Format b        -- format for subdocument blocks
          -> Format x        -- format for document blocks

formatBlock :: Format x -> Block -> [x]
formatBlock (Format f h l) (ts :-: mtss) =
  f <$> parses h ts <*> document l (fromMaybe [] mtss)

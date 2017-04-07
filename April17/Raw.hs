------------------------------------------------------------------------------
-----                                                                    -----
-----     Raw Syntax                                                     -----
-----                                                                    -----
------------------------------------------------------------------------------

{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators,
    TypeFamilies, PatternSynonyms, RankNTypes #-}

module Raw where

import Data.Char
import Control.Concurrent

import Utils


------------------------------------------------------------------------------
-- datatype of raw terms: deeply unsubtle
------------------------------------------------------------------------------

data Raw
  =  RA String         -- atoms (nonempty, legit characters)
  |  RB String Raw     -- bindings
  |  RC Raw (NEL Raw)  -- clumps have a head and a nonempty tail

instance Show Raw where
  show = wee where
    big (RA x)     = x
    big (RB x r)   = x ++ ". " ++ big r
    big (RC r rs)  = wee r ++ clu rs
    clu (Only r) = case r of
      RA x      -> " " ++ x
      RB x r    -> " " ++ x ++ ". " ++ big r
      RC r rs   -> "," ++ clu (r :-: rs)
    clu (r :-: rs) = " " ++ wee r ++ clu rs
    wee (RA x)         = x
    wee r              = "(" ++ big r ++ ")"


------------------------------------------------------------------------------
-- Grammar
------------------------------------------------------------------------------

{-
The only special characters in this syntax are
  ( ) , .
which are tokens by themselves. Other tokens (symbols) are as delimited by
specials and whitespace.

This syntax is designed to do very little analysis: just enough to give us
trees of terms with variable binding.

The basic picture is that we have

  raw ::= symbol             -- an atom, i.e., a tag or identifier
        | raw+               -- a clump of subterms
        | symbol. raw        -- binding
        | (symbol)           -- grouping for disambiguation

There are two extra subtleties:
  1. a binding which stands last in a clump needs no parens, e.g.,
       pi S x. blah de blah
     means
       (pi S (x. blah de blah))
  2. a "LISP-convention" favours the right-nested, e.g.,
       a b c, d e f
     means
       (a b c (d e f))
-}


------------------------------------------------------------------------------
-- The ReadLine interface, for parsing with one character lookahead
------------------------------------------------------------------------------

data RLState = Buff  -- there is one character in the lookahead buffer
             | Nuff  -- there is nothing in the lookahead buffer
             | Huff  -- we've run out of stuff

type family Buffy i where
  Buffy Buff = True
  Buffy i    = False

type family Nuffy i where
  Nuffy Nuff = True
  Nuffy i    = False

type family Huffy i where
  Huffy Huff = True
  Huffy i    = False

data ReadLine :: (RLState -> *) -> (RLState -> *) where
  Peek :: ReadLine (Peeking i) i
       -- peek if you like
  Grok :: ReadLine (() @= Nuff) Buff
       -- accept a character only if you've seen it (and you like it)
  Barf :: ReadLine x i
       -- complain (notionally, you should have a reason to, but sod it)

-- if you were peeking in state i, you might end up in state j
data Peeking (i :: RLState) (j :: RLState) where
  See :: Huffy i ~ False => Char -> Peeking i Buff
      -- if don't know you're at end-of-text, you might get a character
  EOT :: Buffy i ~ False => Peeking i Huff
      -- if you do know you're not at end-of-text, you won't get end-of-text

type READ x i = Prog ReadLine (Got x) i


------------------------------------------------------------------------------
-- parsing Raw with the ReadLine interface
------------------------------------------------------------------------------

-- to eat a raw term, eat a head then check for a tail
rawR :: READ Raw i
rawR = (headR />= tailR) />= \ rs -> case rs of
  Only r    -> rgturn r          -- if we get a singleton, that's it
  r :-: rs  -> rgturn (RC r rs)  -- otherwise, it's a clump

-- eat spaces until you see something that isn't
spcR :: READ () i
spcR = cmd Peek ?>= \ x -> case x of
  See c | isSpace c  -> cmd Grok @> spcR
  _                  -> rgturn ()

-- grab a valid small raw term (which might be mutated by what's after it)
headR :: READ Raw i
headR = spcR /> cmd Peek ?>= \ x -> case x of
    -- make an atom?
    See c | isAtomCh c  -> cmd Grok @> atomR />= \ s -> rgturn (RA (c : s))
    -- an open paren means we can give a big thing, then a close
    See '('             -> cmd Grok @> rawR />= \ r -> closeR /> rgturn r
    -- otherwise, it's crap
    _                   -> cmd Barf
  where
    -- close paren is required
    closeR :: READ () i
    closeR = spcR /> cmd Peek ?>= \ x -> case x of
      See ')'  -> cmd Grok @> rgturn ()
      _        -> cmd Barf

    -- characters allowed in atoms
    isAtomCh :: Char -> Bool
    isAtomCh c = (c > ' ') && not (elem c "().,")

    -- keep eating atomic characters
    atomR :: READ String i
    atomR = cmd Peek ?>= \ x -> case x of
      See c | isAtomCh c  -> cmd Grok @> atomR />= \ s -> rgturn (c : s)
      _                   -> rgturn ""


-- look after a head; returns a nonempty list that might be a clump
tailR :: Raw -> READ (NEL Raw) i
tailR r = spcR /> cmd Peek ?>= \ x -> case x of
  -- end of text or closing bracket means it's not a clump and we're done
  EOT      -> rgturn (Only r)
  See ')'  -> rgturn (Only r)
  -- dot means it's not a clump, it's a binding
  See '.' -> case r of
    RA x   -> cmd Grok @> rawR />= \ r -> rgturn (Only (RB x r))
    _      -> cmd Barf
  -- comma means the rest of the clump is just one thing
  See ','  -> cmd Grok @> rawR />= \ t -> rgturn (r :-: Only t)
  -- otherwise, whatever it is is more stuff for the clump
  See _    -> (headR />= tailR) />= \ rs -> rgturn (r :-: rs)


------------------------------------------------------------------------------
-- running the ReadLine interface on a String
------------------------------------------------------------------------------

data RLSTATE (i :: RLState) :: * where
  NUFF  :: String          -> RLSTATE Nuff
  BUFF  :: Char -> String  -> RLSTATE Buff
  HUFF  ::                    RLSTATE Huff

readString :: READ x i -> RLSTATE i -> Maybe x
readString (RET (Got x)) _             = Just x
readString (DO Peek k)  HUFF           = readString (k RET EOT)      HUFF
readString (DO Peek k) (NUFF "")       = readString (k RET EOT)      HUFF
readString (DO Peek k) (NUFF (c : s))  = readString (k RET (See c)) (BUFF c s)
readString (DO Peek k) (BUFF c s)      = readString (k RET (See c)) (BUFF c s)
readString (DO Grok k) (BUFF _ s)      = readString (k RET (At ())) (NUFF s)
readString (DO Barf _) _               = Nothing


------------------------------------------------------------------------------
-- parsing a String as a Raw
------------------------------------------------------------------------------

rawString :: String -> Maybe Raw
rawString = readString rawR . NUFF


------------------------------------------------------------------------------
-- The IO Handler
------------------------------------------------------------------------------

-- this should have NoBuffering and echo False

data ReadLog x
  = Log0 (READ x Nuff)
  | LogGrok (ReadLog x)
  | LogPeek (ReadLog x) (READ x Nuff)

data RLIOSTATE :: RLState -> * where
  IONUFF :: RLIOSTATE Nuff
  IOBUFF :: Char -> RLIOSTATE Buff

rlIO :: READ x Nuff -> IO x
rlIO r = logIO (Log0 r) r IONUFF

logIO :: ReadLog x -> READ x i -> RLIOSTATE i -> IO x
logIO log   (RET (Got x)) _          = return x
logIO log   (DO Peek k)   (IOBUFF c) = logIO log (k RET (See c)) (IOBUFF c)
logIO log p@(DO Peek k)    IONUFF    = do
  c <- getChar
  case c of
    '\b'   -> unlogIO log
    '\DEL' -> unlogIO log
    '\n'  -> case nullable p of
      Just x  -> return x
      Nothing -> logIO (LogPeek log p) (k RET (See '\n')) (IOBUFF '\n')
    c     -> logIO (LogPeek log p) (k RET (See c)) (IOBUFF c)
logIO log (DO Grok k) (IOBUFF c) = do
  putChar c
  logIO (LogGrok log) (k RET (At ())) IONUFF
logIO log (DO Barf _) _ = do
  curse
  unlogIO log

nullable :: Buffy i ~ False => READ x i -> Maybe x
nullable (RET (Got x)) = Just x
nullable (DO Barf _)   = Nothing
nullable (DO Peek k)   = nullable (k RET EOT)

curse :: IO ()
curse = mapM_ paf "!$!#!&!*!%!?!!!!!!!!!!!$!#!&!*!%!?! " where
  paf c = do
    putChar c
    threadDelay 2000
    putChar '\b'

unlogIO :: ReadLog x -> IO x
unlogIO (Log0 r) = rlIO r
unlogIO (LogGrok log) = do
  putStr "\b \b"
  unlogIO log
unlogIO (LogPeek log p) = logIO log p IONUFF

rawIO :: IO Raw
rawIO = rlIO rawR

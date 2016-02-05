module Raw where

import Control.Applicative

import Layout

data RawTm
  = RawAtom String
  | RawList [Sub RawTm] (Maybe (Sub RawTm))
  | RawLam  String (Sub RawTm)
  | RawEn   (Sub RawHd) [Sub RawTm]
  | RawComm (Sub RawTm) [Sub (Maybe RawSplice)]
  deriving Show

type RawSplice = RawTm

data RawHd
  = RawVar String
  | RawTy (Sub RawTm) (Sub RawTm)
  deriving Show

tag :: ParseTokens String
tag = sym >>= \ x -> case x of
  '\'' : s  -> return s
  _         -> empty

var :: ParseTokens String
var = sym >>= \ x -> case x of
  c : s | elem c "'\\" -> empty
  _ | elem ':' x -> empty
  _ -> return x

smallTm :: ParseTokens RawTm   -- definitely small
smallTm
  =    RawAtom <$> tag
  <|>  grp "[" (RawList <$> listTm <*>
                 (Just <$ eat "|" <* gap <*> sub bigTm <* gap
                  <|> pure Nothing)) "]"
  <|>  RawEn <$> sub smallHd <*> pure []
  <|>  grp "(" (gap *> bigTm <* gap) ")"

lamTm :: ParseTokens RawTm
lamTm = RawLam <$ eat "\\" <* gap <*> var <* gap <* eat "."
         <* gap <*> sub bigTm

listTm :: ParseTokens [Sub RawTm]
listTm = gap *> (ne <|> pure []) where
  ne =   (: []) <$> sub lamTm <* gap
     <|> (:) <$> sub smallTm <*> listTm

midTm :: ParseTokens RawTm   -- small or middle-sized
midTm = smallTm <|> lamTm

individual :: ParseTokens ()
individual = tok >>= \ t -> case t of
  Grp _ _ _ -> empty
  _         -> return ()

splice :: ParseTokens RawSplice
splice = bigTm

nonsense :: ParseTokens [Sub (Maybe RawSplice)]
nonsense = postnonsense <$> prenonsense
  where
  prenonsense :: ParseTokens [[Sub (Maybe RawSplice)]]
  prenonsense =
    many ((:[]) <$> sub (Just <$> grp "`" splice "`" <|> Nothing <$ individual)
          <|> regrp "(" ")" <|> regrp "[" "]" <|> regrp "{" "}")

  -- Glom together consecutive nothings and flatten
  postnonsense :: [[Sub (Maybe RawSplice)]] -> [Sub (Maybe RawSplice)]
  postnonsense = foldr
    (\x xs -> case (x,xs) of
      (ts := Nothing,ts' := Nothing : xs) -> (ts ++ ts') := Nothing : xs
      _                                   -> x : xs)
    [] . concat

  regrp :: String -> String -> ParseTokens [Sub (Maybe RawSplice)]
  regrp op cl = help <$> grp op nonsense cl
    where
    help :: [Sub (Maybe RawSplice)] -> [Sub (Maybe RawSplice)]
    help xs = ([ Sym op ] := Nothing : xs) ++ [[ Sym cl ] := Nothing]
    
bigTm :: ParseTokens RawTm   -- any term
bigTm = stuff <|> RawComm <$> sub stuff <* gap <* eat "--" <*> nonsense
  where
  stuff = midTm
    <|>  RawEn <$> sub smallHd <* gap
               <*> ((++)  <$> many (sub smallTm <* gap)
               <*> ((:[]) <$> sub midTm))

smallHd :: ParseTokens RawHd  -- definitely small
smallHd
  =    RawVar <$> var
  <|>  grp "(" (RawTy <$ gap <*> sub bigTm <* gap <* 
                eat ":"
                <* gap <*> sub bigTm <* gap) ")"

data RawTree = ([Token], RawTm) :& [RawTree] deriving Show

rawTreeFormat :: Format RawTree
rawTreeFormat = Format (:&) (gap *> bigTm <* gap) rawTreeFormat

rawTest :: String -> [[RawTree]]
rawTest = document rawTreeFormat . layout

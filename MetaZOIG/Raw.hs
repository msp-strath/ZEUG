module Raw where

import Control.Applicative

import Layout

data RawTm
  = RawTag   String
  | RawList  [Sub RawTm] (Maybe (Sub RawTm))
  | RawLam   String (Sub RawTm)
  | RawEn    RawEn
  deriving Show

data RawEn
  = RawVar String
  | RawApp (Sub RawEn) (Sub RawTm)
  | RawTy  (Sub RawTm) (Sub RawTm)
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
  =    RawTag <$> tag
  <|>  grp "[" (RawList <$> listTm <*>
                 (Just <$ eat "," <* gap <*> sub bigTm <* gap
                  <|> pure Nothing)) "]"
  <|>  RawEn <$> (RawVar <$> var)
  <|>  grp "(" (gap *> bigTm <* gap) ")"

lamTm :: ParseTokens RawTm
lamTm = RawLam <$ eat "\\" <* gap <*> var <* gap <* eat "."
         <* gap <*> sub midTm

listTm :: ParseTokens [Sub RawTm]
listTm = gap *> (ne <|> pure []) where
  ne =   (: []) <$> sub lamTm <* gap
     <|> (:) <$> sub smallTm <*> listTm

midTm :: ParseTokens RawTm   -- small or middle-sized
midTm = smallTm <|> lamTm <|> RawEn <$> midEn

bigTm :: ParseTokens RawTm   -- any term
bigTm
  =    midTm
  <|>  RawEn <$> bigEn

bigEn :: ParseTokens RawEn   -- definitely big
bigEn
  =    RawTy <$> sub midTm <* gap <* eat ":" <* gap <*> sub bigTm

midEn :: ParseTokens RawEn   -- definitely middle-sized
midEn = grow 1 smallEn $ \ f -> RawApp f <$ gap <*> sub smallTm

smallEn :: ParseTokens RawEn  -- definitely small
smallEn
  =    RawVar <$> var
  <|>  grp "(" (gap *> bigEn <* gap) ")"


data RawTree = RawTm :& [RawTree] deriving Show

rawTreeFormat :: Format RawTree
rawTreeFormat = Format (:&) (gap *> bigTm <* gap) rawTreeFormat

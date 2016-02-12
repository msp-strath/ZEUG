module Raw where

import Control.Applicative
import Data.List.Split

import Layout

type Naming = String

type NameStep = (Naming, Int)
type RawLongName = (NameStep, [NameStep])

getRawLongName :: String -> Maybe RawLongName
getRawLongName s =
  do
    x:xs <- traverse splitHat (splitOn "." s)
    return (x,xs)
  where
  splitHat :: String -> Maybe NameStep
  splitHat s = case splitOn "^" s of
    [s]   -> Just (s,0)
    [s,i] -> case reads i of
      [(i,"")] -> Just (s,i)
      _        -> Nothing
    _     -> Nothing

data RawModule
  = RawTip     (Sub RawTip)
  | RawParam   (String, Sub RawTm)     (Sub RawModule)
  | RawSubMod  (String, Sub RawModule) (Sub RawModule)
  | RawModComm [Sub (Maybe RawSplice)] (Sub RawModule)
  deriving Show

data RawTip
  = RawBlank
  | RawDefn (Either (Sub RawHole) (Sub RawTm)) (Sub RawTm)
  deriving Show
           
data RawHole
  = RawQuestionMark
  deriving Show
           
data RawTm
  = RawAtom String
  | RawList [Sub RawTm] (Maybe (Sub RawTm))
  | RawLam  String (Sub RawTm)
  | RawEn   (Sub RawHd) [Sub RawTm]
  | RawComm (Sub RawTm) [Sub (Maybe RawSplice)]
  deriving Show

type RawSplice = RawTm

data RawHd
  = RawVar  RawLongName
  | RawTy (Sub RawTm) (Sub RawTm)
  deriving Show

tag :: ParseTokens String
tag = sym >>= \ x -> case x of
  '\'' : s  -> return s
  _         -> empty

var :: ParseTokens String
var = sym >>= \ x -> case x of
  c : s | elem c "'\\-" -> empty
  _ | elem ':' x -> empty
  _ -> return x

bigMod :: ParseTokens RawModule
bigMod = id <$ gap <*> (RawTip <$> sub smallTip
   <|> RawParam <$> (grp "(" ((,) <$ gap <*> var <* gap <*
                              eat ":" <* gap <*> sub bigTm <* gap )  ")")
                <*> sub bigMod
   <|> RawSubMod <$> (grp "{" ((,) <$ gap <*> var <* gap
                              <*> sub bigMod <* gap )  "}")
                <*> sub bigMod
   <|> RawModComm <$> (grp "{" (id <$ eat "-" <*> nonsense <* eat "-")  "}")
                <*> sub bigMod)

holeOrDef :: ParseTokens (Either (Sub RawHole) (Sub RawTm))
holeOrDef = Left <$> sub hole <|> Right <$> sub bigTm

hole :: ParseTokens RawHole
hole = RawQuestionMark <$ eat "?"

smallTip :: ParseTokens RawTip
smallTip = id <$ gap <*> (pure RawBlank
   <|> RawDefn <$ eat "=" <* gap <*> holeOrDef <* gap <*
     eat ":" <* gap <*> sub bigTm <* gap)

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
  =    RawVar <$> refine getRawLongName var
  <|>  grp "(" (RawTy <$ gap <*> sub bigTm <* gap <* 
                eat ":"
                <* gap <*> sub bigTm <* gap) ")"

data RawTree = ([Token], RawTm) :&&: [RawTree] deriving Show

rawTreeFormat :: Format RawTree
rawTreeFormat = Format (:&&:) (gap *> bigTm <* gap) rawTreeFormat

rawTest :: String -> [[RawTree]]
rawTest = document rawTreeFormat . layout

-- parses nonsense (headline (layout "blah ( bler        )       berr"))
-- parses bigMod (headline (layout ""))
-- parses bigMod (headline (layout "(x : S)"))
-- parses bigMod (headline (layout "(x : S){x}"))
-- parses bigMod (headline (layout "(x : S){x = hello : world}"))

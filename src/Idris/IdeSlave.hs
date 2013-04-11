{-# LANGUAGE FlexibleInstances, IncoherentInstances #-}

module Idris.IdeSlave(receiveMessage, sendMessage, IdeSlaveCommand(..)) where

import Text.Printf
import Numeric
import Data.List
-- import qualified Data.Text as T
import Text.Parsec

data SExp = List [SExp]
          | StringAtom String
          | BoolAtom Bool
          | IntegerAtom Integer
          | SymbolAtom String
          deriving ( Eq, Show )

sExpToString :: SExp -> String
sExpToString (StringAtom s)   = "\"" ++ escape s ++ "\""
sExpToString (BoolAtom True)  = ":True"
sExpToString (BoolAtom False) = ":False"
sExpToString (IntegerAtom i)  = printf "%d" i
sExpToString (SymbolAtom s)   = ":" ++ s
sExpToString (List l)         = "(" ++ intercalate " " (map sExpToString l) ++ ")"

class SExpable a where
  toSExp :: a -> SExp

instance SExpable Bool where
  toSExp True  = BoolAtom True
  toSExp False = BoolAtom False

instance SExpable String where
  toSExp s = StringAtom s

instance SExpable Integer where
  toSExp n = IntegerAtom n

instance SExpable Int where
  toSExp n = IntegerAtom (toInteger n)

instance (SExpable a) => SExpable (Maybe a) where
  toSExp Nothing  = List [SymbolAtom "Nothing"]
  toSExp (Just a) = List [SymbolAtom "Just", toSExp a]

instance (SExpable a) => SExpable [a] where
  toSExp l = List (map toSExp l)

escape :: String -> String
escape = concatMap escapeChar
  where
    escapeChar '\\' = "\\\\"
    escapeChar '"'  = "\\\""
    escapeChar c    = [c]

pSExp = do xs <- between (char '(') (char ')') (pSExp `sepBy` (char ' '))
           return (List xs)
    <|> atom

atom = do char ':'; x <- atomC; return x
   <|> do char '"'; xs <- many quotedChar; char '"'; return (StringAtom xs)
   <|> do ints <- many1 digit
          case readDec ints of
            ((num, ""):_) -> return (IntegerAtom (toInteger num))
            _ -> return (StringAtom ints)

atomC = do string "True"; return (BoolAtom True)
    <|> do string "False"; return (BoolAtom False)
    <|> do xs <- many (noneOf " \n\t\r\"()"); return (SymbolAtom xs)

quotedChar = noneOf "\""
         <|> try (string "\\\"" >> return '"')

parseSExp :: String -> Either ParseError SExp
parseSExp input = parse pSExp "(unknown)" input

data IdeSlaveCommand = Version
                     | Interpret String
  deriving Show

sexpToCommand :: SExp -> Maybe IdeSlaveCommand
sexpToCommand (List (x:[]))                                    = sexpToCommand x
sexpToCommand (List [SymbolAtom "interpret", StringAtom cmd]) = Just (Interpret cmd)
sexpToCommand (SymbolAtom "version")                           = Just Version
sexpToCommand _                                                = Nothing

receiveMessage :: IO (Maybe IdeSlaveCommand)
receiveMessage
  = do x <- getLine
       return (receiveString x)

receiveString :: String -> Maybe IdeSlaveCommand
receiveString x =
  case readHex (take 6 x) of
    ((num, ""):_) ->
      let msg = drop 6 x in
        if (length msg) /= (num - 1)
           then error "bad input length"
           else parseSExpToCommand msg
    _ -> error "readHex failed"

parseSExpToCommand :: String -> Maybe IdeSlaveCommand
parseSExpToCommand msg =
  case parseSExp msg of
    Left _  -> error "parse failure"
    Right r -> sexpToCommand r

sendMessage :: SExpable a => a -> IO ()
sendMessage s =
  do let str = convertToSExpString s
     putStrLn $ (getHexLength str) ++ str

convertToSExpString :: SExpable a => a -> String
convertToSExpString s =
  let str = sExpToString (toSExp s) in
    if (str !! 0) == '('
        then str
        else "(" ++ str ++ ")"

getHexLength :: String -> String
getHexLength s = printf "%06x" (1 + (length s))

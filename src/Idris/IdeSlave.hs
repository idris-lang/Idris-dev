{-# LANGUAGE FlexibleInstances, IncoherentInstances #-}

module Idris.IdeSlave(parseMessage, convSExp, IdeSlaveCommand(..), sexpToCommand, toSExp, SExp(..)) where

import Text.Printf
import Numeric
import Data.List
-- import qualified Data.Text as T
import Text.Parsec

data SExp = SexpList [SExp]
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
sExpToString (SexpList l)     = "(" ++ intercalate " " (map sExpToString l) ++ ")"

class SExpable a where
  toSExp :: a -> SExp

instance SExpable SExp where
  toSExp a = a

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
  toSExp Nothing  = SexpList [SymbolAtom "Nothing"]
  toSExp (Just a) = SexpList [SymbolAtom "Just", toSExp a]

instance (SExpable a) => SExpable [a] where
  toSExp l = SexpList (map toSExp l)

instance (SExpable a, SExpable b) => SExpable (a, b) where
  toSExp (l, r) = SexpList [toSExp l, toSExp r]

instance (SExpable a, SExpable b, SExpable c) => SExpable (a, b, c) where
  toSExp (l, m, n) = SexpList [toSExp l, toSExp m, toSExp n]

escape :: String -> String
escape = concatMap escapeChar
  where
    escapeChar '\\' = "\\\\"
    escapeChar '"'  = "\\\""
    escapeChar c    = [c]

pSExp = do xs <- between (char '(') (char ')') (pSExp `sepBy` (char ' '))
           return (SexpList xs)
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

quotedChar = try (string "\\\\" >> return '\\')
         <|> try (string "\\\"" >> return '"')
         <|> noneOf "\""

parseSExp :: String -> Either ParseError SExp
parseSExp = parse pSExp "(unknown)"

data IdeSlaveCommand = REPLCompletions String
                     | Interpret String
                     | LoadFile String
  deriving Show

sexpToCommand :: SExp -> Maybe IdeSlaveCommand
sexpToCommand (SexpList (x:[]))                                             = sexpToCommand x
sexpToCommand (SexpList [SymbolAtom "interpret", StringAtom cmd])           = Just (Interpret cmd)
sexpToCommand (SexpList [SymbolAtom "repl-completions", StringAtom prefix]) = Just (REPLCompletions prefix)
sexpToCommand (SexpList [SymbolAtom "load-file", StringAtom filename])      = Just (LoadFile filename)
sexpToCommand _                                                             = Nothing

parseMessage :: String -> (SExp, Integer)
parseMessage x = case receiveString x of
                      (SexpList [cmd, (IntegerAtom id)]) ->
                        (cmd, id)

receiveString :: String -> SExp
receiveString x =
  case readHex (take 6 x) of
    ((num, ""):_) ->
      let msg = drop 6 x in
        if (length msg) /= (num - 1)
           then error "bad input length"
           else (case parseSExp msg of
                      Left _ -> error "parse failure"
                      Right r -> r)
    _ -> error "readHex failed"

convSExp :: SExpable a => String -> a -> Integer -> String
convSExp pre s id =
  let sex = SexpList [SymbolAtom pre, toSExp s, IntegerAtom id] in
      let str = sExpToString sex in
          (getHexLength str) ++ str

getHexLength :: String -> String
getHexLength s = printf "%06x" (1 + (length s))

{-# LANGUAGE FlexibleInstances, IncoherentInstances, PatternGuards #-}

module Idris.IdeSlave(parseMessage, convSExp, IdeSlaveCommand(..), sexpToCommand, toSExp, SExp(..), SExpable, Opt(..)) where

import Text.Printf
import Numeric
import Data.List
import qualified Data.ByteString.UTF8 as UTF8
-- import qualified Data.Text as T
import Text.Trifecta hiding (Err)
import Text.Trifecta.Delta

import Idris.Core.TT

import Control.Applicative

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


instance SExpable Name where
  toSExp s = StringAtom (show s)


instance (SExpable a) => SExpable (Maybe a) where
  toSExp Nothing  = SexpList [SymbolAtom "Nothing"]
  toSExp (Just a) = SexpList [SymbolAtom "Just", toSExp a]

instance (SExpable a) => SExpable [a] where
  toSExp l = SexpList (map toSExp l)

instance (SExpable a, SExpable b) => SExpable (a, b) where
  toSExp (l, r) = SexpList [toSExp l, toSExp r]

instance (SExpable a, SExpable b, SExpable c) => SExpable (a, b, c) where
  toSExp (l, m, n) = SexpList [toSExp l, toSExp m, toSExp n]

instance (SExpable a, SExpable b, SExpable c, SExpable d) => SExpable (a, b, c, d) where
  toSExp (l, m, n, o) = SexpList [toSExp l, toSExp m, toSExp n, toSExp o]

instance (SExpable a, SExpable b, SExpable c, SExpable d, SExpable e) =>
         SExpable (a, b, c, d, e) where
   toSExp (l, m, n, o, p) = SexpList [toSExp l, toSExp m, toSExp n, toSExp o, toSExp p]

instance SExpable NameOutput where
  toSExp TypeOutput    = SymbolAtom "type"
  toSExp FunOutput     = SymbolAtom "function"
  toSExp DataOutput    = SymbolAtom "data"
  toSExp MetavarOutput = SymbolAtom "metavar"

maybeProps :: SExpable a => [(String, Maybe a)] -> [(SExp, SExp)]
maybeProps [] = []
maybeProps ((n, Just p):ps) = (SymbolAtom n, toSExp p) : maybeProps ps
maybeProps ((n, Nothing):ps) = maybeProps ps

instance SExpable OutputAnnotation where
  toSExp (AnnName n ty d t) = toSExp $ [(SymbolAtom "name", StringAtom (show n)),
                                        (SymbolAtom "implicit", BoolAtom False)] ++
                                       maybeProps [("decor", ty)] ++
                                       maybeProps [("doc-overview", d), ("type", t)]
  toSExp (AnnBoundName n imp)    = toSExp [(SymbolAtom "name", StringAtom (show n)),
                                           (SymbolAtom "decor", SymbolAtom "bound"),
                                           (SymbolAtom "implicit", BoolAtom imp)]
  toSExp AnnConstData            = toSExp [(SymbolAtom "decor", SymbolAtom "data")]
  toSExp AnnConstType            = toSExp [(SymbolAtom "decor", SymbolAtom "type")]
  toSExp AnnKeyword              = toSExp [(SymbolAtom "decor", SymbolAtom "keyword")]
  toSExp (AnnFC (FC f (sl, sc) (el, ec)))      = toSExp [(SymbolAtom "source-loc",
                                                    ((SymbolAtom "filename", StringAtom f),
                                                     (SymbolAtom "start",  IntegerAtom (toInteger sl), IntegerAtom (toInteger sc)),
                                                     (SymbolAtom "end", IntegerAtom (toInteger el), IntegerAtom (toInteger ec))))]
  toSExp (AnnTextFmt fmt) = toSExp [(SymbolAtom "text-formatting", SymbolAtom format)]
      where format = case fmt of
                       BoldText      -> "bold"
                       ItalicText    -> "italic"
                       UnderlineText -> "underline"

escape :: String -> String
escape = concatMap escapeChar
  where
    escapeChar '\\' = "\\\\"
    escapeChar '"'  = "\\\""
    escapeChar c    = [c]

pSExp = do xs <- between (char '(') (char ')') (pSExp `sepBy` (char ' '))
           return (SexpList xs)
    <|> atom

atom = do string "nil"; return (SexpList [])
   <|> do char ':'; x <- atomC; return x
   <|> do char '"'; xs <- many quotedChar; char '"'; return (StringAtom xs)
   <|> do ints <- some digit
          case readDec ints of
            ((num, ""):_) -> return (IntegerAtom (toInteger num))
            _ -> return (StringAtom ints)

atomC = do string "True"; return (BoolAtom True)
    <|> do string "False"; return (BoolAtom False)
    <|> do xs <- many (noneOf " \n\t\r\"()"); return (SymbolAtom xs)

quotedChar = try (string "\\\\" >> return '\\')
         <|> try (string "\\\"" >> return '"')
         <|> noneOf "\""

parseSExp :: String -> Result SExp
parseSExp = parseString pSExp (Directed (UTF8.fromString "(unknown)") 0 0 0 0)

data Opt = ShowImpl | ErrContext deriving Show

data IdeSlaveCommand = REPLCompletions String
                     | Interpret String
                     | TypeOf String
                     | CaseSplit Int String
                     | AddClause Int String
                     | AddProofClause Int String
                     | AddMissing Int String
                     | MakeWithBlock Int String
                     | ProofSearch Int String [String]
                     | LoadFile String
                     | DocsFor String
                     | Apropos String
                     | GetOpts
                     | SetOpt Opt Bool
                     | Metavariables Int -- ^^ the Int is the column count for pretty-printing
  deriving Show

sexpToCommand :: SExp -> Maybe IdeSlaveCommand
sexpToCommand (SexpList (x:[]))                                                         = sexpToCommand x
sexpToCommand (SexpList [SymbolAtom "interpret", StringAtom cmd])                       = Just (Interpret cmd)
sexpToCommand (SexpList [SymbolAtom "repl-completions", StringAtom prefix])             = Just (REPLCompletions prefix)
sexpToCommand (SexpList [SymbolAtom "load-file", StringAtom filename])                  = Just (LoadFile filename)
sexpToCommand (SexpList [SymbolAtom "type-of", StringAtom name])                        = Just (TypeOf name)
sexpToCommand (SexpList [SymbolAtom "case-split", IntegerAtom line, StringAtom name])   = Just (CaseSplit (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-clause", IntegerAtom line, StringAtom name])   = Just (AddClause (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-proof-clause", IntegerAtom line, StringAtom name])   = Just (AddProofClause (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-missing", IntegerAtom line, StringAtom name])  = Just (AddMissing (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "make-with", IntegerAtom line, StringAtom name])    = Just (MakeWithBlock (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "proof-search", IntegerAtom line, StringAtom name, SexpList hintexp]) | Just hints <- getHints hintexp = Just (ProofSearch (fromInteger line) name hints)
  where getHints = mapM (\h -> case h of
                                 StringAtom s -> Just s
                                 _            -> Nothing)
sexpToCommand (SexpList [SymbolAtom "docs-for", StringAtom name])                       = Just (DocsFor name)
sexpToCommand (SexpList [SymbolAtom "apropos", StringAtom search])                      = Just (Apropos search)
sexpToCommand (SymbolAtom "get-options")                                                = Just GetOpts
sexpToCommand (SexpList [SymbolAtom "set-option", SymbolAtom s, BoolAtom b])
  | Just opt <- lookup s opts                                                           = Just (SetOpt opt b)
    where opts = [("show-implicits", ShowImpl), ("error-context", ErrContext)] --TODO support more
sexpToCommand (SexpList [SymbolAtom "metavariables", IntegerAtom cols])                 = Just (Metavariables (fromIntegral cols))
sexpToCommand _                                                                         = Nothing

parseMessage :: String -> Either Err (SExp, Integer)
parseMessage x = case receiveString x of
                   Right (SexpList [cmd, (IntegerAtom id)]) -> Right (cmd, id)
                   Left err -> Left err

receiveString :: String -> Either Err SExp
receiveString x =
  case readHex (take 6 x) of
    ((num, ""):_) ->
      let msg = drop 6 x in
        if (length msg) /= (num - 1)
           then Left . Msg $ "bad input length"
           else (case parseSExp msg of
                      Failure _ -> Left . Msg $ "parse failure"
                      Success r -> Right r)
    _ -> Left . Msg $ "readHex failed"

convSExp :: SExpable a => String -> a -> Integer -> String
convSExp pre s id =
  let sex = SexpList [SymbolAtom pre, toSExp s, IntegerAtom id] in
      let str = sExpToString sex in
          (getHexLength str) ++ str

getHexLength :: String -> String
getHexLength s = printf "%06x" (1 + (length s))

{-|
Module      : Idris.IdeMode
Description : Idris' IDE Mode
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-# LANGUAGE FlexibleInstances, IncoherentInstances, PatternGuards #-}

module Idris.IdeMode(parseMessage, convSExp, WhatDocs(..), IdeModeCommand(..), sexpToCommand, toSExp, SExp(..), SExpable, Opt(..), ideModeEpoch, getLen, getNChar, sExpToString) where

import Idris.Core.Binary
import Idris.Core.TT

import Control.Applicative hiding (Const)
import qualified Data.Binary as Binary
import qualified Data.ByteString.Base64 as Base64
import qualified Data.ByteString.Lazy as Lazy
import qualified Data.ByteString.UTF8 as UTF8
import Data.List
import Data.Maybe (isJust)
import qualified Data.Text as T
import Numeric
import System.IO
import Text.Printf
import Text.Trifecta hiding (Err)
import Text.Trifecta.Delta

getNChar :: Handle -> Int -> String -> IO (String)
getNChar _ 0 s = return (reverse s)
getNChar h n s = do c <- hGetChar h
                    getNChar h (n - 1) (c : s)

getLen :: Handle -> IO (Either Err Int)
getLen h = do s <- getNChar h 6 ""
              case readHex s of
                ((num, ""):_) -> return $ Right num
                _             -> return $ Left . Msg $ "Couldn't read length " ++ s

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
  toSExp TypeOutput      = SymbolAtom "type"
  toSExp FunOutput       = SymbolAtom "function"
  toSExp DataOutput      = SymbolAtom "data"
  toSExp MetavarOutput   = SymbolAtom "metavar"
  toSExp PostulateOutput = SymbolAtom "postulate"

maybeProps :: SExpable a => [(String, Maybe a)] -> [(SExp, SExp)]
maybeProps [] = []
maybeProps ((n, Just p):ps) = (SymbolAtom n, toSExp p) : maybeProps ps
maybeProps ((n, Nothing):ps) = maybeProps ps

constTy :: Const -> String
constTy (I _) = "Int"
constTy (BI _) = "Integer"
constTy (Fl _) = "Double"
constTy (Ch _) = "Char"
constTy (Str _) = "String"
constTy (B8 _) = "Bits8"
constTy (B16 _) = "Bits16"
constTy (B32 _) = "Bits32"
constTy (B64 _) = "Bits64"
constTy _ = "Type"

namespaceOf :: Name -> Maybe String
namespaceOf (NS _ ns) = Just (intercalate "." $ reverse (map T.unpack ns))
namespaceOf _         = Nothing

instance SExpable OutputAnnotation where
  toSExp (AnnName n ty d t) = toSExp $ [(SymbolAtom "name", StringAtom (show n)),
                                        (SymbolAtom "implicit", BoolAtom False)] ++
                                       maybeProps [("decor", ty)] ++
                                       maybeProps [("doc-overview", d), ("type", t)] ++
                                       maybeProps [("namespace", namespaceOf n)]
  toSExp (AnnBoundName n imp)    = toSExp [(SymbolAtom "name", StringAtom (show n)),
                                           (SymbolAtom "decor", SymbolAtom "bound"),
                                           (SymbolAtom "implicit", BoolAtom imp)]
  toSExp (AnnConst c)            = toSExp [(SymbolAtom "decor",
                                            SymbolAtom (if constIsType c then "type" else "data")),
                                           (SymbolAtom "type", StringAtom (constTy c)),
                                           (SymbolAtom "doc-overview", StringAtom (constDocs c)),
                                           (SymbolAtom "name", StringAtom (show c))]
  toSExp (AnnData ty doc)        = toSExp [(SymbolAtom "decor", SymbolAtom "data"),
                                           (SymbolAtom "type", StringAtom ty),
                                           (SymbolAtom "doc-overview", StringAtom doc)]
  toSExp (AnnType name doc)      = toSExp $ [(SymbolAtom "decor", SymbolAtom "type"),
                                             (SymbolAtom "type", StringAtom "Type"),
                                             (SymbolAtom "doc-overview", StringAtom doc)] ++
                                             if not (null name) then [(SymbolAtom "name", StringAtom name)] else []
  toSExp AnnKeyword              = toSExp [(SymbolAtom "decor", SymbolAtom "keyword")]
  toSExp (AnnFC fc)      = toSExp [(SymbolAtom "source-loc", toSExp fc)]
  toSExp (AnnTextFmt fmt) = toSExp [(SymbolAtom "text-formatting", SymbolAtom format)]
      where format = case fmt of
                       BoldText      -> "bold"
                       ItalicText    -> "italic"
                       UnderlineText -> "underline"
  toSExp (AnnLink url) = toSExp [(SymbolAtom "link-href", StringAtom url)]
  toSExp (AnnTerm bnd tm)
    | termSmallerThan 1000 tm = toSExp [(SymbolAtom "tt-term", StringAtom (encodeTerm bnd tm))]
    | otherwise = SexpList []
  toSExp (AnnSearchResult ordr) = toSExp [(SymbolAtom "doc-overview",
      StringAtom ("Result type is " ++ descr))]
      where descr = case ordr of
              EQ -> "isomorphic"
              LT -> "more general than searched type"
              GT -> "more specific than searched type"
  toSExp (AnnErr e) = toSExp [(SymbolAtom "error", StringAtom (encodeErr e))]
  toSExp (AnnNamespace ns file) =
    toSExp $ [(SymbolAtom "namespace", StringAtom (intercalate "." (map T.unpack ns)))] ++
             [(SymbolAtom "decor", SymbolAtom $ if isJust file then "module" else "namespace")] ++
             maybeProps [("source-file", file)]
  toSExp AnnQuasiquote = toSExp [(SymbolAtom "quasiquotation", True)]
  toSExp AnnAntiquote = toSExp [(SymbolAtom "antiquotation", True)]

encodeTerm :: [(Name, Bool)] -> Term -> String
encodeTerm bnd tm = UTF8.toString . Base64.encode . Lazy.toStrict . Binary.encode $
                    (bnd, tm)

decodeTerm :: String -> ([(Name, Bool)], Term)
decodeTerm = Binary.decode . Lazy.fromStrict . Base64.decodeLenient . UTF8.fromString

encodeErr :: Err -> String
encodeErr e = UTF8.toString . Base64.encode . Lazy.toStrict . Binary.encode $ e

decodeErr :: String -> Err
decodeErr = Binary.decode . Lazy.fromStrict . Base64.decodeLenient . UTF8.fromString

instance SExpable FC where
  toSExp (FC f (sl, sc) (el, ec)) =
    toSExp ((SymbolAtom "filename", StringAtom f),
            (SymbolAtom "start",  IntegerAtom (toInteger sl), IntegerAtom (toInteger sc)),
            (SymbolAtom "end", IntegerAtom (toInteger el), IntegerAtom (toInteger ec)))
  toSExp NoFC = toSExp ([] :: [String])
  toSExp (FileFC f) = toSExp [(SymbolAtom "filename", StringAtom f)]

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

data WhatDocs = Overview | Full

data IdeModeCommand = REPLCompletions String
                    | Interpret String
                    | TypeOf String
                    | CaseSplit Int String
                    | AddClause Int String
                    | AddProofClause Int String
                    | AddMissing Int String
                    | MakeWithBlock Int String
                    | MakeCaseBlock Int String
                    | ProofSearch Bool Int String [String] (Maybe Int) -- ^^ Recursive?, line, name, hints, depth
                    | MakeLemma Int String
                    | LoadFile String (Maybe Int)
                    | DocsFor String WhatDocs
                    | Apropos String
                    | GetOpts
                    | SetOpt Opt Bool
                    | Metavariables Int -- ^^ the Int is the column count for pretty-printing
                    | WhoCalls String
                    | CallsWho String
                    | BrowseNS String
                    | TermNormalise [(Name, Bool)] Term
                    | TermShowImplicits [(Name, Bool)] Term
                    | TermNoImplicits [(Name, Bool)] Term
                    | TermElab [(Name, Bool)] Term
                    | PrintDef String
                    | ErrString Err
                    | ErrPPrint Err
                    | GetIdrisVersion

sexpToCommand :: SExp -> Maybe IdeModeCommand
sexpToCommand (SexpList ([x]))                                                              = sexpToCommand x
sexpToCommand (SexpList [SymbolAtom "interpret", StringAtom cmd])                           = Just (Interpret cmd)
sexpToCommand (SexpList [SymbolAtom "repl-completions", StringAtom prefix])                 = Just (REPLCompletions prefix)
sexpToCommand (SexpList [SymbolAtom "load-file", StringAtom filename, IntegerAtom line])    = Just (LoadFile filename (Just (fromInteger line)))
sexpToCommand (SexpList [SymbolAtom "load-file", StringAtom filename])                      = Just (LoadFile filename Nothing)
sexpToCommand (SexpList [SymbolAtom "type-of", StringAtom name])                            = Just (TypeOf name)
sexpToCommand (SexpList [SymbolAtom "case-split", IntegerAtom line, StringAtom name])       = Just (CaseSplit (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-clause", IntegerAtom line, StringAtom name])       = Just (AddClause (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-proof-clause", IntegerAtom line, StringAtom name]) = Just (AddProofClause (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "add-missing", IntegerAtom line, StringAtom name])      = Just (AddMissing (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "make-with", IntegerAtom line, StringAtom name])        = Just (MakeWithBlock (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "make-case", IntegerAtom line, StringAtom name])        = Just (MakeCaseBlock (fromInteger line) name)
-- The Boolean in ProofSearch means "search recursively"
-- If it's False, that means "refine", i.e. apply the name and fill in any
-- arguments which can be done by unification.
sexpToCommand (SexpList (SymbolAtom "proof-search" : IntegerAtom line : StringAtom name : rest))
  | [] <- rest = Just (ProofSearch True (fromInteger line) name [] Nothing)
  | [SexpList hintexp] <- rest
  ,  Just hints <- getHints hintexp = Just (ProofSearch True (fromInteger line) name hints Nothing)
  | [SexpList hintexp, IntegerAtom depth] <- rest
 , Just hints <- getHints hintexp = Just (ProofSearch True (fromInteger line) name hints (Just (fromInteger depth)))
 where getHints = mapM (\h -> case h of
                                StringAtom s -> Just s
                                _            -> Nothing)
sexpToCommand (SexpList [SymbolAtom "make-lemma", IntegerAtom line, StringAtom name])   = Just (MakeLemma (fromInteger line) name)
sexpToCommand (SexpList [SymbolAtom "refine", IntegerAtom line, StringAtom name, StringAtom hint]) = Just (ProofSearch False (fromInteger line) name [hint] Nothing)
sexpToCommand (SexpList [SymbolAtom "docs-for", StringAtom name])                       = Just (DocsFor name Full)
sexpToCommand (SexpList [SymbolAtom "docs-for", StringAtom name, SymbolAtom s])
  | Just w <- lookup s opts                                                             = Just (DocsFor name w)
    where opts = [("overview", Overview), ("full", Full)]
sexpToCommand (SexpList [SymbolAtom "apropos", StringAtom search])                      = Just (Apropos search)
sexpToCommand (SymbolAtom "get-options")                                                = Just GetOpts
sexpToCommand (SexpList [SymbolAtom "set-option", SymbolAtom s, BoolAtom b])
  | Just opt <- lookup s opts                                                           = Just (SetOpt opt b)
    where opts = [("show-implicits", ShowImpl), ("error-context", ErrContext)] --TODO support more options. Issue #1611 in the Issue tracker. https://github.com/idris-lang/Idris-dev/issues/1611
sexpToCommand (SexpList [SymbolAtom "metavariables", IntegerAtom cols])                 = Just (Metavariables (fromIntegral cols))
sexpToCommand (SexpList [SymbolAtom "who-calls", StringAtom name])                      = Just (WhoCalls name)
sexpToCommand (SexpList [SymbolAtom "calls-who", StringAtom name])                      = Just (CallsWho name)
sexpToCommand (SexpList [SymbolAtom "browse-namespace", StringAtom ns])                 = Just (BrowseNS ns)
sexpToCommand (SexpList [SymbolAtom "normalise-term", StringAtom encoded])              = let (bnd, tm) = decodeTerm encoded in
                                                                                          Just (TermNormalise bnd tm)
sexpToCommand (SexpList [SymbolAtom "show-term-implicits", StringAtom encoded])         = let (bnd, tm) = decodeTerm encoded in
                                                                                          Just (TermShowImplicits bnd tm)
sexpToCommand (SexpList [SymbolAtom "hide-term-implicits", StringAtom encoded])         = let (bnd, tm) = decodeTerm encoded in
                                                                                          Just (TermNoImplicits bnd tm)
sexpToCommand (SexpList [SymbolAtom "elaborate-term", StringAtom encoded])              = let (bnd, tm) = decodeTerm encoded in
                                                                                          Just (TermElab bnd tm)
sexpToCommand (SexpList [SymbolAtom "print-definition", StringAtom name])               = Just (PrintDef name)
sexpToCommand (SexpList [SymbolAtom "error-string", StringAtom encoded])                = Just . ErrString . decodeErr $ encoded
sexpToCommand (SexpList [SymbolAtom "error-pprint", StringAtom encoded])                = Just . ErrPPrint . decodeErr $ encoded
sexpToCommand (SymbolAtom "version")                                                    = Just GetIdrisVersion
sexpToCommand _                                                                         = Nothing

parseMessage :: String -> Either Err (SExp, Integer)
parseMessage x = case receiveString x of
                   Right (SexpList [cmd, (IntegerAtom id)]) -> Right (cmd, id)
                   Right x -> Left . Msg $ "Invalid message " ++ show x
                   Left err -> Left err

receiveString :: String -> Either Err SExp
receiveString x =
  case parseSExp x of
    Failure _ -> Left . Msg $ "parse failure"
    Success r -> Right r

convSExp :: SExpable a => String -> a -> Integer -> String
convSExp pre s id =
  let sex = SexpList [SymbolAtom pre, toSExp s, IntegerAtom id] in
      let str = sExpToString sex in
          (getHexLength str) ++ str

getHexLength :: String -> String
getHexLength s = printf "%06x" (1 + (length s))

-- | The version of the IDE mode command set. Increment this when you
-- change it so clients can adapt.
ideModeEpoch :: Int
ideModeEpoch = 1

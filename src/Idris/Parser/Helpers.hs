{-|
Module      : Idris.Parser.Helpers
Description : Utilities for Idris' parser.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts, MultiParamTypeClasses #-}
module Idris.Parser.Helpers
  ( module Idris.Parser.Stack
    -- * The parser
  , IdrisParser
  , parseErrorDoc
    -- * Space
  , whiteSpace
  , someSpace
  , eol
  , isEol
    -- * Basic parsers
  , char
  , symbol
  , string
  , lookAheadMatches
    -- * Terminals
  , lchar
  , reserved
  , docComment
  , token
  , natural
  , charLiteral
  , stringLiteral
  , float
    -- * Names
  , bindList
  , maybeWithNS
  , iName
  , name
  , identifier
  , identifierWithExtraChars
  , packageName
    -- * Access
  , accessibility
  , accData
  , addAcc
    -- * Warnings and errors
  , fixErrorMsg
  , parserWarning
  , clearParserWarnings
  , reportParserWarnings
    -- * Highlighting
  , highlight
  , keyword
    -- * Indentation
  , pushIndent
  , popIndent
  , indentGt
  , notOpenBraces
    -- * Indented blocks
  , openBlock
  , closeBlock
  , terminator
  , notEndBlock
  , indentedBlock
  , indentedBlock1
  , indentedBlockS
  , indented
    -- * Miscellaneous
  , notEndApp
  , commaSeparated
  )
where

import Idris.AbsSyntax
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate (pprintErr)
import Idris.Docstrings
import Idris.Options
import Idris.Output (iWarn)
import Idris.Parser.Stack

import Prelude hiding (pi)

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Data.Char
import qualified Data.HashSet as HS
import Data.List
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Text.Megaparsec ((<?>))
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as P hiding (space)
import qualified Text.PrettyPrint.ANSI.Leijen as PP


-- | Idris parser with state used during parsing
type IdrisParser = Parser IState

parseErrorDoc :: ParseError -> PP.Doc
parseErrorDoc = PP.string . prettyError

someSpace :: Parsing m => m ()
someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()

token :: Parsing m => m a -> m a
token p = trackExtent p <* whiteSpace

highlight :: (MonadState IState m, Parsing m) => OutputAnnotation -> m a -> m a
highlight annot p = do
  (result, fc) <- withExtent p
  modify $ \ist -> ist { idris_parserHighlights = S.insert (FC' fc, annot) (idris_parserHighlights ist) }
  return result

-- | Parse a reserved identfier, highlighting it as a keyword
keyword :: (Parsing m, MonadState IState m) => String -> m ()
keyword str = highlight AnnKeyword (reserved str)

clearParserWarnings :: Idris ()
clearParserWarnings = do ist <- getIState
                         putIState ist { parserWarnings = [] }

reportParserWarnings :: Idris ()
reportParserWarnings = do ist <- getIState
                          mapM_ (uncurry iWarn)
                                (map (\ (fc, err) -> (fc, pprintErr ist err)) .
                                 reverse .
                                 nubBy (\(fc, err) (fc', err') ->
                                         FC' fc == FC' fc' && err == err') $
                                 parserWarnings ist)
                          clearParserWarnings


parserWarning :: FC -> Maybe Opt -> Err -> IdrisParser ()
parserWarning fc warnOpt warnErr = do
  ist <- get
  let cmdline = opt_cmdline (idris_options ist)
  unless (maybe False (`elem` cmdline) warnOpt) $
    put ist { parserWarnings = (fc, warnErr) : parserWarnings ist }

{- * Space, comments and literals (token/lexing like parsers) -}

-- | Consumes any simple whitespace (any character which satisfies Char.isSpace)
simpleWhiteSpace :: Parsing m => m ()
simpleWhiteSpace = () <$ P.satisfy isSpace

-- | Checks if a charcter is end of line
isEol :: Char -> Bool
isEol '\n' = True
isEol  _   = False

-- | A parser that succeeds at the end of the line
eol :: Parsing m => m ()
eol = () <$ P.satisfy isEol <|> P.lookAhead P.eof <?> "end of line"

{- | Consumes a single-line comment

@
     SingleLineComment_t ::= '--' ~EOL_t* EOL_t ;
@
 -}
singleLineComment :: Parsing m => m ()
singleLineComment = P.hidden (() <$ string "--" *> many (P.satisfy (not . isEol)) *> eol)

{- | Consumes a multi-line comment

@
  MultiLineComment_t ::=
     '{ -- }'
   | '{ -' InCommentChars_t
  ;
@

@
  InCommentChars_t ::=
   '- }'
   | MultiLineComment_t InCommentChars_t
   | ~'- }'+ InCommentChars_t
  ;
@
-}
multiLineComment :: Parsing m => m ()
multiLineComment = P.hidden $ P.try (string "{-" *> string "-}" *> pure ())
                              <|> string "{-" *> inCommentChars
  where inCommentChars :: Parsing m => m ()
        inCommentChars =     string "-}" *> pure ()
                         <|> P.try (multiLineComment) *> inCommentChars
                         <|> string "|||" *> many (P.satisfy (not . isEol)) *> eol *> inCommentChars
                         <|> P.skipSome (P.noneOf startEnd) *> inCommentChars
                         <|> P.oneOf startEnd *> inCommentChars
                         <?> "end of comment"
        startEnd :: String
        startEnd = "{}-"

{-| Parses a documentation comment

@
  DocComment_t ::= DocCommentLine (ArgCommentLine DocCommentLine*)* ;

  DocCommentLine ::= '|||' ~EOL_t* EOL_t ;
  ArgCommentLine ::= '|||' '@' ~EOL_t* EOL_t ;
@
 -}
docComment :: IdrisParser (Docstring (), [(Name, Docstring ())])
docComment = do dc <- pushIndent *> docCommentLine
                rest <- many (indented docCommentLine)
                args <- many $ do (name, first) <- indented argDocCommentLine
                                  rest <- many (indented docCommentLine)
                                  return (name, concat (intersperse "\n" (first:rest)))
                popIndent
                return (parseDocstring $ T.pack (concat (intersperse "\n" (dc:rest))),
                        map (\(n, d) -> (n, parseDocstring (T.pack d))) args)

  where docCommentLine :: Parsing m => m String
        docCommentLine = P.hidden $ P.try $ do
                           string "|||"
                           many (P.satisfy (==' '))
                           contents <- P.option "" (do first <- P.satisfy (\c -> not (isEol c || c == '@'))
                                                       res <- many (P.satisfy (not . isEol))
                                                       return $ first:res)
                           eol ; someSpace
                           return contents

        argDocCommentLine :: IdrisParser (Name, String)
        argDocCommentLine = do P.string "|||"
                               P.many (P.satisfy isSpace)
                               P.char '@'
                               P.many (P.satisfy isSpace)
                               n <- name
                               P.many (P.satisfy isSpace)
                               docs <- P.many (P.satisfy (not . isEol))
                               P.eol ; someSpace
                               return (n, docs)

-- | Parses some white space
whiteSpace :: Parsing m => m ()
whiteSpace = someSpace <|> pure ()

-- | Parses a string literal
stringLiteral :: Parsing m => m String
stringLiteral = token . P.try $ P.char '"' *> P.manyTill P.charLiteral (P.char '"')

-- | Parses a char literal
charLiteral :: Parsing m => m Char
charLiteral = token . P.try $ P.char '\'' *> P.charLiteral <* P.char '\''

-- | Parses a natural number
natural :: Parsing m => m Integer
natural = token (    P.try (P.char '0' *> P.char' 'x' *> P.hexadecimal)
                 <|> P.try (P.char '0' *> P.char' 'o' *> P.octal)
                 <|> P.try P.decimal)

-- | Parses a floating point number
float :: Parsing m => m Double
float = token . P.try $ P.float

{- * Symbols, identifiers, names and operators -}

reservedIdentifiers :: HS.HashSet String
reservedIdentifiers = HS.fromList
  [ "Type"
  , "case", "class", "codata", "constructor", "corecord", "data"
  , "do", "dsl", "else", "export", "if", "implementation", "implicit"
  , "import", "impossible", "in", "infix", "infixl", "infixr", "instance"
  , "interface", "let", "mutual", "namespace", "of", "parameters", "partial"
  , "postulate", "private", "proof", "public", "quoteGoal", "record"
  , "rewrite", "syntax", "then", "total", "using", "where", "with"
  ]

identifierOrReservedWithExtraChars :: Parsing m => String -> m String
identifierOrReservedWithExtraChars extraChars = token $ P.try $ do
  c <- P.satisfy isAlpha <|> P.oneOf "_"
  cs <- P.many (P.satisfy isAlphaNum <|> P.oneOf extraChars)
  return $ c : cs

char :: Parsing m => Char -> m Char
char = P.char

string :: Parsing m => String -> m String
string = P.string

-- | Parses a character as a token
lchar :: Parsing m => Char -> m Char
lchar = token . P.char

symbol :: Parsing m => String -> m ()
symbol = void . token . P.string

-- | Parses a reserved identifier
reserved :: Parsing m => String -> m ()
reserved name = token $ P.try $ do
  P.string name
  P.notFollowedBy (P.satisfy isAlphaNum <|> P.oneOf "_'.") <?> "end of " ++ name

-- | Parses an identifier as a token
identifierWithExtraChars :: Parsing m => String -> m String
identifierWithExtraChars extraChars = P.try $ do
  ident <- identifierOrReservedWithExtraChars extraChars
  when (ident `HS.member` reservedIdentifiers) $ P.unexpected . P.Label . NonEmpty.fromList $ "reserved " ++ ident
  when (ident == "_") $ P.unexpected . P.Label . NonEmpty.fromList $ "wildcard"
  return ident

identifier :: Parsing m => m String
identifier = identifierWithExtraChars "_'."

-- | Parses an identifier with possible namespace as a name
iName :: Parsing m => [String] -> m Name
iName bad = maybeWithNS identifier bad <?> "name"

-- | Parses an string possibly prefixed by a namespace
maybeWithNS :: Parsing m => m String -> [String] -> m Name
maybeWithNS parser bad = do
  i <- P.option "" (P.lookAhead identifier)
  when (i `elem` bad) $ P.unexpected . P.Label . NonEmpty.fromList $ "reserved identifier"
  mkName <$> P.choice (reverse (parserNoNS parser : parsersNS parser i))
  where parserNoNS :: Parsing m => m String -> m (String, String)
        parserNoNS = fmap (\x -> (x, ""))
        parserNS   :: Parsing m => m String -> String -> m (String, String)
        parserNS   parser ns = do xs <- trackExtent (string ns)
                                  lchar '.'
                                  x <- parser
                                  return (x, xs)
        parsersNS  :: Parsing m => m String -> String -> [m (String, String)]
        parsersNS parser i = [P.try (parserNS parser ns) | ns <- (initsEndAt (=='.') i)]

-- | Parses a name
name :: (Parsing m, MonadState IState m) => m Name
name = do
    keywords <- syntax_keywords <$> get
    aliases  <- module_aliases  <$> get
    n <- iName keywords
    return (unalias aliases n)
   <?> "name"
  where
    unalias :: M.Map [T.Text] [T.Text] -> Name -> Name
    unalias aliases (NS n ns) | Just ns' <- M.lookup ns aliases = NS n ns'
    unalias aliases name = name

{- | List of all initial segments in ascending order of a list.  Every
such initial segment ends right before an element satisfying the given
condition.
-}
initsEndAt :: (a -> Bool) -> [a] -> [[a]]
initsEndAt p [] = []
initsEndAt p (x:xs) | p x = [] : x_inits_xs
                    | otherwise = x_inits_xs
  where x_inits_xs = [x : cs | cs <- initsEndAt p xs]


{- | Create a `Name' from a pair of strings representing a base name and its
 namespace.
-}
mkName :: (String, String) -> Name
mkName (n, "") = sUN n
mkName (n, ns) = sNS (sUN n) (reverse (parseNS ns))
  where parseNS x = case span (/= '.') x of
                      (x, "")    -> [x]
                      (x, '.':y) -> x : parseNS y

-- | Parse a package name
packageName :: Parsing m => m String
packageName = (:) <$> P.oneOf firstChars <*> many (P.oneOf remChars)
  where firstChars = ['a'..'z'] ++ ['A'..'Z']
        remChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['-','_']

{- * Position helpers -}

{-* Syntax helpers-}
-- | Bind constraints to term
bindList :: (RigCount -> Name -> FC -> PTerm -> PTerm -> PTerm) -> [(RigCount, Name, FC, PTerm)] -> PTerm -> PTerm
bindList b []                 sc = sc
bindList b ((r, n, fc, t):bs) sc = b r n fc t (bindList b bs sc)

{- | @commaSeparated p@ parses one or more occurences of `p`,
     separated by commas and optional whitespace. -}
commaSeparated :: Parsing m => m a -> m [a]
commaSeparated p = p `P.sepBy1` (P.space >> P.char ',' >> P.space)

{- * Layout helpers -}

-- | Push indentation to stack
pushIndent :: IdrisParser ()
pushIndent = do columnNumber <- indent
                ist <- get
                put (ist { indent_stack = columnNumber : indent_stack ist })

-- | Pops indentation from stack
popIndent :: IdrisParser ()
popIndent = do ist <- get
               case indent_stack ist of
                 [] -> error "The impossible happened! Tried to pop an indentation level where none was pushed (underflow)."
                 (x : xs) -> put (ist { indent_stack = xs })


-- | Gets current indentation
indent :: Parsing m => m Int
indent = P.unPos . P.sourceColumn <$> P.getSourcePos

-- | Gets last indentation
lastIndent :: (MonadState IState m) => m Int
lastIndent = do ist <- get
                case indent_stack ist of
                  (x : xs) -> return x
                  _        -> return 1

-- | Applies parser in an indented position
indented :: IdrisParser a -> IdrisParser a
indented p = notEndBlock *> p <* keepTerminator

-- | Applies parser to get a block (which has possibly indented statements)
indentedBlock :: IdrisParser a -> IdrisParser [a]
indentedBlock p = do openBlock
                     pushIndent
                     res <- many (indented p)
                     popIndent
                     closeBlock
                     return res

-- | Applies parser to get a block with at least one statement (which has possibly indented statements)
indentedBlock1 :: IdrisParser a -> IdrisParser [a]
indentedBlock1 p = do openBlock
                      pushIndent
                      res <- some (indented p)
                      popIndent
                      closeBlock
                      return res

-- | Applies parser to get a block with exactly one (possibly indented) statement
indentedBlockS :: IdrisParser a -> IdrisParser a
indentedBlockS p = do openBlock
                      pushIndent
                      res <- indented p
                      popIndent
                      closeBlock
                      return res


-- | Checks if the following character matches provided parser
lookAheadMatches :: Parsing m => m a -> m Bool
lookAheadMatches p = isJust <$> P.lookAhead (P.optional p)

-- | Parses a start of block
openBlock :: IdrisParser ()
openBlock =     do lchar '{'
                   ist <- get
                   put (ist { brace_stack = Nothing : brace_stack ist })
            <|> do ist <- get
                   lvl' <- indent
                    -- if we're not indented further, it's an empty block, so
                    -- increment lvl to ensure we get to the end
                   let lvl = case brace_stack ist of
                                   Just lvl_old : _ ->
                                       if lvl' <= lvl_old then lvl_old+1
                                                          else lvl'
                                   [] -> if lvl' == 1 then 2 else lvl'
                                   _ -> lvl'
                   put (ist { brace_stack = Just lvl : brace_stack ist })
            <?> "start of block"

-- | Parses an end of block
closeBlock :: IdrisParser ()
closeBlock = do ist <- get
                bs <- case brace_stack ist of
                        []  -> [] <$ P.eof
                        Nothing : xs -> lchar '}' >> return xs <?> "end of block"
                        Just lvl : xs -> (do i   <- indent
                                             isParen <- lookAheadMatches (char ')')
                                             isIn <- lookAheadMatches (reserved "in")
                                             if i >= lvl && not (isParen || isIn)
                                                then fail "not end of block"
                                                else return xs)
                                          <|> (do notOpenBraces
                                                  P.eof
                                                  return [])
                put (ist { brace_stack = bs })

-- | Parses a terminator
terminator :: IdrisParser ()
terminator =     do lchar ';'; popIndent
             <|> do c <- indent; l <- lastIndent
                    if c <= l then popIndent else fail "not a terminator"
             <|> do isParen <- lookAheadMatches (P.oneOf ")}")
                    if isParen then popIndent else fail "not a terminator"
             <|> P.lookAhead P.eof

-- | Parses and keeps a terminator
keepTerminator :: IdrisParser ()
keepTerminator =  () <$ lchar ';'
              <|> do c <- indent; l <- lastIndent
                     unless (c <= l) $ fail "not a terminator"
              <|> do isParen <- lookAheadMatches (P.oneOf ")}|")
                     isIn <- lookAheadMatches (reserved "in")
                     unless (isIn || isParen) $ fail "not a terminator"
              <|> P.lookAhead P.eof

-- | Checks if application expression does not end
notEndApp :: IdrisParser ()
notEndApp = do c <- indent; l <- lastIndent
               when (c <= l) (fail "terminator")

-- | Checks that it is not end of block
notEndBlock :: IdrisParser ()
notEndBlock = do ist <- get
                 case brace_stack ist of
                      Just lvl : xs -> do i <- indent
                                          isParen <- lookAheadMatches (P.char ')')
                                          when (i < lvl || isParen) (fail "end of block")
                      _ -> return ()

indentGt :: (Parsing m, MonadState IState m) => m ()
indentGt = do
  li <- lastIndent
  i <- indent
  when (i <= li) $ fail "Wrong indention: should be greater than context indentation"

-- | Checks that there are no braces that are not closed
notOpenBraces :: IdrisParser ()
notOpenBraces = do ist <- get
                   when (hasNothing $ brace_stack ist) $ fail "end of input"
  where hasNothing :: [Maybe a] -> Bool
        hasNothing = any isNothing

{- | Parses an accessibilty modifier (e.g. public, private) -}
accessibility' :: IdrisParser Accessibility
accessibility' = Public  <$ reserved "public" <* reserved "export"
             <|> Frozen  <$ reserved "export"
             <|> Private <$ reserved "private"
             <?> "accessibility modifier"

accessibility :: IdrisParser Accessibility
accessibility = do acc <- optional accessibility'
                   case acc of
                        Just a -> return a
                        Nothing -> do ist <- get
                                      return (default_access ist)

-- | Adds accessibility option for function
addAcc :: Name -> Accessibility -> IdrisParser ()
addAcc n a = do i <- get
                put (i { hide_list = addDef n a (hide_list i) })

{- | Add accessbility option for data declarations
 (works for interfaces too - 'abstract' means the data/interface is visible but members not) -}
accData :: Accessibility -> Name -> [Name] -> IdrisParser ()
accData Frozen n ns = do addAcc n Public -- so that it can be used in public definitions
                         mapM_ (\n -> addAcc n Private) ns -- so that they are invisible
accData a n ns = do addAcc n a
                    mapM_ (`addAcc` a) ns


{- * Error reporting helpers -}
{- | Error message with possible fixes list -}
fixErrorMsg :: String -> [String] -> String
fixErrorMsg msg fixes = msg ++ ", possible fixes:\n" ++ (concat $ intersperse "\n\nor\n\n" fixes)

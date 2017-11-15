{-|
Module      : Idris.Parser.Helpers
Description : Utilities for Idris' parser.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}
module Idris.Parser.Helpers where

import Idris.AbsSyntax
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate (pprintErr)
import Idris.Docstrings
import Idris.Options
import Idris.Output (iWarn)

import Prelude hiding (pi)

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict (MonadWriter(..), WriterT(..), execWriterT)
import Data.Char
import qualified Data.HashSet as HS
import Data.List
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import Data.Void (Void(..))
import System.FilePath
import Text.Megaparsec ((<?>))
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as P hiding (space)
import qualified Text.PrettyPrint.ANSI.Leijen as PP


-- | Idris parser with state used during parsing
type BaseParser  = P.Parsec Void String     -- Parses text (base of parser stack)
type SpanParser  = WriterT FC BaseParser    -- Computes FC spans of all non-terminals
type IdrisParser = StateT IState SpanParser -- Tracks IState

type Parsing m = (P.MonadParsec Void String m, MonadWriter FC m)

type ParseState = P.State String
data ParseError = ParseError String (P.ParseError (P.Token String) Void)

parseErrorPretty                    :: ParseError -> String
parseErrorPretty (ParseError s err) = P.parseErrorPretty' s err

parseErrorDoc :: ParseError -> PP.Doc
parseErrorDoc = PP.string . parseErrorPretty

parseErrorFC :: ParseError -> FC
parseErrorFC (ParseError _ err) = sourcePositionFC pos
  where
    (pos NonEmpty.:| _) = P.errorPos err

parseErrorMessage :: ParseError -> String
parseErrorMessage (ParseError _ err) = P.parseErrorTextPretty err



someSpace :: Parsing m => m ()
someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()

spanning :: Parsing m => m a -> m a
spanning p = (getFC >>= tell) *> p <* (getFC >>= tell)

tokenFC :: Parsing m => m a -> m a
tokenFC p = spanning p <* whiteSpace

token :: Parsing m => m a -> m a
token p = p <* whiteSpace

-- | Helper to run Idris parser stack
runparser :: StateT st SpanParser res -> st -> String -> String -> Either ParseError res
runparser p i inputname s =
  case P.parse (runWriterT (evalStateT p i)) inputname s of
    Left err -> Left $ ParseError s err
    Right v  -> Right $ fst v


highlightP :: FC -> OutputAnnotation -> IdrisParser ()
highlightP fc annot = do ist <- get
                         put ist { idris_parserHighlights = (fc, annot) : idris_parserHighlights ist}

noDocCommentHere :: String -> IdrisParser ()
noDocCommentHere msg =
  optional (do fc <- getFC
               docComment
               ist <- get
               put ist { parserWarnings = (fc, Msg msg) : parserWarnings ist}) *>
  pure ()

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
  DocComment_t ::=   '|||' ~EOL_t* EOL_t
                 ;
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
                               n <- fst <$> name
                               P.many (P.satisfy isSpace)
                               docs <- P.many (P.satisfy (not . isEol))
                               P.eol ; someSpace
                               return (n, docs)

-- | Parses some white space
whiteSpace :: Parsing m => m ()
whiteSpace = someSpace <|> pure ()

-- | Parses a string literal
stringLiteral :: Parsing m => m String
stringLiteral = tokenFC . P.try $ P.char '"' *> P.manyTill P.charLiteral (P.char '"')

-- | Parses a char literal
charLiteral :: Parsing m => m Char
charLiteral = tokenFC . P.try $ P.char '\'' *> P.charLiteral <* P.char '\''

-- | Parses a natural number
natural :: Parsing m => m Integer
natural = tokenFC (    P.try (P.char '0' *> P.char' 'x' *> P.hexadecimal)
                   <|> P.try (P.char '0' *> P.char' 'o' *> P.octal)
                   <|> P.try P.decimal)

-- | Parses a floating point number
float :: Parsing m => m Double
float = tokenFC . P.try $ P.float

{- * Symbols, identifiers, names and operators -}

reservedIdentifiers :: HS.HashSet String
reservedIdentifiers = HS.fromList
  [ "Type"
  , "abstract", "case", "class", "codata", "constructor", "corecord", "data"
  , "do", "dsl", "else", "export", "if", "implementation", "implicit"
  , "import", "impossible", "in", "infix", "infixl", "infixr", "instance"
  , "interface", "let", "mutual", "namespace", "of", "parameters", "partial"
  , "postulate", "private", "proof", "public", "quoteGoal", "record"
  , "rewrite", "syntax", "then", "total", "using", "where", "with"
  ]

identifierOrReserved :: Parsing m => m String
identifierOrReserved = token $ P.try $ do
  c <- P.satisfy isAlpha <|> P.oneOf "_"
  cs <- P.many (P.satisfy isAlphaNum <|> P.oneOf "_'.")
  return $ c : cs

char :: Parsing m => Char -> m Char
char = P.char

string :: Parsing m => String -> m String
string = P.string

-- | Parses a character as a token
lchar :: Parsing m => Char -> m Char
lchar = token . P.char

-- | Parses a character as a token, returning the source span of the character
lcharFC :: Parsing m => Char -> m Char
lcharFC = tokenFC . P.char

symbol :: Parsing m => String -> m ()
symbol = void . P.symbol someSpace

symbolFC :: Parsing m => String -> m ()
symbolFC = spanning . symbol

-- | Parses a reserved identifier
reserved :: Parsing m => String -> m ()
reserved name = token $ P.try $ do
  P.string name
  P.notFollowedBy (P.satisfy isAlphaNum <|> P.oneOf "_'.") <?> "end of " ++ name

-- | Parses a reserved identifier, computing its span. Assumes that
-- reserved identifiers never contain line breaks.
reservedFC :: Parsing m => String -> m ()
reservedFC = spanning . reserved

-- | Parse a reserved identfier, highlighting its span as a keyword
reservedHL :: String -> IdrisParser ()
reservedHL str = execWriterT (reservedFC str) >>= flip highlightP AnnKeyword

-- Taken from Parsec (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- | Parses a reserved operator
reservedOp :: Parsing m => String -> m ()
reservedOp name = token $ P.try $
  do string name
     P.notFollowedBy operatorLetter <?> ("end of " ++ show name)

reservedOpFC :: Parsing m => String -> m ()
reservedOpFC = spanning . reservedOp

-- | Parses an identifier as a token
identifierFC :: Parsing m => m String
identifierFC = P.try $ do
  ident <- spanning identifierOrReserved
  when (ident `HS.member` reservedIdentifiers) $ P.unexpected . P.Label . NonEmpty.fromList $ "reserved " ++ ident
  when (ident == "_") $ P.unexpected . P.Label . NonEmpty.fromList $ "wildcard"
  return ident

-- | Parses an identifier with possible namespace as a name
iName :: Parsing m => [String] -> m (Name, FC)
iName bad = listen (maybeWithNS identifierFC bad) <?> "name"

-- | Parses an string possibly prefixed by a namespace
maybeWithNS :: Parsing m => m String -> [String] -> m Name
maybeWithNS parser bad = do
  i <- P.option "" (P.lookAhead identifierFC)
  when (i `elem` bad) $ P.unexpected . P.Label . NonEmpty.fromList $ "reserved identifier"
  mkName <$> P.choice (reverse (parserNoNS parser : parsersNS parser i))
  where parserNoNS :: Parsing m => m String -> m (String, String)
        parserNoNS = fmap (\x -> (x, ""))
        parserNS   :: Parsing m => m String -> String -> m (String, String)
        parserNS   parser ns = do xs <- string ns
                                  lchar '.'
                                  x <- parser
                                  return (x, xs)
        parsersNS  :: Parsing m => m String -> String -> [m (String, String)]
        parsersNS parser i = [P.try (parserNS parser ns) | ns <- (initsEndAt (=='.') i)]

-- | Parses a name
name :: IdrisParser (Name, FC)
name = (<?> "name") $ do
    keywords <- syntax_keywords <$> get
    aliases  <- module_aliases  <$> get
    (n, fc) <- iName keywords
    return (unalias aliases n, fc)
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

opChars :: String
opChars = ":!#$%&*+./<=>?@\\^|-~"

operatorLetter :: Parsing m => m Char
operatorLetter = P.oneOf opChars

-- | Parse a package name
packageName :: Parsing m => m String
packageName = (:) <$> P.oneOf firstChars <*> many (P.oneOf remChars)
  where firstChars = ['a'..'z'] ++ ['A'..'Z']
        remChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['-','_']

commentMarkers :: [String]
commentMarkers = [ "--", "|||" ]

invalidOperators :: [String]
invalidOperators = [":", "=>", "->", "<-", "=", "?=", "|", "**", "==>", "\\", "%", "~", "?", "!", "@"]

-- | Parses an operator
symbolicOperator :: Parsing m => m String
symbolicOperator = do op <- token . some $ operatorLetter
                      when (op `elem` (invalidOperators ++ commentMarkers)) $
                           fail $ op ++ " is not a valid operator"
                      return op

-- | Parses an operator
symbolicOperatorFC :: Parsing m => m String
symbolicOperatorFC = spanning symbolicOperator

{- * Position helpers -}

sourcePositionFC :: P.SourcePos -> FC
sourcePositionFC (P.SourcePos name line column) =
  -- TODO: Change to actual spanning
  -- Issue #1594 on the Issue Tracker.
  -- https://github.com/idris-lang/Idris-dev/issues/1594
  FC f (lineNumber, columnNumber) (lineNumber, columnNumber)
  where
    lineNumber = P.unPos line
    columnNumber = P.unPos column
    (dir, file) = splitFileName name
    f = if dir == addTrailingPathSeparator "."
        then file
        else name

{- | Get file position as FC -}
getFC :: Parsing m => m FC
getFC = sourcePositionFC <$> P.getPosition

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
indent = P.unPos . P.sourceColumn <$> P.getPosition

-- | Gets last indentation
lastIndent :: IdrisParser Int
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

indentGt :: IdrisParser ()
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
accessibility'
              = do fc <- execWriterT $ reservedFC "public"
                   gotexp <- optional (reserved "export")
                   case gotexp of
                        Just _ -> return ()
                        Nothing -> do
                           ist <- get
                           put ist { parserWarnings =
                              (fc, Msg "'public' is deprecated. Use 'public export' instead.")
                                   : parserWarnings ist }
                   return Public
            <|> do fc <- execWriterT $ reservedFC "abstract"
                   ist <- get
                   put ist { parserWarnings =
                      (fc, Msg "The 'abstract' keyword is deprecated. Use 'export' instead.")
                           : parserWarnings ist }
                   return Frozen
            <|> do reserved "export"; return Frozen
            <|> do reserved "private";  return Private
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

-- | Collect 'PClauses' with the same function name
collect :: [PDecl] -> [PDecl]
collect (c@(PClauses _ o _ _) : ds)
    = clauses (cname c) [] (c : ds)
  where clauses :: Maybe Name -> [PClause] -> [PDecl] -> [PDecl]
        clauses j@(Just n) acc (PClauses fc _ _ [PClause fc' n' l ws r w] : ds)
           | n == n' = clauses j (PClause fc' n' l ws r (collect w) : acc) ds
        clauses j@(Just n) acc (PClauses fc _ _ [PWith fc' n' l ws r pn w] : ds)
           | n == n' = clauses j (PWith fc' n' l ws r pn (collect w) : acc) ds
        clauses (Just n) acc xs = PClauses (fcOf c) o n (reverse acc) : collect xs
        clauses Nothing acc (x:xs) = collect xs
        clauses Nothing acc [] = []

        cname :: PDecl -> Maybe Name
        cname (PClauses fc _ _ [PClause _ n _ _ _ _]) = Just n
        cname (PClauses fc _ _ [PWith   _ n _ _ _ _ _]) = Just n
        cname (PClauses fc _ _ [PClauseR _ _ _ _]) = Nothing
        cname (PClauses fc _ _ [PWithR _ _ _ _ _]) = Nothing
        fcOf :: PDecl -> FC
        fcOf (PClauses fc _ _ _) = fc
collect (PParams f ns ps : ds) = PParams f ns (collect ps) : collect ds
collect (POpenInterfaces f ns ps : ds) = POpenInterfaces f ns (collect ps) : collect ds
collect (PMutual f ms : ds) = PMutual f (collect ms) : collect ds
collect (PNamespace ns fc ps : ds) = PNamespace ns fc (collect ps) : collect ds
collect (PInterface doc f s cs n nfc ps pdocs fds ds cn cd : ds')
    = PInterface doc f s cs n nfc ps pdocs fds (collect ds) cn cd : collect ds'
collect (PImplementation doc argDocs f s cs pnames acc opts n nfc ps pextra t en ds : ds')
    = PImplementation doc argDocs f s cs pnames acc opts n nfc ps pextra t en (collect ds) : collect ds'
collect (d : ds) = d : collect ds
collect [] = []

{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards #-}
module Idris.ParseHelpers where

import Prelude hiding (pi)

import Text.Trifecta.Delta
import Text.Trifecta hiding (span, stringLiteral, charLiteral, natural, symbol, char, string, whiteSpace)
import Text.Parser.LookAhead
import Text.Parser.Expression
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Char as Chr
import qualified Text.Parser.Token.Highlight as Hi

import Idris.AbsSyntax

import Idris.Core.TT
import Idris.Core.Evaluate

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict

import Data.Maybe
import qualified Data.List.Split as Spl
import Data.List
import Data.Monoid
import Data.Char
import qualified Data.HashSet as HS
import qualified Data.Text as T
import qualified Data.ByteString.UTF8 as UTF8

import System.FilePath

-- | Idris parser with state used during parsing
type IdrisParser = StateT IState IdrisInnerParser

newtype IdrisInnerParser a = IdrisInnerParser { runInnerParser :: Parser a }
  deriving (Monad, Functor, MonadPlus, Applicative, Alternative, CharParsing, LookAheadParsing, Parsing, DeltaParsing, MarkParsing Delta, Monoid)

instance TokenParsing IdrisInnerParser where
  someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()

-- | Generalized monadic parsing constraint type
type MonadicParsing m = (DeltaParsing m, LookAheadParsing m, TokenParsing m, Monad m)

-- | Helper to run Idris inner parser based stateT parsers
runparser :: StateT st IdrisInnerParser res -> st -> String -> String -> Result res
runparser p i inputname = parseString (runInnerParser (evalStateT p i)) (Directed (UTF8.fromString inputname) 0 0 0 0)

{- * Space, comments and literals (token/lexing like parsers) -}

-- | Consumes any simple whitespace (any character which satisfies Char.isSpace)
simpleWhiteSpace :: MonadicParsing m => m ()
simpleWhiteSpace = satisfy isSpace *> pure ()

-- | Checks if a charcter is end of line
isEol :: Char -> Bool
isEol '\n' = True
isEol  _   = False

eol :: MonadicParsing m => m ()
eol = (satisfy isEol *> pure ()) <|> lookAhead eof <?> "end of line"

-- | Checks if a character is a documentation comment marker
isDocCommentMarker :: Char -> Bool
isDocCommentMarker '|' = True
isDocCommentMarker '^' = True
isDocCommentMarker   _  = False

{- | Consumes a single-line comment

@
     SingleLineComment_t ::= '--' EOL_t
                        |     '--' ~DocCommentMarker_t ~EOL_t* EOL_t
                        ;
@
 -}
singleLineComment :: MonadicParsing m => m ()
singleLineComment =     try (string "--" *> eol *> pure ())
                    <|> string "--" *> satisfy (not . isDocCommentMarker) *> many (satisfy (not . isEol)) *> eol *> pure ()
                    <?> ""

{- | Consumes a multi-line comment

@
  MultiLineComment_t ::=
     '{ -- }'
   | '{ -' ~DocCommentMarker_t InCommentChars_t
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
multiLineComment :: MonadicParsing m => m ()
multiLineComment =     try (string "{-" *> (string "-}") *> pure ())
                   <|> string "{-" *> satisfy (not . isDocCommentMarker) *> inCommentChars
                   <?> ""
  where inCommentChars :: MonadicParsing m => m ()
        inCommentChars =     string "-}" *> pure ()
                         <|> try (multiLineComment) *> inCommentChars
                         <|> try (docComment '|') *> inCommentChars
                         <|> try (docComment '^') *> inCommentChars
                         <|> skipSome (noneOf startEnd) *> inCommentChars
                         <|> oneOf startEnd *> inCommentChars
                         <?> "end of comment"
        startEnd :: String
        startEnd = "{}-"

{-| Parses a documentation comment (similar to haddoc) given a marker character

@
  DocComment_t ::=   '--' DocCommentMarker_t ~EOL_t* EOL_t
                  | '{ -' DocCommentMarket_t ~'- }'* '- }'
                 ;
@
 -}
docComment :: MonadicParsing m => Char -> m String
docComment marker | isDocCommentMarker marker = do dc <- docComment' marker; return (T.unpack $ T.strip $ T.pack dc)
                       | otherwise            = fail "internal error: tried to parse a documentation comment with invalid marker"
  where docComment' :: MonadicParsing m => Char -> m String
        docComment' marker  =     string "--" *> char marker *> many (satisfy (not . isEol)) <* eol
                              <|> string "{-" *> char marker *> (manyTill anyChar (try (string "-}")) <?> "end of comment")
                              <?> ""

-- | Parses some white space
whiteSpace :: MonadicParsing m => m ()
whiteSpace = Tok.whiteSpace

-- | Parses a string literal
stringLiteral :: MonadicParsing m => m String
stringLiteral = Tok.stringLiteral

-- | Parses a char literal
charLiteral :: MonadicParsing m => m Char
charLiteral = Tok.charLiteral

-- | Parses a natural number
natural :: MonadicParsing m => m Integer
natural = Tok.natural

-- | Parses an integral number
integer :: MonadicParsing m => m Integer
integer = Tok.integer

-- | Parses a floating point number
float :: MonadicParsing m => m Double
float = Tok.double

{- * Symbols, identifiers, names and operators -}


-- | Idris Style for parsing identifiers/reserved keywords
idrisStyle :: MonadicParsing m => IdentifierStyle m
idrisStyle = IdentifierStyle _styleName _styleStart _styleLetter _styleReserved Hi.Identifier Hi.ReservedIdentifier
  where _styleName = "Idris"
        _styleStart = satisfy isAlpha
        _styleLetter = satisfy isAlphaNum <|> oneOf "_'" <|> (lchar '.')
        _styleReserved = HS.fromList ["let", "in", "data", "codata", "record", "Type",
                                      "do", "dsl", "import", "impossible",
                                      "case", "of", "total", "partial", "mutual",
                                      "infix", "infixl", "infixr", "rewrite",
                                      "where", "with", "syntax", "proof", "postulate",
                                      "using", "namespace", "class", "instance", "parameters",
                                      "public", "private", "abstract", "implicit",
                                      "quoteGoal"]

char :: MonadicParsing m => Char -> m Char
char = Chr.char

string :: MonadicParsing m => String -> m String
string = Chr.string

-- | Parses a character as a token
lchar :: MonadicParsing m => Char -> m Char
lchar = token . char

-- | Parses string as a token
symbol :: MonadicParsing m => String -> m String
symbol = Tok.symbol

-- | Parses a reserved identifier
reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve idrisStyle

-- Taken from Parsec (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- | Parses a reserved operator
reservedOp :: MonadicParsing m => String -> m ()
reservedOp name = token $ try $
  do string name
     notFollowedBy (operatorLetter) <?> ("end of " ++ show name)

-- | Parses an identifier as a token
identifier :: MonadicParsing m => m String
identifier = token $ Tok.ident idrisStyle

-- | Parses an identifier with possible namespace as a name
iName :: MonadicParsing m => [String] -> m Name
iName bad = maybeWithNS identifier False bad <?> "name"

-- | Parses an string possibly prefixed by a namespace
maybeWithNS :: MonadicParsing m => m String -> Bool -> [String] -> m Name
maybeWithNS parser ascend bad = do
  i <- option "" (lookAhead identifier)
  when (i `elem` bad) $ unexpected "reserved identifier"
  let transf = if ascend then id else reverse
  (x, xs) <- choice (transf (parserNoNS parser : parsersNS parser i))
  return $ mkName (x, xs)
  where parserNoNS :: MonadicParsing m => m String -> m (String, String)
        parserNoNS parser = do x <- parser; return (x, "")
        parserNS   :: MonadicParsing m => m String -> String -> m (String, String)
        parserNS   parser ns = do xs <- string ns; lchar '.';  x <- parser; return (x, xs)
        parsersNS  :: MonadicParsing m => m String -> String -> [m (String, String)]
        parsersNS parser i = [try (parserNS parser ns) | ns <- (initsEndAt (=='.') i)]

-- | Parses a name
name :: IdrisParser Name
name = do i <- get
          iName (syntax_keywords i)
       <?> "name"


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

operatorLetter :: MonadicParsing m => m Char
operatorLetter = oneOf opChars

-- | Parses an operator
operator :: MonadicParsing m => m String
operator = do op <- token . some $ operatorLetter
              when (op == ":") $ fail "(:) is not a valid operator"
              return op

{- * Position helpers -}
{- | Get filename from position (returns "(interactive)" when no source file is given)  -}
fileName :: Delta -> String
fileName (Directed fn _ _ _ _) = UTF8.toString fn
fileName _                     = "(interactive)"

{- | Get line number from position -}
lineNum :: Delta -> Int
lineNum (Lines l _ _ _)      = fromIntegral l + 1
lineNum (Directed _ l _ _ _) = fromIntegral l + 1
lineNum _ = 0

{- | Get column number from position -}
columnNum :: Delta -> Int
columnNum pos = fromIntegral (column pos) + 1


{- | Get file position as FC -}
getFC :: MonadicParsing m => m FC
getFC = do s <- position
           let (dir, file) = splitFileName (fileName s)
           let f = if dir == addTrailingPathSeparator "." then file else fileName s
           return $ FC f (lineNum s) (columnNum s)

{-* Syntax helpers-}
-- | Bind constraints to term
bindList :: (Name -> PTerm -> PTerm -> PTerm) -> [(Name, PTerm)] -> PTerm -> PTerm
bindList b []          sc = sc
bindList b ((n, t):bs) sc = b n t (bindList b bs sc)

{- * Layout helpers -}

-- | Push indentation to stack
pushIndent :: IdrisParser ()
pushIndent = do pos <- position
                ist <- get
                put (ist { indent_stack = (fromIntegral (column pos) + 1) : indent_stack ist })

-- | Pops indentation from stack
popIndent :: IdrisParser ()
popIndent = do ist <- get
               let (x : xs) = indent_stack ist
               put (ist { indent_stack = xs })


-- | Gets current indentation
indent :: IdrisParser Int
indent = liftM ((+1) . fromIntegral . column) position

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
lookAheadMatches :: MonadicParsing m => m a -> m Bool
lookAheadMatches p = do match <- lookAhead (optional p)
                        return $ isJust match

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
                        []  -> eof >> return []
                        Nothing : xs -> lchar '}' >> return xs <?> "end of block"
                        Just lvl : xs -> (do i   <- indent
                                             isParen <- lookAheadMatches (char ')')
                                             if i >= lvl && not isParen
                                                then fail "not end of block"
                                                else return xs)
                                          <|> (do notOpenBraces
                                                  eof
                                                  return [])
                put (ist { brace_stack = bs })

-- | Parses a terminator
terminator :: IdrisParser ()
terminator =     do lchar ';'; popIndent
             <|> do c <- indent; l <- lastIndent
                    if c <= l then popIndent else fail "not a terminator"
             <|> do isParen <- lookAheadMatches (oneOf ")}")
                    if isParen then popIndent else fail "not a terminator"
             <|> lookAhead eof

-- | Parses and keeps a terminator
keepTerminator :: IdrisParser ()
keepTerminator =  do lchar ';'; return ()
              <|> do c <- indent; l <- lastIndent
                     unless (c <= l) $ fail "not a terminator"
              <|> do isParen <- lookAheadMatches (oneOf ")}|")
                     unless isParen $ fail "not a terminator"
              <|> lookAhead eof

-- | Checks if application expression does not end
notEndApp :: IdrisParser ()
notEndApp = do c <- indent; l <- lastIndent
               when (c <= l) (fail "terminator")

-- | Checks that it is not end of block
notEndBlock :: IdrisParser ()
notEndBlock = do ist <- get
                 case brace_stack ist of
                      Just lvl : xs -> do i <- indent
                                          isParen <- lookAheadMatches (char ')')
                                          when (i < lvl || isParen) (fail "end of block")
                      _ -> return ()

-- | Representation of an operation that can compare the current indentation with the last indentation, and an error message if it fails
data IndentProperty = IndentProperty (Int -> Int -> Bool) String

-- | Allows comparison of indent, and fails if property doesn't hold
indentPropHolds :: IndentProperty -> IdrisParser()
indentPropHolds (IndentProperty op msg) = do
  li <- lastIndent
  i <- indent
  when (not $ op i li) $ fail ("Wrong indention: " ++ msg)

-- | Greater-than indent property
gtProp :: IndentProperty
gtProp = IndentProperty (>) "should be greater than context indentation"

-- | Greater-than or equal to indent property
gteProp :: IndentProperty
gteProp = IndentProperty (>=) "should be greater than or equal context indentation"

-- | Equal indent property
eqProp :: IndentProperty
eqProp = IndentProperty (==) "should be equal to context indentation"

-- | Less-than indent property
ltProp :: IndentProperty
ltProp = IndentProperty (<) "should be less than context indentation"

-- | Less-than or equal to indent property
lteProp :: IndentProperty
lteProp = IndentProperty (<=) "should be less than or equal to context indentation"


-- | Checks that there are no braces that are not closed
notOpenBraces :: IdrisParser ()
notOpenBraces = do ist <- get
                   when (hasNothing $ brace_stack ist) $ fail "end of input"
  where hasNothing :: [Maybe a] -> Bool
        hasNothing = any isNothing

{- | Parses an accessibilty modifier (e.g. public, private) -}
accessibility :: IdrisParser Accessibility
accessibility = do reserved "public";   return Public
            <|> do reserved "abstract"; return Frozen
            <|> do reserved "private";  return Hidden
            <?> "accessibility modifier"

-- | Adds accessibility option for function
addAcc :: Name -> Maybe Accessibility -> IdrisParser ()
addAcc n a = do i <- get
                put (i { hide_list = (n, a) : hide_list i })

{- | Add accessbility option for data declarations
 (works for classes too - 'abstract' means the data/class is visible but members not) -}
accData :: Maybe Accessibility -> Name -> [Name] -> IdrisParser ()
accData (Just Frozen) n ns = do addAcc n (Just Frozen)
                                mapM_ (\n -> addAcc n (Just Hidden)) ns
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
        clauses j@(Just n) acc (PClauses fc _ _ [PWith fc' n' l ws r w] : ds)
           | n == n' = clauses j (PWith fc' n' l ws r (collect w) : acc) ds
        clauses (Just n) acc xs = PClauses (fcOf c) o n (reverse acc) : collect xs
        clauses Nothing acc (x:xs) = collect xs
        clauses Nothing acc [] = []

        cname :: PDecl -> Maybe Name
        cname (PClauses fc _ _ [PClause _ n _ _ _ _]) = Just n
        cname (PClauses fc _ _ [PWith   _ n _ _ _ _]) = Just n
        cname (PClauses fc _ _ [PClauseR _ _ _ _]) = Nothing
        cname (PClauses fc _ _ [PWithR _ _ _ _]) = Nothing
        fcOf :: PDecl -> FC
        fcOf (PClauses fc _ _ _) = fc
collect (PParams f ns ps : ds) = PParams f ns (collect ps) : collect ds
collect (PMutual f ms : ds) = PMutual f (collect ms) : collect ds
collect (PNamespace ns ps : ds) = PNamespace ns (collect ps) : collect ds
collect (PClass doc f s cs n ps ds : ds')
    = PClass doc f s cs n ps (collect ds) : collect ds'
collect (PInstance f s cs n ps t en ds : ds')
    = PInstance f s cs n ps t en (collect ds) : collect ds'
collect (d : ds) = d : collect ds
collect [] = []


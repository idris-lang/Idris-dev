{-|
Module      : Idris.Parser.Helpers
Description : Utilities for Idris' parser.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP, ConstraintKinds, GeneralizedNewtypeDeriving, PatternGuards,
             StandaloneDeriving #-}
#if !(MIN_VERSION_base(4,8,0))
{-# LANGUAGE OverlappingInstances #-}
#endif
module Idris.Parser.Helpers where

import Idris.AbsSyntax
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate (pprintErr)
import Idris.Docstrings
import Idris.Output (iWarn)

import qualified Util.Pretty as Pretty (text)

import Prelude hiding (pi)

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import qualified Data.ByteString.UTF8 as UTF8
import Data.Char
import qualified Data.HashSet as HS
import Data.List
import qualified Data.List.Split as Spl
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import Debug.Trace
import System.FilePath
import qualified Text.Parser.Char as Chr
import Text.Parser.Expression
import Text.Parser.LookAhead
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Token.Highlight as Hi
import Text.Trifecta hiding (Err, char, charLiteral, natural, span, string,
                      stringLiteral, symbol, whiteSpace)
import Text.Trifecta.Delta

-- | Idris parser with state used during parsing
type IdrisParser = StateT IState IdrisInnerParser

newtype IdrisInnerParser a = IdrisInnerParser { runInnerParser :: Parser a }
  deriving (Monad, Functor, MonadPlus, Applicative, Alternative, CharParsing, LookAheadParsing, DeltaParsing, MarkParsing Delta, Monoid, TokenParsing)

deriving instance Parsing IdrisInnerParser

#if MIN_VERSION_base(4,9,0)
instance {-# OVERLAPPING #-} DeltaParsing IdrisParser where
  line = lift line
  {-# INLINE line #-}
  position = lift position
  {-# INLINE position #-}
  slicedWith f (StateT m) = StateT $ \s -> slicedWith (\(a,s') b -> (f a b, s')) $ m s
  {-# INLINE slicedWith #-}
  rend = lift rend
  {-# INLINE rend #-}
  restOfLine = lift restOfLine
  {-# INLINE restOfLine #-}

#endif

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPING #-} TokenParsing IdrisParser where
#else
instance TokenParsing IdrisParser where
#endif
  someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()
  token p = do s <- get
               (FC fn (sl, sc) _) <- getFC --TODO: Update after fixing getFC
                                           -- See Issue #1594
               r <- p
               (FC fn _ (el, ec)) <- getFC
               whiteSpace
               put (s { lastTokenSpan = Just (FC fn (sl, sc) (el, ec)) })
               return r
-- | Generalized monadic parsing constraint type
type MonadicParsing m = (DeltaParsing m, LookAheadParsing m, TokenParsing m, Monad m)

class HasLastTokenSpan m where
  getLastTokenSpan :: m (Maybe FC)

instance HasLastTokenSpan IdrisParser where
  getLastTokenSpan = lastTokenSpan <$> get

-- | Helper to run Idris inner parser based stateT parsers
runparser :: StateT st IdrisInnerParser res -> st -> String -> String -> Result res
runparser p i inputname =
  parseString (runInnerParser (evalStateT p i))
              (Directed (UTF8.fromString inputname) 0 0 0 0)

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
simpleWhiteSpace :: MonadicParsing m => m ()
simpleWhiteSpace = satisfy isSpace *> pure ()

-- | Checks if a charcter is end of line
isEol :: Char -> Bool
isEol '\n' = True
isEol  _   = False

-- | A parser that succeeds at the end of the line
eol :: MonadicParsing m => m ()
eol = (satisfy isEol *> pure ()) <|> lookAhead eof <?> "end of line"

{- | Consumes a single-line comment

@
     SingleLineComment_t ::= '--' ~EOL_t* EOL_t ;
@
 -}
singleLineComment :: MonadicParsing m => m ()
singleLineComment = (string "--" *>
                     many (satisfy (not . isEol)) *>
                     eol *> pure ())
                    <?> ""

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
multiLineComment :: MonadicParsing m => m ()
multiLineComment =     try (string "{-" *> (string "-}") *> pure ())
                   <|> string "{-" *> inCommentChars
                   <?> ""
  where inCommentChars :: MonadicParsing m => m ()
        inCommentChars =     string "-}" *> pure ()
                         <|> try (multiLineComment) *> inCommentChars
                         <|> string "|||" *> many (satisfy (not . isEol)) *> eol *> inCommentChars
                         <|> skipSome (noneOf startEnd) *> inCommentChars
                         <|> oneOf startEnd *> inCommentChars
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

  where docCommentLine :: MonadicParsing m => m String
        docCommentLine = try (do string "|||"
                                 many (satisfy (==' '))
                                 contents <- option "" (do first <- satisfy (\c -> not (isEol c || c == '@'))
                                                           res <- many (satisfy (not . isEol))
                                                           return $ first:res)
                                 eol ; someSpace
                                 return contents)-- ++ concat rest))
                        <?> ""

        argDocCommentLine = do string "|||"
                               many (satisfy isSpace)
                               char '@'
                               many (satisfy isSpace)
                               n <- fst <$> name
                               many (satisfy isSpace)
                               docs <- many (satisfy (not . isEol))
                               eol ; someSpace
                               return (n, docs)

-- | Parses some white space
whiteSpace :: MonadicParsing m => m ()
whiteSpace = Tok.whiteSpace

-- | Parses a string literal
stringLiteral :: (MonadicParsing m, HasLastTokenSpan m) => m (String, FC)
stringLiteral = do str <- Tok.stringLiteral
                   fc <- getLastTokenSpan
                   return (str, fromMaybe NoFC fc)

-- | Parses a char literal
charLiteral :: (MonadicParsing m, HasLastTokenSpan m) => m (Char, FC)
charLiteral = do ch <- Tok.charLiteral
                 fc <- getLastTokenSpan
                 return (ch, fromMaybe NoFC fc)

-- | Parses a natural number
natural :: (MonadicParsing m, HasLastTokenSpan m) => m (Integer, FC)
natural = do n <- Tok.natural
             fc <- getLastTokenSpan
             return (n, fromMaybe NoFC fc)

-- | Parses an integral number
integer :: MonadicParsing m => m Integer
integer = Tok.integer

-- | Parses a floating point number
float :: (MonadicParsing m, HasLastTokenSpan m) => m (Double, FC)
float = do f <- Tok.double
           fc <- getLastTokenSpan
           return (f, fromMaybe NoFC fc)

{- * Symbols, identifiers, names and operators -}


-- | Idris Style for parsing identifiers/reserved keywords
idrisStyle :: MonadicParsing m => IdentifierStyle m
idrisStyle = IdentifierStyle {
    _styleName = "Idris"
  , _styleStart = satisfy isAlpha <|> oneOf "_"
  , _styleLetter = satisfy isAlphaNum <|> oneOf "_'."
  , _styleReserved = HS.fromList
      ["let", "in", "data", "codata", "record", "corecord", "Type", "do", "dsl",
      "import", "impossible", "case", "of", "total", "partial", "mutual",
      "infix", "infixl", "infixr", "rewrite", "where", "with", "syntax",
      "proof", "postulate", "using", "namespace", "class", "instance",
      "interface", "implementation", "parameters", "public", "private",
      "export", "abstract", "implicit", "quoteGoal", "constructor", "if",
      "then", "else"]
  , _styleHighlight = Hi.Identifier
  , _styleReservedHighlight = Hi.ReservedIdentifier }

char :: MonadicParsing m => Char -> m Char
char = Chr.char

string :: MonadicParsing m => String -> m String
string = Chr.string

-- | Parses a character as a token
lchar :: MonadicParsing m => Char -> m Char
lchar = token . char

-- | Parses a character as a token, returning the source span of the character
lcharFC :: MonadicParsing m => Char -> m FC
lcharFC ch = do (FC file (l, c) _) <- getFC
                _ <- token (char ch)
                return $ FC file (l, c) (l, c+1)

-- | Parses string as a token
symbol :: MonadicParsing m => String -> m String
symbol = Tok.symbol

symbolFC :: MonadicParsing m => String -> m FC
symbolFC str = do (FC file (l, c) _) <- getFC
                  Tok.symbol str
                  return $ FC file (l, c) (l, c + length str)

-- | Parses a reserved identifier
reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve idrisStyle

-- | Parses a reserved identifier, computing its span. Assumes that
-- reserved identifiers never contain line breaks.
reservedFC :: MonadicParsing m => String -> m FC
reservedFC str = do (FC file (l, c) _) <- getFC
                    reserved str
                    return $ FC file (l, c) (l, c + length str)

-- | Parse a reserved identfier, highlighting its span as a keyword
reservedHL :: String -> IdrisParser ()
reservedHL str = reservedFC str >>= flip highlightP AnnKeyword

-- Taken from Parsec (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- | Parses a reserved operator
reservedOp :: MonadicParsing m => String -> m ()
reservedOp name = token $ try $
  do string name
     notFollowedBy (operatorLetter) <?> ("end of " ++ show name)

reservedOpFC :: MonadicParsing m => String -> m FC
reservedOpFC name = do (FC f (l, c) _) <- getFC
                       reservedOp name
                       return (FC f (l, c) (l, c + length name))

-- | Parses an identifier as a token
identifier :: (MonadicParsing m) => m (String, FC)
identifier = try(do (i, fc) <-
                      token $ do (FC f (l, c) _) <- getFC
                                 i <- Tok.ident idrisStyle
                                 return (i, FC f (l, c) (l, c + length i))
                    when (i == "_") $ unexpected "wildcard"
                    return (i, fc))

-- | Parses an identifier with possible namespace as a name
iName :: (MonadicParsing m, HasLastTokenSpan m) => [String] -> m (Name, FC)
iName bad = do (n, fc) <- maybeWithNS identifier False bad
               return (n, fc)
            <?> "name"

-- | Parses an string possibly prefixed by a namespace
maybeWithNS :: (MonadicParsing m, HasLastTokenSpan m) => m (String, FC) -> Bool -> [String] -> m (Name, FC)
maybeWithNS parser ascend bad = do
  fc <- getFC
  i <- option "" (lookAhead (fst <$> identifier))
  when (i `elem` bad) $ unexpected "reserved identifier"
  let transf = if ascend then id else reverse
  (x, xs, fc) <- choice (transf (parserNoNS parser : parsersNS parser i))
  return (mkName (x, xs), fc)
  where parserNoNS :: MonadicParsing m => m (String, FC) -> m (String, String, FC)
        parserNoNS parser = do startFC <- getFC
                               (x, nameFC) <- parser
                               return (x, "", spanFC startFC nameFC)
        parserNS   :: MonadicParsing m => m (String, FC) -> String -> m (String, String, FC)
        parserNS   parser ns = do startFC <- getFC
                                  xs <- string ns
                                  lchar '.';  (x, nameFC) <- parser
                                  return (x, xs, spanFC startFC nameFC)
        parsersNS  :: MonadicParsing m => m (String, FC) -> String -> [m (String, String, FC)]
        parsersNS parser i = [try (parserNS parser ns) | ns <- (initsEndAt (=='.') i)]

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

operatorLetter :: MonadicParsing m => m Char
operatorLetter = oneOf opChars


commentMarkers :: [String]
commentMarkers = [ "--", "|||" ]

invalidOperators :: [String]
invalidOperators = [":", "=>", "->", "<-", "=", "?=", "|", "**", "==>", "\\", "%", "~", "?", "!", "@"]

-- | Parses an operator
operator :: MonadicParsing m => m String
operator = do op <- token . some $ operatorLetter
              when (op `elem` (invalidOperators ++ commentMarkers)) $
                   fail $ op ++ " is not a valid operator"
              return op

-- | Parses an operator
operatorFC :: MonadicParsing m => m (String, FC)
operatorFC = do (FC f (l, c) _) <- getFC
                op <- operator
                return (op, FC f (l, c) (l, c + length op))

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
           return $ FC f (lineNum s, columnNum s) (lineNum s, columnNum s) -- TODO: Change to actual spanning
           -- Issue #1594 on the Issue Tracker.
           -- https://github.com/idris-lang/Idris-dev/issues/1594


{-* Syntax helpers-}
-- | Bind constraints to term
bindList :: (RigCount -> Name -> FC -> PTerm -> PTerm -> PTerm) -> [(RigCount, Name, FC, PTerm)] -> PTerm -> PTerm
bindList b []                 sc = sc
bindList b ((r, n, fc, t):bs) sc = b r n fc t (bindList b bs sc)

{- | @commaSeparated p@ parses one or more occurences of `p`,
     separated by commas and optional whitespace. -}
commaSeparated :: MonadicParsing m => m a -> m [a]
commaSeparated p = p `sepBy1` (spaces >> char ',' >> spaces)

{- * Layout helpers -}

-- | Push indentation to stack
pushIndent :: IdrisParser ()
pushIndent = do pos <- position
                ist <- get
                put (ist { indent_stack = (fromIntegral (column pos) + 1) : indent_stack ist })

-- | Pops indentation from stack
popIndent :: IdrisParser ()
popIndent = do ist <- get
               case indent_stack ist of
                 [] -> error "The impossible happened! Tried to pop an indentation level where none was pushed (underflow)."
                 (x : xs) -> put (ist { indent_stack = xs })


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
                                             isIn <- lookAheadMatches (reserved "in")
                                             if i >= lvl && not (isParen || isIn)
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
                     isIn <- lookAheadMatches (reserved "in")
                     unless (isIn || isParen) $ fail "not a terminator"
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
indentPropHolds :: IndentProperty -> IdrisParser ()
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
accessibility' :: IdrisParser Accessibility
accessibility'
              = do reserved "public";
                   gotexp <- optional (reserved "export")
                   case gotexp of
                        Just _ -> return ()
                        Nothing -> do
                           ist <- get
                           fc <- getFC
                           put ist { parserWarnings =
                              (fc, Msg "'public' is deprecated. Use 'public export' instead.")
                                   : parserWarnings ist }
                   return Public
            <|> do reserved "abstract";
                   ist <- get
                   fc <- getFC
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

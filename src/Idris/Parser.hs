{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards #-}
module Idris.Parser where

import Prelude hiding (pi)

import Text.Trifecta.Delta
import Text.Trifecta hiding (span, token, whiteSpace, stringLiteral, charLiteral, natural, symbol, char, string)
import Text.Parser.LookAhead
import Text.Parser.Expression
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Char as Chr
import qualified Text.Parser.Token.Highlight as Hi

import Idris.AbsSyntax
import Idris.DSL
import Idris.Imports
import Idris.Error
import Idris.ElabDecls
import Idris.ElabTerm hiding (namespace, params)
import Idris.Coverage
import Idris.IBC
import Idris.Unlit
import Idris.Providers
import Paths_idris

import Util.DynamicLinker

import Core.TT
import Core.Evaluate

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

import Debug.Trace

import System.FilePath
{-
 grammar shortcut notation:
    ~CHARSEQ = complement of char sequence (i.e. any character except CHARSEQ)
    RULE? = optional rule (i.e. RULE or nothing)
    RULE* = repeated rule (i.e. RULE zero or more times)
    RULE+ = repeated rule with at least one match (i.e. RULE one or more times)
    RULE! = invalid rule (i.e. rule that is not valid in context, report meaningful error in case)
    RULE{n} = rule repeated n times
-}


-- | Idris parser with state used during parsing
type IdrisParser = StateT IState Parser

-- | Generalized monadic parsing constraint type
type MonadicParsing m = (DeltaParsing m, LookAheadParsing m, TokenParsing m, Monad m)

{- * Space, comments and literals (token/lexing like parsers) -}
-- | Parses a token by applying parser and then consuming all following whiteSpace
lexeme :: MonadicParsing m => m a -> m a
lexeme p = p <* whiteSpace

-- | Consumes any simple whitespace (any character which satisfies Char.isSpace)
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
     SingleLineComment_t ::= '--' EOL_t
                        |     '--' ~DocCommentMarker_t ~EOL_t* EOL_t
                        ;
 -}
singleLineComment :: MonadicParsing m => m ()
singleLineComment =     try (string "--" *> eol *> pure ())
                    <|> string "--" *> satisfy (not . isDocCommentMarker) *> many (satisfy (not . isEol)) *> eol *> pure ()
                    <?> ""

{- | Consumes a multi-line comment
  MultiLineComment_t ::=
     '{ -- }'
   | '{ -' ~DocCommentMarker_t InCommentChars_t
  ;

  InCommentChars_t ::=
   '- }'
   | MultiLineComment_t InCommentChars_t
   | ~'- }'+ InCommentChars_t
  ;
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
  DocComment_t ::=   '--' DocCommentMarker_t ~EOL_t* EOL_t
                  | '{ -' DocCommentMarket_t ~'- }'* '- }'
                 ;
 -}
docComment :: MonadicParsing m => Char -> m String
docComment marker | isDocCommentMarker marker = do dc <- docComment' marker; return (T.unpack $ T.strip $ T.pack dc)
                       | otherwise            = fail "internal error: tried to parse a documentation comment with invalid marker"
  where docComment' :: MonadicParsing m => Char -> m String
        docComment' marker  =     string "--" *> char marker *> many (satisfy (not . isEol)) <* eol
                              <|> string "{-" *> char marker *> (manyTill anyChar (try (string "-}")) <?> "end of comment")
                              <?> ""

-- | Consumes whitespace (and comments)
whiteSpace :: MonadicParsing m => m ()
whiteSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()

-- | Parses a string literal
stringLiteral :: MonadicParsing m => m String
stringLiteral = lexeme $ Tok.stringLiteral

-- | Parses a char literal
charLiteral :: MonadicParsing m => m Char
charLiteral = lexeme $ Tok.charLiteral

-- | Parses a natural number
natural :: MonadicParsing m => m Integer
natural = lexeme $ Tok.natural

-- | Parses an integral number
integer :: MonadicParsing m => m Integer
integer = lexeme $ Tok.integer

-- | Parses a floating point number
float :: MonadicParsing m => m Double
float = lexeme $ Tok.double

{- * Symbols, identifiers, names and operators -}


-- | Idris Style for parsing identifiers/reserved keywords
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
                                      "using", "namespace", "class", "instance",
                                      "public", "private", "abstract", "implicit",
                                      "quoteGoal",
                                      "Int", "Integer", "Float", "Char", "String", "Ptr",
                                      "Bits8", "Bits16", "Bits32", "Bits64",
                                      "Bits8x16", "Bits16x8", "Bits32x4", "Bits64x2"]

char :: MonadicParsing m => Char -> m Char
char = Chr.char

string :: MonadicParsing m => String -> m String
string = Chr.string

-- | Parses a character as a lexeme
lchar :: MonadicParsing m => Char -> m Char
lchar = lexeme . char

-- | Parses string as a lexeme
symbol :: MonadicParsing m => String -> m String
symbol = lexeme . Tok.symbol

-- | Parses a reserved identifier
reserved :: MonadicParsing m => String -> m ()
reserved = lexeme . Tok.reserve idrisStyle

-- Taken from Parsec (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- | Parses a reserved operator
reservedOp :: MonadicParsing m => String -> m ()
reservedOp name = lexeme $ try $
  do string name
     notFollowedBy (operatorLetter) <?> ("end of " ++ show name)

-- | Parses an identifier as a lexeme
identifier :: MonadicParsing m => m String
identifier = lexeme $ Tok.ident idrisStyle

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


{- | List of all initial segments in ascending order of a list.  Every such
 initial segment ends right before an element satisfying the given
 condition.
-}
initsEndAt :: (a -> Bool) -> [a] -> [[a]]
initsEndAt p [] = []
initsEndAt p (x:xs) | p x = [] : x_inits_xs
                    | otherwise = x_inits_xs
  where x_inits_xs = [x : cs | cs <- initsEndAt p xs]


{- | Create a `Name' from a pair of strings representing a base name and its
 namespace.
-}
mkName :: (String, String) -> Name
mkName (n, "") = UN n
mkName (n, ns) = NS (UN n) (reverse (parseNS ns))
  where parseNS x = case span (/= '.') x of
                      (x, "")    -> [x]
                      (x, '.':y) -> x : parseNS y

operatorLetter :: MonadicParsing m => m Char
operatorLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"

-- | Parses an operator
operator :: MonadicParsing m => m String
operator = do op <- lexeme . some $ operatorLetter
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

{- | Get file position as FC -}
getFC :: MonadicParsing m => m FC
getFC = do s <- position
           let (dir, file) = splitFileName (fileName s)
           let f = if dir == addTrailingPathSeparator "." then file else fileName s
           return $ FC f (lineNum s)

{-* Syntax helpers-}
-- | Bind constraints to term
bindList :: (Name -> PTerm -> PTerm -> PTerm) -> [(Name, PTerm)] -> PTerm -> PTerm
bindList b []          sc = sc
bindList b ((n, t):bs) sc = b n t (bindList b bs sc)

{- |Creates table for fixtiy declarations to build expression parser using
  pre-build and user-defined operator/fixity declarations -}
table :: [FixDecl] -> OperatorTable IdrisParser PTerm
table fixes
   = [[prefix "-" (\fc x -> PApp fc (PRef fc (UN "-"))
        [pexp (PApp fc (PRef fc (UN "fromInteger")) [pexp (PConstant (BI 0))]), pexp x])]]
       ++ toTable (reverse fixes) ++
      [[backtick],
       [binary "="  PEq AssocLeft],
       [binary "->" (\fc x y -> PPi expl (MN 42 "__pi_arg") x y) AssocRight]]

{- |Calculates table for fixtiy declarations -}
toTable :: [FixDecl] -> OperatorTable IdrisParser PTerm
toTable fs = map (map toBin)
                 (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)
   where toBin (Fix (PrefixN _) op) = prefix op
                                       (\fc x -> PApp fc (PRef fc (UN op)) [pexp x])
         toBin (Fix f op)
            = binary op (\fc x y -> PApp fc (PRef fc (UN op)) [pexp x,pexp y]) (assoc f)
         assoc (Infixl _) = AssocLeft
         assoc (Infixr _) = AssocRight
         assoc (InfixN _) = AssocNone

{- |Binary operator -}
binary :: String -> (FC -> PTerm -> PTerm -> PTerm) -> Assoc -> Operator IdrisParser PTerm
binary name f = Infix (do fc <- getFC
                          reservedOp name
                          doc <- option "" (docComment '^')
                          return (f fc))

{- |Prefix operator -}
prefix :: String -> (FC -> PTerm -> PTerm) -> Operator IdrisParser PTerm
prefix name f = Prefix (do reservedOp name
                           fc <- getFC
                           return (f fc))

{- |Backtick operator -}
backtick :: Operator IdrisParser PTerm
backtick = Infix (do lchar '`'; n <- fnName
                     lchar '`'
                     fc <- getFC
                     return (\x y -> PApp fc (PRef fc n) [pexp x, pexp y])) AssocNone

-- | Allow implicit type declarations
allowImp :: SyntaxInfo -> SyntaxInfo
allowImp syn = syn { implicitAllowed = True }

-- | Disallow implicit type declarations
disallowImp :: SyntaxInfo -> SyntaxInfo
disallowImp syn = syn { implicitAllowed = False }

-- | Adds accessibility option for function
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

-- | Applies parser in an indented position
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

-- | Applies parser to get a block with exactly one (possibly indented) statement
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
                    if isParen then popIndent else fail "not a termiantor"
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

notOpenBraces :: IdrisParser ()
notOpenBraces = do ist <- get
                   when (hasNothing $ brace_stack ist) $ fail "end of input"
  where hasNothing :: [Maybe a] -> Bool
        hasNothing = any isNothing

{- * Main grammar -}

{- | Parses module definition
      ModuleHeader ::= 'module' Identifier_t ';'?;
-}
moduleHeader :: IdrisParser [String]
moduleHeader =     try (do reserved "module"
                           i <- identifier
                           option ';' (lchar ';')
                           return (moduleName i))
               <|> return []
  where moduleName x = case span (/='.') x of
                           (x, "")    -> [x]
                           (x, '.':y) -> x : moduleName y

{- | Parses an import statement
  Import ::= 'import' Identifier_t ';'?;
 -}
import_ :: IdrisParser String
import_ = do reserved "import"
             id <- identifier
             option ';' (lchar ';')
             return (toPath id)
          <?> "import statement"
  where toPath f = foldl1' (</>) (Spl.splitOn "." f)

{- | Parses program source
     Prog ::= Decl* EOF;
 -}
prog :: SyntaxInfo -> IdrisParser [PDecl]
prog syn = do whiteSpace
              decls <- many (decl syn)
              notOpenBraces
              eof
              let c = (concat decls)
              return c

{- | Parses a top-level declaration
Decl ::=
    Decl'
  | Using
  | Params
  | Mutual
  | Namespace
  | Class
  | Instance
  | DSL
  | Directive
  | Provider
  | Transform
  | Import!
  ;
-}
decl :: SyntaxInfo -> IdrisParser [PDecl]
decl syn = do notEndBlock
              declBody
  where declBody :: IdrisParser [PDecl]
        declBody =     declBody'
                   <|> using_ syn
                   <|> params syn
                   <|> mutual syn
                   <|> namespace syn
                   <|> class_ syn
                   <|> instance_ syn
                   <|> do d <- dsl syn; return [d]
                   <|> directive syn
                   <|> provider syn
                   <|> transform syn
                   <|> do import_; fail "imports must be at top of file"
                   <?> "declaration"
        declBody' :: IdrisParser [PDecl]
        declBody' = do d <- decl' syn
                       i <- get
                       let d' = fmap (desugar syn i) d
                       return [d']

{- | Parses a top-level declaration with possible syntax sugar
Decl' ::=
    Fixity
  | FunDecl'
  | Data
  | Record
  | SyntaxDecl
  ;
-}
decl' :: SyntaxInfo -> IdrisParser PDecl
decl' syn =    fixity
           <|> syntaxDecl syn
           <|> fnDecl' syn
           <|> data_ syn
           <|> record syn
           <?> "declaration"

{- | Parses a syntax extension declaration (and adds the rule to parser state)
  SyntaxDecl ::= SyntaxRule;
-}
syntaxDecl :: SyntaxInfo -> IdrisParser PDecl
syntaxDecl syn = do s <- syntaxRule syn
                    i <- get
                    let rs = syntax_rules i
                    let ns = syntax_keywords i
                    let ibc = ibc_write i
                    let ks = map show (names s)
                    put (i { syntax_rules = s : rs,
                             syntax_keywords = ks ++ ns,
                             ibc_write = IBCSyntax s : map IBCKeyword ks ++ ibc })
                    fc <- getFC
                    return (PSyntax fc s)
  where names (Rule syms _ _) = mapMaybe ename syms
        ename (Keyword n) = Just n
        ename _           = Nothing

{- | Parses a syntax extension declaration
SyntaxRuleOpts ::= 'term' | 'pattern';

SyntaxRule ::=
  SyntaxRuleOpts? 'syntax' SyntaxSym+ '=' TypeExpr Terminator;

SyntaxSym ::=   '[' Name_t ']'
             |  '{' Name_t '}'
             |  Name_t
             |  StringLiteral_t
             ;
-}
syntaxRule :: SyntaxInfo -> IdrisParser Syntax
syntaxRule syn
    = do sty <- try (do
            pushIndent
            sty <- option AnySyntax (do reserved "term"; return TermSyntax
                                  <|> do reserved "pattern"; return PatternSyntax)
            reserved "syntax"
            return sty)
         syms <- some syntaxSym
         when (all isExpr syms) $ unexpected "missing keywords in syntax rule"
         let ns = mapMaybe getName syms
         when (length ns /= length (nub ns))
            $ unexpected "repeated variable in syntax rule"
         lchar '='
         tm <- typeExpr (allowImp syn)
         terminator
         return (Rule (mkSimple syms) tm sty)
  where
    isExpr (Expr _) = True
    isExpr _ = False
    getName (Expr n) = Just n
    getName _ = Nothing
    -- Can't parse two full expressions (i.e. expressions with application) in a row
    -- so change them both to a simple expression
    mkSimple (Expr e : es) = SimpleExpr e : mkSimple' es
    mkSimple xs = mkSimple' xs

    mkSimple' (Expr e : Expr e1 : es) = SimpleExpr e : SimpleExpr e1 :
                                           mkSimple es
    mkSimple' (e : es) = e : mkSimple' es
    mkSimple' [] = []


{- | Parses a syntax symbol (either binding variable, keyword or expression)
SyntaxSym ::=   '[' Name_t ']'
             |  '{' Name_t '}'
             |  Name_t
             |  StringLiteral_t
             ;
 -}
syntaxSym :: IdrisParser SSymbol
syntaxSym =    try (do lchar '['; n <- name; lchar ']'
                       return (Expr n))
            <|> try (do lchar '{'; n <- name; lchar '}'
                        return (Binding n))
            <|> do n <- iName []
                   return (Keyword n)
            <|> do sym <- stringLiteral
                   return (Symbol sym)
            <?> "syntax symbol"

{- | Parses a function declaration with possible syntax sugar
  FunDecl ::= FunDecl';
-}
fnDecl :: SyntaxInfo -> IdrisParser [PDecl]
fnDecl syn
      = try (do notEndBlock
                d <- fnDecl' syn
                i <- get
                let d' = fmap (desugar syn i) d
                return [d'])
        <?> "function declaration"

{- Parses a function declaration
 FunDecl' ::=
  DocComment_t? FnOpts* Accessibility? FnOpts* FnName TypeSig Terminator
  | Postulate
  | Pattern
  | CAF
  ;
-}
fnDecl' :: SyntaxInfo -> IdrisParser PDecl
fnDecl' syn = do (doc, fc, opts', n, acc) <- try (do 
                        doc <- option "" (docComment '|')
                        pushIndent
                        ist <- get
                        let initOpts = if default_total ist
                                          then [TotalFn]
                                          else []
                        opts <- fnOpts initOpts
                        acc <- optional accessibility
                        opts' <- fnOpts opts
                        n_in <- fnName
                        let n = expandNS syn n_in
                        fc <- getFC
                        lchar ':'
                        return (doc, fc, opts', n, acc))
                 ty <- typeExpr (allowImp syn)
                 terminator
                 addAcc n acc
                 return (PTy doc syn fc opts' n ty)
            <|> postulate syn
            <|> caf syn
            <|> pattern syn
            <?> "function declaration"


{- Parses function options given initial options
FnOpts ::= 'total'
  | 'partial'
  | 'implicit'
  | '%' 'assert_total'
  | '%' 'reflection'
  | '%' 'specialise' '[' NameTimesList? ']'
  ;

NameTimes ::= FnName Natural?;

NameTimesList ::=
  NameTimes
  | NameTimes ',' NameTimesList
  ;

-}
-- FIXME: Check compatability for function options (i.e. partal/total)
fnOpts :: [FnOpt] -> IdrisParser [FnOpt]
fnOpts opts
        = do reserved "total"; fnOpts (TotalFn : opts)
      <|> do reserved "partial"; fnOpts (PartialFn : (opts \\ [TotalFn]))
      <|> do try (lchar '%' *> reserved "export"); c <- stringLiteral;
                  fnOpts (CExport c : opts)
      <|> do try (lchar '%' *> reserved "assert_total");
                  fnOpts (AssertTotal : opts)
      <|> do try (lchar '%' *> reserved "reflection");
                  fnOpts (Reflection : opts)
      <|> do lchar '%'; reserved "specialise";
             lchar '['; ns <- sepBy nameTimes (lchar ','); lchar ']'
             fnOpts (Specialise ns : opts)
      <|> do reserved "implicit"; fnOpts (Implicit : opts)
      <|> return opts
      <?> "function modifier"
  where nameTimes :: IdrisParser (Name, Maybe Int)
        nameTimes = do n <- fnName
                       t <- option Nothing (do reds <- natural
                                               return (Just (fromInteger reds)))
                       return (n, t)

{- | Parses an operator in function position i.e. enclosed by `()', with an
 optional namespace

  OperatorFront ::= (Identifier_t '.')? '(' Operator_t ')';
-}
operatorFront :: IdrisParser Name
operatorFront = maybeWithNS (lchar '(' *> operator <* lchar ')') False []

{- | Parses a function (either normal name or operator)
  FnName ::= Name | OperatorFront;
-}
fnName :: IdrisParser Name
fnName = try operatorFront <|> name <?> "function name"

{- | Parses an accessibilty modifier (e.g. public, private) -}
accessibility :: IdrisParser Accessibility
accessibility = do reserved "public";   return Public
            <|> do reserved "abstract"; return Frozen
            <|> do reserved "private";  return Hidden
            <?> "accessibility modifier"



{- | Parses a postulate

Postulate ::=
  DocComment_t? 'postulate' FnOpts* Accesibility? FnOpts* FnName TypeSig Terminator
  ;
-}
postulate :: SyntaxInfo -> IdrisParser PDecl
postulate syn = do doc <- try $ do doc <- option "" (docComment '|')
                                   pushIndent
                                   reserved "postulate"
                                   return doc
                   ist <- get
                   let initOpts = if default_total ist
                                     then [TotalFn]
                                     else []
                   opts <- fnOpts initOpts
                   acc <- optional accessibility
                   opts' <- fnOpts opts
                   n_in <- fnName
                   let n = expandNS syn n_in
                   lchar ':'
                   ty <- typeExpr (allowImp syn)
                   fc <- getFC
                   terminator
                   addAcc n acc
                   return (PPostulate doc syn fc opts' n ty)
                 <?> "postulate"

{- | Parses a using declaration

Using ::=
  'using' '(' UsingDeclList ')' OpenBlock Decl* CloseBlock
  ;
 -}
using_ :: SyntaxInfo -> IdrisParser [PDecl]
using_ syn =
    do reserved "using"; lchar '('; ns <- usingDeclList syn; lchar ')'
       openBlock
       let uvars = using syn
       ds <- many (decl (syn { using = uvars ++ ns }))
       closeBlock
       return (concat ds)
    <?> "using declaration"

{- | Parses a parameters declaration

Params ::=
  'parameters' '(' TypeDeclList ')' OpenBlock Decl* CloseBlock
  ;
 -}
params :: SyntaxInfo -> IdrisParser [PDecl]
params syn =
    do reserved "parameters"; lchar '('; ns <- typeDeclList syn; lchar ')'
       openBlock
       let pvars = syn_params syn
       ds <- many (decl syn { syn_params = pvars ++ ns })
       closeBlock
       fc <- getFC
       return [PParams fc ns (concat ds)]
    <?> "parameters declaration"

{- | Parses a mutual declaration (for mutually recursive functions)

Mutual ::=
  'mutual' OpenBlock Decl* CloseBlock
  ;
-}
mutual :: SyntaxInfo -> IdrisParser [PDecl]
mutual syn =
    do reserved "mutual"
       openBlock
       let pvars = syn_params syn
       ds <- many (decl syn)
       closeBlock
       fc <- getFC
       return [PMutual fc (concat ds)]
    <?> "mutual block"

{- | Parses a namespace declaration

Namespace ::=
  'namespace' identifier OpenBlock Decl+ CloseBlock
  ;
-}
namespace :: SyntaxInfo -> IdrisParser [PDecl]
namespace syn =
    do reserved "namespace"; n <- identifier;
       openBlock
       ds <- some (decl syn { syn_namespace = n : syn_namespace syn })
       closeBlock
       return [PNamespace n (concat ds)]
     <?> "namespace declaration"

{- | Parses a fixity declaration

Fixity ::=
  FixityType Natural_t OperatorList Terminator
  ;
-}
fixity :: IdrisParser PDecl
fixity = do pushIndent
            f <- fixityType; i <- natural; ops <- sepBy1 operator (lchar ',')
            terminator
            let prec = fromInteger i
            istate <- get
            let infixes = idris_infixes istate
            let fs      = map (Fix (f prec)) ops
            let redecls = map (alreadyDeclared infixes) fs
            let ill     = filter (not . checkValidity) redecls
            if null ill
               then do put (istate { idris_infixes = nub $ sort (fs ++ infixes)
                                     , ibc_write     = map IBCFix fs ++ ibc_write istate
                                   })
                       fc <- getFC
                       return (PFix fc (f prec) ops)
               else fail $ concatMap (\(f, (x:xs)) -> "Illegal redeclaration of fixity:\n\t\""
                                                ++ show f ++ "\" overrides \"" ++ show x ++ "\"") ill
         <?> "fixity declaration"
             where alreadyDeclared :: [FixDecl] -> FixDecl -> (FixDecl, [FixDecl])
                   alreadyDeclared fs f = (f, filter ((extractName f ==) . extractName) fs)

                   checkValidity :: (FixDecl, [FixDecl]) -> Bool
                   checkValidity (f, fs) = all (== f) fs

                   extractName :: FixDecl -> String
                   extractName (Fix _ n) = n

{- | Parses a fixity declaration type (i.e. infix or prefix, associtavity)
FixityType ::=
  'infixl'
  | 'infixr'
  | 'infix'
  | 'prefix'
  ;
 -}
fixityType :: IdrisParser (Int -> Fixity)
fixityType = do reserved "infixl"; return Infixl
         <|> do reserved "infixr"; return Infixr
         <|> do reserved "infix";  return InfixN
         <|> do reserved "prefix"; return PrefixN
         <?> "fixity type"

{- |Parses a methods block (for type classes and instances)
  MethodsBlock ::= 'where' OpenBlock FnDecl* CloseBlock
 -}
methodsBlock :: SyntaxInfo -> IdrisParser [PDecl]
methodsBlock syn = do reserved "where"
                      openBlock
                      ds <- many (fnDecl syn)
                      closeBlock
                      return (concat ds)
                   <?> "methods block"

{- |Parses a type class declaration

ClassArgument ::=
   Name
   | '(' Name ':' Expr ')'
   ;

Class ::=
  DocComment_t? Accessibility? 'class' ConstraintList? Name ClassArgument* MethodsBlock?
  ;
-}
class_ :: SyntaxInfo -> IdrisParser [PDecl]
class_ syn = do (doc, acc) <- try (do 
                  doc <- option "" (docComment '|')
                  acc <- optional accessibility
                  return (doc, acc))
                reserved "class"; fc <- getFC; cons <- constraintList syn; n_in <- name
                let n = expandNS syn n_in
                cs <- many carg
                ds <- option [] (methodsBlock syn)
                accData acc n (concatMap declared ds)
                return [PClass doc syn fc cons n cs ds]
             <?> "type-class declaration"
  where
    carg :: IdrisParser (Name, PTerm)
    carg = do lchar '('; i <- name; lchar ':'; ty <- expr syn; lchar ')'
              return (i, ty)
       <|> do i <- name;
              return (i, PType)

{- |Parses a type class instance declaration

  Instance ::=
    'instance' InstanceName? ConstraintList? Name SimpleExpr* MethodsBlock?
    ;

  InstanceName ::= '[' Name ']';
-}
instance_ :: SyntaxInfo -> IdrisParser [PDecl]
instance_ syn = do reserved "instance"; fc <- getFC
                   en <- optional instanceName
                   cs <- constraintList syn
                   cn <- name
                   args <- many (simpleExpr syn)
                   let sc = PApp fc (PRef fc cn) (map pexp args)
                   let t = bindList (PPi constraint) (map (\x -> (MN 0 "c", x)) cs) sc
                   ds <- option [] (methodsBlock syn)
                   return [PInstance syn fc cs cn args t en ds]
                 <?> "instance declaratioN"
  where instanceName :: IdrisParser Name
        instanceName = do lchar '['; n_in <- fnName; lchar ']'
                          let n = expandNS syn n_in
                          return n
                       <?> "instance name"


{- | Parses an expression as a whole
  FullExpr ::= Expr EOF_t;
 -}
fullExpr :: SyntaxInfo -> IdrisParser PTerm
fullExpr syn = do x <- expr syn
                  eof
                  i <- get
                  return $ desugar syn i x


{- |Parses an expression
  Expr ::= Expr';
-}
expr :: SyntaxInfo -> IdrisParser PTerm
expr syn = do i <- get
              buildExpressionParser (table (idris_infixes i)) (expr' syn)

{- | Parses either an internally defined expression or
    a user-defined one

Expr' ::=  "External (User-defined) Syntax"
      |   InternalExpr;

 -}
expr' :: SyntaxInfo -> IdrisParser PTerm
expr' syn =     try (externalExpr syn)
            <|> internalExpr syn
            <?> "expression"

{- | Parses a user-defined expression -}
externalExpr :: SyntaxInfo -> IdrisParser PTerm
externalExpr syn = do i <- get
                      extensions syn (syntax_rules i)
                   <?> "user-defined expression"

{- | Parses a simple user-defined expression -}
simpleExternalExpr :: SyntaxInfo -> IdrisParser PTerm
simpleExternalExpr syn = do i <- get
                            extensions syn (filter isSimple (syntax_rules i))
  where
    isSimple (Rule (Expr x:xs) _ _) = False
    isSimple (Rule (SimpleExpr x:xs) _ _) = False
    isSimple (Rule [Keyword _] _ _) = True
    isSimple (Rule [Symbol _]  _ _) = True
    isSimple (Rule (_:xs) _ _) = case last xs of
        Keyword _ -> True
        Symbol _  -> True
        _ -> False
    isSimple _ = False

{- | Tries to parse a user-defined expression given a list of syntactic extensions -}
extensions :: SyntaxInfo -> [Syntax] -> IdrisParser PTerm
extensions syn rules = choice (map (try . extension syn) (filter isValid rules))
                       <?> "user-defined expression"
  where
    isValid :: Syntax -> Bool
    isValid (Rule _ _ AnySyntax) = True
    isValid (Rule _ _ PatternSyntax) = inPattern syn
    isValid (Rule _ _ TermSyntax) = not (inPattern syn)


data SynMatch = SynTm PTerm | SynBind Name

{- | Tries to parse an expression given a user-defined rule -}
extension :: SyntaxInfo -> Syntax -> IdrisParser PTerm
extension syn (Rule ssym ptm _)
    = do smap <- mapM extensionSymbol ssym
         let ns = mapMaybe id smap
         return (update ns ptm) -- updated with smap
  where
    extensionSymbol :: SSymbol -> IdrisParser (Maybe (Name, SynMatch))
    extensionSymbol (Keyword n)    = do reserved (show n); return Nothing
    extensionSymbol (Expr n)       = do tm <- expr syn
                                        return $ Just (n, SynTm tm)
    extensionSymbol (SimpleExpr n) = do tm <- simpleExpr syn
                                        return $ Just (n, SynTm tm)
    extensionSymbol (Binding n)    = do b <- name
                                        return $ Just (n, SynBind b)
    extensionSymbol (Symbol s)     = do symbol s
                                        return Nothing
    dropn :: Name -> [(Name, a)] -> [(Name, a)]
    dropn n [] = []
    dropn n ((x,t) : xs) | n == x = xs
                         | otherwise = (x,t):dropn n xs

    updateB :: [(Name, SynMatch)] -> Name -> Name
    updateB ns n = case lookup n ns of
                     Just (SynBind t) -> t
                     _ -> n

    update :: [(Name, SynMatch)] -> PTerm -> PTerm
    update ns (PRef fc n) = case lookup n ns of
                              Just (SynTm t) -> t
                              _ -> PRef fc n
    update ns (PLam n ty sc) = PLam (updateB ns n) (update ns ty) (update (dropn n ns) sc)
    update ns (PPi p n ty sc) = PPi p (updateB ns n) (update ns ty) (update (dropn n ns) sc)
    update ns (PLet n ty val sc) = PLet (updateB ns n) (update ns ty) (update ns val)
                                          (update (dropn n ns) sc)
    update ns (PApp fc t args) = PApp fc (update ns t) (map (fmap (update ns)) args)
    update ns (PCase fc c opts) = PCase fc (update ns c) (map (pmap (update ns)) opts)
    update ns (PPair fc l r) = PPair fc (update ns l) (update ns r)
    update ns (PDPair fc l t r) = PDPair fc (update ns l) (update ns t) (update ns r)
    update ns (PAlternative a as) = PAlternative a (map (update ns) as)
    update ns (PHidden t) = PHidden (update ns t)
    update ns (PDoBlock ds) = PDoBlock $ upd ns ds
      where upd :: [(Name, SynMatch)] -> [PDo] -> [PDo]
            upd ns (DoExp fc t : ds) = DoExp fc (update ns t) : upd ns ds
            upd ns (DoBind fc n t : ds) = DoBind fc n (update ns t) : upd (dropn n ns) ds
            upd ns (DoLet fc n ty t : ds) = DoLet fc n (update ns ty) (update ns t)
                                                : upd (dropn n ns) ds
            upd ns (DoBindP fc i t : ds) = DoBindP fc (update ns i) (update ns t)
                                                : upd ns ds
            upd ns (DoLetP fc i t : ds) = DoLetP fc (update ns i) (update ns t)
                                                : upd ns ds
    update ns (PGoal fc r n sc) = PGoal fc (update ns r) n (update ns sc)
    update ns t = t

{- |Parses a (normal) built-in expression

InternalExpr ::=
  App
  | MatchApp
  | UnifyLog
  | RecordType
  | SimpleExpr
  | Lambda
  | QuoteGoal
  | Let
  | RewriteTerm
  | Pi
  | DoBlock
  ;
-}
internalExpr :: SyntaxInfo -> IdrisParser PTerm
internalExpr syn =
         try (app syn)
     <|> try (matchApp syn)
     <|> try (unifyLog syn)
     <|> recordType syn
     <|> try (simpleExpr syn)
     <|> lambda syn
     <|> quoteGoal syn
     <|> let_ syn
     <|> rewriteTerm syn
     <|> pi syn
     <|> doBlock syn
     <?> "expression"

{- | Parses a case expression
CaseExpr ::=
  'case' Expr 'of' OpenBlock CaseOption+ CloseBlock;
-}
caseExpr :: SyntaxInfo -> IdrisParser PTerm
caseExpr syn = do reserved "case"; fc <- getFC
                  scr <- expr syn; reserved "of";
                  opts <- indentedBlock1 (caseOption syn)
                  return (PCase fc scr opts)
               <?> "case expression"

{- | Parses a case in a case expression
CaseOption ::=
  Expr '=>' Expr Terminator
  ;
-}
caseOption :: SyntaxInfo -> IdrisParser (PTerm, PTerm)
caseOption syn = do lhs <- expr (syn { inPattern = True })
                    symbol "=>"; r <- expr syn
                    return (lhs, r)
                 <?> "case option"

{- | Parses a proof block
ProofExpr ::=
  'proof' OpenBlock Tactic'* CloseBlock
  ;
-}
proofExpr :: SyntaxInfo -> IdrisParser PTerm
proofExpr syn = do reserved "proof"
                   ts <- indentedBlock (tactic syn)
                   return $ PProof ts
                <?> "proof block"

{- | Parses a tactics block
TacticsExpr :=
  'tactics' OpenBlock Tactic'* CloseBlock
;
-}
tacticsExpr :: SyntaxInfo -> IdrisParser PTerm
tacticsExpr syn = do reserved "tactics"
                     ts <- indentedBlock (tactic syn)
                     return $ PTactics ts
                  <?> "tactics block"

{- | Parses a simple expresion
SimpleExpr ::=
  '![' Term ']'
  | '?' Name
  | % 'instance'
  | 'refl' ('{' Expr '}')?
  | ProofExpr
  | TacticsExpr
  | CaseExpr
  | FnName
  | List
  | Comprehension
  | Alt
  | Idiom
  | '(' Bracketed
  | Constant
  | Type
  | '_|_'
  | '_'
  | {- External (User-defined) Simple Expression -}
  ;
-}
simpleExpr :: SyntaxInfo -> IdrisParser PTerm
simpleExpr syn =
        {-try (do symbol "!["; t <- term; lchar ']'; return $ PQuote t)
        <|>-} do lchar '?'; x <- name; return (PMetavar x)
        <|> do lchar '%'; fc <- getFC; reserved "instance"; return (PResolveTC fc)
        <|> do reserved "refl"; fc <- getFC;
               tm <- option Placeholder (do lchar '{'; t <- expr syn; lchar '}';
                                            return t)
               return (PRefl fc tm)
        <|> proofExpr syn
        <|> tacticsExpr syn
        <|> caseExpr syn
        <|> try (do fc <- getFC
                    x <- fnName
                    return (PRef fc x))
        <|> try (listExpr syn)
        <|> try (comprehension syn)
        <|> try (alt syn)
        <|> try (idiom syn)
        <|> do lchar '('
               bracketed (disallowImp syn)
        <|> try (do c <- constant
                    fc <- getFC
                    return (modifyConst syn fc (PConstant c)))
        <|> do reserved "Type"; return PType
        <|> try (do symbol "_|_"
                    fc <- getFC
                    return (PFalse fc))
        <|> do lchar '_'; return Placeholder
        <|> simpleExternalExpr syn
        <?> "expression"


{- |Parses the rest of an expression in braces
Bracketed ::=
  ')'
  | Expr ')'
  | ExprList ')'
  | Expr '**' Expr ')'
  | Operator Expr ')'
  | Expr Operator ')'
  | Name ':' Expr '**' Expr ')'
  ;
-}
bracketed :: SyntaxInfo -> IdrisParser PTerm
bracketed syn =
            do lchar ')'
               fc <- getFC
               return $ PTrue fc
        <|>
        try (do l <- expr syn
                lchar ')'
                return l) 
        <|>  do (l, fc) <- try (do
                     l <- expr syn
                     fc <- getFC
                     lchar ','
                     return (l, fc))
                rs <- sepBy1 (do fc' <- getFC; r <- expr syn; return (r, fc')) (lchar ',')
                lchar ')'
                return $ PPair fc l (mergePairs rs)
        <|>  do (l, fc) <- try (do
                   l <- expr syn
                   fc <- getFC
                   reservedOp "**"
                   return (l, fc))
                r <- expr syn
                lchar ')'
                return (PDPair fc l Placeholder r)
        <|> try(do fc0 <- getFC
                   l <- simpleExpr syn
                   o <- operator
                   lchar ')'
                   return $ PLam (MN 1000 "ARG") Placeholder
                                    (PApp fc0 (PRef fc0 (UN o)) [pexp l,
                                                                 pexp (PRef fc0 (MN 1000 "ARG"))]))
        <|> try(do fc <- getFC; o <- operator; e <- expr syn; lchar ')'
                   return $ PLam (MN 1000 "ARG") Placeholder
                             (PApp fc (PRef fc (UN o)) [pexp (PRef fc (MN 1000 "ARG")),
                                                             pexp e]))
        <|> try (do ln <- name; lchar ':'
                    lty <- expr syn
                    reservedOp "**"
                    fc <- getFC
                    r <- expr syn
                    lchar ')'
                    return (PDPair fc (PRef fc ln) lty r))
        <?> "end of braced expression"
  where mergePairs :: [(PTerm, FC)] -> PTerm
        mergePairs [(t, fc)]    = t
        mergePairs ((t, fc):rs) = PPair fc t (mergePairs rs)

-- bit of a hack here. If the integer doesn't fit in an Int, treat it as a
-- big integer, otherwise try fromInteger and the constants as alternatives.
-- a better solution would be to fix fromInteger to work with Integer, as the
-- name suggests, rather than Int
{-| Finds optimal type for integer constant -}
modifyConst :: SyntaxInfo -> FC -> PTerm -> PTerm
modifyConst syn fc (PConstant (BI x))
    | not (inPattern syn)
        = PAlternative False
             (PApp fc (PRef fc (UN "fromInteger")) [pexp (PConstant (BI (fromInteger x)))]
             : consts)
    | otherwise = PAlternative False consts
    where
      consts = [ PConstant (BI x)
               , PConstant (I (fromInteger x))
               , PConstant (B8 (fromInteger x))
               , PConstant (B16 (fromInteger x))
               , PConstant (B32 (fromInteger x))
               , PConstant (B64 (fromInteger x))
               ]
modifyConst syn fc x = x

{- | Parses a list literal expression e.g. [1,2,3]
ListExpr ::=
  '[' ExprList? ']'
;

ExprList ::=
  Expr
  | Expr ',' ExprList
  ;

 -}
listExpr :: SyntaxInfo -> IdrisParser PTerm
listExpr syn = do lchar '['; fc <- getFC; xs <- sepBy (expr syn) (lchar ','); lchar ']'
                  return (mkList fc xs)
               <?> "list expression"
  where
    mkList :: FC -> [PTerm] -> PTerm
    mkList fc [] = PRef fc (UN "Nil")
    mkList fc (x : xs) = PApp fc (PRef fc (UN "::")) [pexp x, pexp (mkList fc xs)]


{- | Parses an alternative expression
  Alt ::= '(|' Expr_List '|)';

  Expr_List ::=
    Expr'
    | Expr' ',' Expr_List
  ;
-}
alt :: SyntaxInfo -> IdrisParser PTerm
alt syn = do symbol "(|"; alts <- sepBy1 (expr' syn) (lchar ','); symbol "|)"
             return (PAlternative False alts)

{- | Parses a possibly hidden simple expression
HSimpleExpr ::=
  '.' SimpleExpr
  | SimpleExpr
  ;
-}
hsimpleExpr :: SyntaxInfo -> IdrisParser PTerm
hsimpleExpr syn =
  do lchar '.'
     e <- simpleExpr syn
     return $ PHidden e
  <|> simpleExpr syn
  <?> "expression"

{- | Parses a matching application expression
MatchApp ::=
  SimpleExpr '<==' FnName
  ;
-}
matchApp :: SyntaxInfo -> IdrisParser PTerm
matchApp syn = do ty <- simpleExpr syn
                  symbol "<=="
                  fc <- getFC
                  f <- fnName
                  return (PLet (MN 0 "match")
                                ty
                                (PMatchApp fc f)
                                (PRef fc (MN 0 "match")))
               <?> "matching application expression"

{- | Parses a unification log expression
UnifyLog ::=
  '%' 'unifyLog' SimpleExpr
  ;
-}
unifyLog :: SyntaxInfo -> IdrisParser PTerm
unifyLog syn = do lchar '%'; reserved "unifyLog";
                  tm <- simpleExpr syn
                  return (PUnifyLog tm)
               <?> "unification log expression"

{- | Parses a function application expression
App ::=
  'mkForeign' Arg Arg*
  | SimpleExpr Arg+
  ;
-}
app :: SyntaxInfo -> IdrisParser PTerm
app syn = do f <- reserved "mkForeign"
             fc <- getFC
             fn <- arg syn
             args <- many (do notEndApp; arg syn)
             i <- get
             -- mkForeign f args ==>
             -- liftPrimIO (\w => mkForeignPrim f args w)
             let ap = PApp fc (PRef fc (UN "liftPrimIO"))
                       [pexp (PLam (MN 0 "w")
                             Placeholder
                             (PApp fc (PRef fc (UN "mkForeignPrim"))
                                         (fn : args ++
                                            [pexp (PRef fc (MN 0 "w"))])))]
             return (dslify i ap)

       <|> do f <- simpleExpr syn
              fc <- getFC
              args <- some (do notEndApp; arg syn)
              i <- get
              return (dslify i $ PApp fc f args)
       <?> "function application"
  where
    dslify :: IState -> PTerm -> PTerm
    dslify i (PApp fc (PRef _ f) [a])
        | [d] <- lookupCtxt f (idris_dsls i)
            = desugar (syn { dsl_info = d }) i (getTm a)
    dslify i t = t

{- |Parses a function argument
Arg ::=
  ImplicitArg
  | ConstraintArg
  | SimpleExpr
  ;
-}
arg :: SyntaxInfo -> IdrisParser PArg
arg syn =  implicitArg syn
       <|> constraintArg syn
       <|> do e <- simpleExpr syn
              return (pexp e)
       <?> "function argument"

{- |Parses an implicit function argument
ImplicitArg ::=
  '{' Name ('=' Expr)? '}'
  ;
-}
implicitArg :: SyntaxInfo -> IdrisParser PArg
implicitArg syn = do lchar '{'
                     n <- name
                     fc <- getFC
                     v <- option (PRef fc n) (do lchar '='
                                                 expr syn)
                     lchar '}'
                     return (pimp n v)
                  <?> "implicit function argument"

{- |Parses a constraint argument (for selecting a named type class instance)
ConstraintArg ::=
  '@{' Expr '}'
  ;
-}
constraintArg :: SyntaxInfo -> IdrisParser PArg
constraintArg syn = do symbol "@{"
                       e <- expr syn
                       symbol "}"
                       return (pconst e)
                    <?> "constraint argument"


{- |Parses a record field setter expression
RecordType ::=
  'record' '{' FieldTypeList '}';

FieldTypeList ::=
  FieldType
  | FieldType ',' FieldTypeList
  ;

FieldType ::=
  FnName '=' Expr
  ;
-}
recordType :: SyntaxInfo -> IdrisParser PTerm
recordType syn
    = do reserved "record"
         lchar '{'
         fields <- sepBy1 fieldType (lchar ',')
         lchar '}'
         fc <- getFC
         rec <- optional (simpleExpr syn)
         case rec of
            Nothing ->
                return (PLam (MN 0 "fldx") Placeholder
                            (applyAll fc fields (PRef fc (MN 0 "fldx"))))
            Just v -> return (applyAll fc fields v)
       <?> "record setting expression"
   where fieldType :: IdrisParser (Name, PTerm)
         fieldType = do n <- fnName
                        lchar '='
                        e <- expr syn
                        return (n, e)
                     <?> "field setter"
         applyAll :: FC -> [(Name, PTerm)] -> PTerm -> PTerm
         applyAll fc [] x = x
         applyAll fc ((n, e) : es) x
            = applyAll fc es (PApp fc (PRef fc (mkType n)) [pexp e, pexp x])

{- |Creates setters for record types on necessary functions -}
mkType :: Name -> Name
mkType (UN n) = UN ("set_" ++ n)
mkType (MN 0 n) = MN 0 ("set_" ++ n)
mkType (NS n s) = NS (mkType n) s

{- |Parses a type signature
TypeSig ::=
  ':' Expr
  ;
TypeExpr ::= ConstraintList? Expr;
 -}
typeExpr :: SyntaxInfo -> IdrisParser PTerm
typeExpr syn = do cs <- if implicitAllowed syn then constraintList syn else return []
                  sc <- expr syn
                  return (bindList (PPi constraint) (map (\x -> (MN 0 "c", x)) cs) sc)
               <?> "type signature"

{- |Parses a lambda expression
Lambda ::=
    '\\' TypeOptDeclList '=>' Expr
  | '\\' SimpleExprList  '=>' Expr
  ;
SimpleExprList ::=
  SimpleExpr
  | SimpleExpr ',' SimpleExprList
  ;
-}
lambda :: SyntaxInfo -> IdrisParser PTerm
lambda syn = do lchar '\\'
                try (do xt <- tyOptDeclList syn
                        symbol "=>"
                        sc <- expr syn
                        return (bindList PLam xt sc)
                 <|> (do ps <- sepBy (do fc <- getFC
                                         e <- simpleExpr syn
                                         return (fc, e)) (lchar ',')
                         symbol "=>"
                         sc <- expr syn
                         return (pmList (zip [0..] ps) sc)))
                 <?> "lambda expression"
    where pmList :: [(Int, (FC, PTerm))] -> PTerm -> PTerm
          pmList [] sc = sc
          pmList ((i, (fc, x)) : xs) sc
                = PLam (MN i "lamp") Placeholder
                        (PCase fc (PRef fc (MN i "lamp"))
                                [(x, pmList xs sc)])

{- |Parses a term rewrite expression
RewriteTerm ::=
  'rewrite' Expr ('==>' Expr)? 'in' Expr
  ;
-}
rewriteTerm :: SyntaxInfo -> IdrisParser PTerm
rewriteTerm syn = do reserved "rewrite"
                     fc <- getFC
                     prf <- expr syn
                     giving <- optional (do symbol "==>"; expr' syn)
                     reserved "in";  sc <- expr syn
                     return (PRewrite fc
                             (PApp fc (PRef fc (UN "sym")) [pexp prf]) sc
                               giving)
                  <?> "term rewrite expression"

{- |Parses a let binding
Let ::=
  'let' Name TypeSig'? '=' Expr  'in' Expr
| 'let' Expr'          '=' Expr' 'in' Expr

TypeSig' ::=
  ':' Expr'
  ;
 -}
let_ :: SyntaxInfo -> IdrisParser PTerm
let_ syn = try (do reserved "let"; n <- name;
                   ty <- option Placeholder (do lchar ':'; expr' syn)
                   lchar '='
                   v <- expr syn
                   reserved "in";  sc <- expr syn
                   return (PLet n ty v sc))
           <|> (do reserved "let"; fc <- getFC; pat <- expr' (syn { inPattern = True } )
                   symbol "="; v <- expr syn
                   reserved "in"; sc <- expr syn
                   return (PCase fc v [(pat, sc)]))
           <?> "let binding"

{- |Parses a quote goal
QuoteGoal ::=
  'quoteGoal' Name 'by' Expr 'in' Expr
  ;
 -}
quoteGoal :: SyntaxInfo -> IdrisParser PTerm
quoteGoal syn = do reserved "quoteGoal"; n <- name;
                   reserved "by"
                   r <- expr syn
                   reserved "in"
                   fc <- getFC
                   sc <- expr syn
                   return (PGoal fc r n sc)
                <?> "quote goal expression"

{- |Parses a dependent type signature
Pi ::=
    '|'? Static? '('           TypeDeclList ')' DocComment '->' Expr
  | '|'? Static? '{'           TypeDeclList '}'            '->' Expr
  |              '{' 'auto'    TypeDeclList '}'            '->' Expr
  |              '{' 'default' TypeDeclList '}'            '->' Expr
  |              '{' 'static'               '}' Expr'      '->' Expr
  ;
 -}
pi syn =
     try (do lazy <- if implicitAllowed syn -- laziness is top level only
                        then option False (do lchar '|'; return True)
                        else return False
             st <- static
             lchar '('; xt <- typeDeclList syn; lchar ')'
             doc <- option "" (docComment '^')
             symbol "->"
             sc <- expr syn
             return (bindList (PPi (Exp lazy st doc)) xt sc))
 <|> try (if implicitAllowed syn
             then do lazy <- option False (do lchar '|'
                                              return True)
                     st <- static
                     lchar '{'
                     xt <- typeDeclList syn
                     lchar '}'
                     symbol "->"
                     sc <- expr syn
                     return (bindList (PPi (Imp lazy st "")) xt sc)
             else fail "no implicit arguments allowed here")
 <|> try (do lchar '{'
             reserved "auto"
             xt <- typeDeclList syn
             lchar '}'
             symbol "->"
             sc <- expr syn
             return (bindList (PPi
                      (TacImp False Dynamic (PTactics [Trivial]) "")) xt sc))
 <|> try (do lchar '{'
             reserved "default"
             script <- simpleExpr syn
             xt <- typeDeclList syn
             lchar '}'
             symbol "->"
             sc <- expr syn
             return (bindList (PPi (TacImp False Dynamic script "")) xt sc))
 <|> do lchar '{'
        reserved "static"
        lchar '}'
        t <- expr' syn
        symbol "->"
        sc <- expr syn
        return (PPi (Exp False Static "") (MN 42 "__pi_arg") t sc)
  <?> "dependent type signature"

{- | Parses a type constraint list
ConstraintList ::=
    '(' Expr_List ')' '=>'
  | Expr              '=>'
  ;
-}
constraintList :: SyntaxInfo -> IdrisParser [PTerm]
constraintList syn = try (do lchar '('
                             tys <- sepBy1 (expr' (disallowImp syn)) (lchar ',')
                             lchar ')'
                             reservedOp "=>"
                             return tys)
                 <|> try (do t <- expr (disallowImp syn)
                             reservedOp "=>"
                             return [t])
                 <|> return []
                 <?> "type constraint list"

{- | Parses a using declaration list
UsingDeclList ::=
  UsingDeclList'
  | NameList TypeSig
  ;

UsingDeclList' ::=
  UsingDecl
  | UsingDecl ',' UsingDeclList'
  ;

NameList ::=
  Name
  | Name ',' NameList
  ;
-}
usingDeclList :: SyntaxInfo -> IdrisParser [Using]
usingDeclList syn
               = try (sepBy1 (usingDecl syn) (lchar ','))
             <|> do ns <- sepBy1 name (lchar ',')
                    lchar ':'
                    t <- typeExpr (disallowImp syn)
                    return (map (\x -> UImplicit x t) ns)
             <?> "using declaration list"

{- |Parses a using declaration
UsingDecl ::=
  FnName TypeSig
  | FnName FnName+
  ;
-}
usingDecl :: SyntaxInfo -> IdrisParser Using
usingDecl syn = try (do x <- fnName
                        lchar ':'
                        t <- typeExpr (disallowImp syn)
                        return (UImplicit x t))
            <|> do c <- fnName
                   xs <- some fnName
                   return (UConstraint c xs)
            <?> "using declaration"

{- |Parses a type declaration list
TypeDeclList ::=
    FunctionSignatureList
  | NameList TypeSig
  ;

FunctionSignatureList ::=
    Name TypeSig
  | Name TypeSig ',' FunctionSignatureList
  ;
-}
typeDeclList :: SyntaxInfo -> IdrisParser [(Name, PTerm)]
typeDeclList syn = try (sepBy1 (do x <- fnName
                                   lchar ':'
                                   t <- typeExpr (disallowImp syn)
                                   return (x,t))
                           (lchar ','))
                   <|> do ns <- sepBy1 name (lchar ',')
                          lchar ':'
                          t <- typeExpr (disallowImp syn)
                          return (map (\x -> (x, t)) ns)
                   <?> "type declaration list"

{- |Parses a type declaration list with optional parameters
TypeOptDeclList ::=
    NameOrPlaceholder TypeSig?
  | NameOrPlaceholder TypeSig? ',' TypeOptDeclList
  ;

NameOrPlaceHolder ::= Name | '_';
-}
tyOptDeclList :: SyntaxInfo -> IdrisParser [(Name, PTerm)]
tyOptDeclList syn = sepBy1 (do x <- nameOrPlaceholder
                               t <- option Placeholder (do lchar ':'
                                                           expr syn)
                               return (x,t))
                           (lchar ',')
                    <?> "type declaration list"
    where  nameOrPlaceholder :: IdrisParser Name
           nameOrPlaceholder = fnName
                           <|> do symbol "_"
                                  return (MN 0 "underscore")
                           <?> "name or placeholder"

{- |Parses a list comprehension
Comprehension ::= '[' Expr '|' DoList ']';

DoList ::=
    Do
  | Do ',' DoList
  ;
-}
comprehension :: SyntaxInfo -> IdrisParser PTerm
comprehension syn
    = do lchar '['
         fc <- getFC
         pat <- expr syn
         lchar '|'
         qs <- sepBy1 (do_ syn) (lchar ',')
         lchar ']'
         return (PDoBlock (map addGuard qs ++
                    [DoExp fc (PApp fc (PRef fc (UN "return"))
                                 [pexp pat])]))
      <?> "list comprehension"
    where addGuard :: PDo -> PDo
          addGuard (DoExp fc e) = DoExp fc (PApp fc (PRef fc (UN "guard"))
                                                    [pexp e])
          addGuard x = x

{- |Parses a do-block
Do' ::= Do KeepTerminator;

DoBlock ::=
  'do' OpenBlock Do'+ CloseBlock
  ;
 -}
doBlock :: SyntaxInfo -> IdrisParser PTerm
doBlock syn
    = do reserved "do"
         ds <- indentedBlock (do_ syn)
         return (PDoBlock ds)
      <?> "do block"

{- |Parses an expression inside a do block
Do ::=
    'let' Name  TypeSig'?      '=' Expr
  | 'let' Expr'                '=' Expr
  | Name  '<-' Expr
  | Expr' '<-' Expr
  | Expr
  ;
-}
do_ :: SyntaxInfo -> IdrisParser PDo
do_ syn
     = try (do reserved "let"
               i <- name
               ty <- option Placeholder (do lchar ':'
                                            expr' syn)
               reservedOp "="
               fc <- getFC
               e <- expr syn
               return (DoLet fc i ty e))
   <|> try (do reserved "let"
               i <- expr' syn
               reservedOp "="
               fc <- getFC
               sc <- expr syn
               return (DoLetP fc i sc))
   <|> try (do i <- name
               symbol "<-"
               fc <- getFC
               e <- expr syn;
               return (DoBind fc i e))
   <|> try (do i <- expr' syn
               symbol "<-"
               fc <- getFC
               e <- expr syn;
               return (DoBindP fc i e))
   <|> do e <- expr syn
          fc <- getFC
          return (DoExp fc e)
   <?> "do block expression"

{- |Parses an expression in idiom brackets
Idiom ::= '[|' Expr '|]';
-}
idiom :: SyntaxInfo -> IdrisParser PTerm
idiom syn
    = do symbol "[|"
         fc <- getFC
         e <- expr syn
         symbol "|]"
         return (PIdiom fc e)
      <?> "expression in idiom brackets"

{- |Parses a constant or literal expression
Constant ::=
    'Integer'
  | 'Int'
  | 'Char'
  | 'Float'
  | 'String'
  | 'Ptr'
  | 'Bits8'
  | 'Bits16'
  | 'Bits32'
  | 'Bits64'
  | 'Bits8x16'
  | 'Bits16x8'
  | 'Bits32x4'
  | 'Bits64x2'
  | Float_t
  | Natural_t
  | String_t
  | Char_t
  ;
-}
constant :: IdrisParser Core.TT.Const
constant =  do reserved "Integer";return (AType (ATInt ITBig))
        <|> do reserved "Int";    return (AType (ATInt ITNative))
        <|> do reserved "Char";   return (AType (ATInt ITChar))
        <|> do reserved "Float";  return (AType ATFloat)
        <|> do reserved "String"; return StrType
        <|> do reserved "Ptr";    return PtrType
        <|> do reserved "Bits8";  return (AType (ATInt (ITFixed IT8)))
        <|> do reserved "Bits16"; return (AType (ATInt (ITFixed IT16)))
        <|> do reserved "Bits32"; return (AType (ATInt (ITFixed IT32)))
        <|> do reserved "Bits64"; return (AType (ATInt (ITFixed IT64)))
        <|> do reserved "Bits8x16"; return (AType (ATInt (ITVec IT8 16)))
        <|> do reserved "Bits16x8"; return (AType (ATInt (ITVec IT16 8)))
        <|> do reserved "Bits32x4"; return (AType (ATInt (ITVec IT32 4)))
        <|> do reserved "Bits64x2"; return (AType (ATInt (ITVec IT64 2)))
        <|> try (do f <- float;   return $ Fl f)
        <|> try (do i <- natural; return $ BI i)
        <|> try (do s <- stringLiteral;  return $ Str s)
        <|> try (do c <- charLiteral;   return $ Ch c)
        <?> "constant or literal"

{- |Parses a static modifier
Static ::=
  '[' static ']'
;
-}
static :: IdrisParser Static
static =     do lchar '['; reserved "static"; lchar ']'; return Static
         <|> return Dynamic
         <?> "static modifier"

{- |Parses a record type declaration
Record ::=
    DocComment Accessibility? 'record' FnName TypeSig 'where' OpenBlock Constructor KeepTerminator CloseBlock;
-}
record :: SyntaxInfo -> IdrisParser PDecl
record syn = do (doc, acc) <- try (do 
                      doc <- option "" (docComment '|')
                      acc <- optional accessibility
                      reserved "record"
                      return (doc, acc))
                fc <- getFC
                tyn_in <- fnName
                lchar ':'
                ty <- typeExpr (allowImp syn)
                let tyn = expandNS syn tyn_in
                reserved "where"
                (cdoc, cn, cty, _) <- indentedBlockS (constructor syn)
                accData acc tyn [cn]
                let rsyn = syn { syn_namespace = show (nsroot tyn) :
                                                    syn_namespace syn }
                let fns = getRecNames rsyn cty
                mapM_ (\n -> addAcc n acc) fns
                return $ PRecord doc rsyn fc tyn ty cdoc cn cty
             <?> "record type declaration"
  where
    getRecNames :: SyntaxInfo -> PTerm -> [Name]
    getRecNames syn (PPi _ n _ sc) = [expandNS syn n, expandNS syn (mkType n)]
                                       ++ getRecNames syn sc
    getRecNames _ _ = []

    toFreeze :: Maybe Accessibility -> Maybe Accessibility
    toFreeze (Just Frozen) = Just Hidden
    toFreeze x = x

{- | Parses data declaration type (normal or codata)
DataI ::= 'data' | 'codata';
-}
dataI :: IdrisParser Bool
dataI = do reserved "data"; return False
    <|> do reserved "codata"; return True

{- | Parses a data type declaration
Data ::= DocComment? Accessibility? DataI FnName TypeSig ExplicitTypeDataRest?
       | DocComment? Accessibility? DataI FnName Name*   DataRest?
       ;
Constructor' ::= Constructor KeepTerminator;
ExplicitTypeDataRest ::= 'where' OpenBlock Constructor'* CloseBlock;

DataRest ::= '=' SimpleConstructorList Terminator
            | 'where'!
           ;
SimpleConstructorList ::=
    SimpleConstructor
  | SimpleConstructor '|' SimpleConstructorList
  ;
-}
data_ :: SyntaxInfo -> IdrisParser PDecl
data_ syn = do (doc, acc, co) <- try (do
                    doc <- option "" (docComment '|')
                    pushIndent
                    acc <- optional accessibility
                    co <- dataI
                    return (doc, acc, co))
               fc <- getFC
               tyn_in <- fnName
               (do try (lchar ':')
                   popIndent
                   ty <- typeExpr (allowImp syn)
                   let tyn = expandNS syn tyn_in
                   option (PData doc syn fc co (PLaterdecl tyn ty)) (do
                     reserved "where"
                     cons <- indentedBlock (constructor syn)
                     accData acc tyn (map (\ (_, n, _, _) -> n) cons)
                     return $ PData doc syn fc co (PDatadecl tyn ty cons))) <|> (do
                    args <- many name
                    let ty = bindArgs (map (const PType) args) PType
                    let tyn = expandNS syn tyn_in
                    option (PData doc syn fc co (PLaterdecl tyn ty)) (do
                      try (lchar '=') <|> do reserved "where"
                                             let kw = (if co then "co" else "") ++ "data "
                                             let n  = show tyn_in ++ " "
                                             let s  = kw ++ n
                                             let as = concat (intersperse " " $ map show args) ++ " "
                                             let ns = concat (intersperse " -> " $ map ((\x -> "(" ++ x ++ " : Type)") . show) args)
                                             let ss = concat (intersperse " -> " $ map (const "Type") args)
                                             let fix1 = s ++ as ++ " = ..."
                                             let fix2 = s ++ ": " ++ ns ++ " -> Type where\n  ..."
                                             let fix3 = s ++ ": " ++ ss ++ " -> Type where\n  ..."
                                             fail $ fixErrorMsg "unexpected \"where\"" [fix1, fix2, fix3]
                      cons <- sepBy1 (simpleConstructor syn) (lchar '|')
                      terminator
                      let conty = mkPApp fc (PRef fc tyn) (map (PRef fc) args)
                      cons' <- mapM (\ (doc, x, cargs, cfc) ->
                                   do let cty = bindArgs cargs conty
                                      return (doc, x, cty, cfc)) cons
                      accData acc tyn (map (\ (_, n, _, _) -> n) cons')
                      return $ PData doc syn fc co (PDatadecl tyn ty cons')))
           <?> "data type declaration"
  where
    mkPApp :: FC -> PTerm -> [PTerm] -> PTerm
    mkPApp fc t [] = t
    mkPApp fc t xs = PApp fc t (map pexp xs)
    bindArgs :: [PTerm] -> PTerm -> PTerm
    bindArgs xs t = foldr (PPi expl (MN 0 "t")) t xs


{- | Parses a type constructor declaration
  Constructor ::= DocComment? FnName TypeSig;
-}
constructor :: SyntaxInfo -> IdrisParser (String, Name, PTerm, FC)
constructor syn
    = do doc <- option "" (docComment '|')
         cn_in <- fnName; fc <- getFC
         let cn = expandNS syn cn_in
         lchar ':'
         ty <- typeExpr (allowImp syn)
         return (doc, cn, ty, fc)
      <?> "constructor"

{- | Parses a constructor for simple discriminative union data types
  SimpleConstructor ::= FnName SimpleExpr* DocComment?
-}
simpleConstructor :: SyntaxInfo -> IdrisParser (String, Name, [PTerm], FC)
simpleConstructor syn
     = do cn_in <- fnName
          let cn = expandNS syn cn_in
          fc <- getFC
          args <- many (do notEndApp
                           simpleExpr syn)
          doc <- option "" (docComment '^')
          return (doc, cn, args, fc)
       <?> "constructor"

{- | Parses a dsl block declaration
DSL ::= 'dsl' FnName OpenBlock Overload'+ CloseBlock;
 -}
dsl :: SyntaxInfo -> IdrisParser PDecl
dsl syn = do reserved "dsl"
             n <- fnName
             bs <- indentedBlock (overload syn)
             let dsl = mkDSL bs (dsl_info syn)
             checkDSL dsl
             i <- get
             put (i { idris_dsls = addDef n dsl (idris_dsls i) })
             return (PDSL n dsl)
          <?> "dsl block declaration"
    where mkDSL :: [(String, PTerm)] -> DSL -> DSL
          mkDSL bs dsl = let var    = lookup "variable" bs
                             first  = lookup "index_first" bs
                             next   = lookup "index_next" bs
                             leto   = lookup "let" bs
                             lambda = lookup "lambda" bs in
                             initDSL { dsl_var = var,
                                       index_first = first,
                                       index_next = next,
                                       dsl_lambda = lambda,
                                       dsl_let = leto }

{- | Checks DSL for errors -}
-- FIXME: currently does nothing, check if DSL is really sane
checkDSL :: DSL -> IdrisParser ()
checkDSL dsl = return ()

{- | Parses a DSL overload declaration
OverloadIdentifier ::= 'let' | Identifier;
Overload ::= OverloadIdentifier '=' Expr;
-}
overload :: SyntaxInfo -> IdrisParser (String, PTerm)
overload syn = do o <- identifier <|> do reserved "let"
                                         return "let"
                  if o `notElem` overloadable
                     then fail $ show o ++ " is not an overloading"
                     else do
                       lchar '='
                       t <- expr syn
                       return (o, t)
               <?> "dsl overload declaratioN"
    where overloadable = ["let","lambda","index_first","index_next","variable"]

{- | Parse a clause with patterns
Pattern ::= Clause;
-}
pattern :: SyntaxInfo -> IdrisParser PDecl
pattern syn = do fc <- getFC
                 clause <- clause syn
                 return (PClauses fc [] (MN 2 "_") [clause]) -- collect together later
              <?> "pattern"

{- | Parse a constant applicative form declaration
  CAF ::= 'let' FnName '=' Expr Terminator;
-}
caf :: SyntaxInfo -> IdrisParser PDecl
caf syn = do reserved "let"
             n_in <- fnName; let n = expandNS syn n_in
             lchar '='
             t <- expr syn
             terminator
             fc <- getFC
             return (PCAF fc n t)
           <?> "constant applicative form declaration"

{- | Parse an argument expression
  ArgExpr ::= HSimpleExpr | {- In Pattern External (User-defined) Expression -};
-}
argExpr :: SyntaxInfo -> IdrisParser PTerm
argExpr syn = let syn' = syn { inPattern = True } in
                  try (hsimpleExpr syn') <|> simpleExternalExpr syn'
              <?> "argument expression"

{- | Parse a right hand side of a function
RHS ::= '='            Expr
     |  '?='  RHSName? Expr
     |  'impossible'
     ;

RHSName ::= '{' FnName '}';
-}
rhs :: SyntaxInfo -> Name -> IdrisParser PTerm
rhs syn n = do lchar '='; expr syn
        <|> do symbol "?=";
               name <- option n' (do symbol "{"; n <- fnName; symbol "}";
                                     return n)
               r <- expr syn
               return (addLet name r)
        <|> do reserved "impossible"; return PImpossible
        <?> "function right hand side"
  where mkN :: Name -> Name
        mkN (UN x)   = UN (x++"_lemma_1")
        mkN (NS x n) = NS (mkN x) n
        n' :: Name
        n' = mkN n
        addLet :: Name -> PTerm -> PTerm
        addLet nm (PLet n ty val r) = PLet n ty val (addLet nm r)
        addLet nm (PCase fc t cs) = PCase fc t (map addLetC cs)
          where addLetC (l, r) = (l, addLet nm r)
        addLet nm r = (PLet (UN "value") Placeholder r (PMetavar nm))

{- |Parses a function clause
RHSOrWithBlock ::= RHS WhereOrTerminator
               | 'with' SimpleExpr OpenBlock FnDecl+ CloseBlock
               ;
Clause ::=                                                               WExpr+ RHSOrWithBlock
       |   SimpleExpr '<=='  FnName                                             RHS WhereOrTerminator
       |   ArgExpr Operator ArgExpr                                      WExpr* RHSOrWithBlock {- Except "=" and "?=" operators to avoid ambiguity -}
       |                     FnName ConstraintArg* ImplicitOrArgExpr*    WExpr* RHSOrWithBlock
       ;
ImplicitOrArgExpr ::= ImplicitArg | ArgExpr;
WhereOrTerminator ::= WhereBlock | Terminator;
-}
clause :: SyntaxInfo -> IdrisParser PClause
clause syn
         = do wargs <- try (do pushIndent; some (wExpr syn))
              fc <- getFC
              ist <- get
              n <- case lastParse ist of
                        Just t -> return t
                        Nothing -> fail "Invalid clause"
              (do r <- rhs syn n
                  let ctxt = tt_ctxt ist
                  let wsyn = syn { syn_namespace = [] }
                  (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                               popIndent
                                               return x,
                                            do terminator
                                               return ([], [])]
                  return $ PClauseR fc wargs r wheres) <|> (do
                  popIndent
                  reserved "with"
                  wval <- simpleExpr syn
                  openBlock
                  ds <- some $ fnDecl syn
                  let withs = concat ds
                  closeBlock
                  return $ PWithR fc wargs wval withs)
       <|> do ty <- try (do pushIndent
                            ty <- simpleExpr syn
                            symbol "<=="
                            return ty)
              fc <- getFC
              n_in <- fnName; let n = expandNS syn n_in
              r <- rhs syn n
              ist <- get
              let ctxt = tt_ctxt ist
              let wsyn = syn { syn_namespace = [] }
              (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                           popIndent
                                           return x,
                                        do terminator
                                           return ([], [])]
              let capp = PLet (MN 0 "match")
                              ty
                              (PMatchApp fc n)
                              (PRef fc (MN 0 "match"))
              ist <- get
              put (ist { lastParse = Just n })
              return $ PClause fc n capp [] r wheres
       <|> do (l, op) <- try (do 
                pushIndent
                l <- argExpr syn
                op <- operator
                when (op == "=" || op == "?=" ) (fail "infix clause definition with \"=\" and \"?=\" not supported ")
                return (l, op))
              let n = expandNS syn (UN op)
              r <- argExpr syn
              fc <- getFC
              wargs <- many (wExpr syn)
              (do rs <- rhs syn n
                  let wsyn = syn { syn_namespace = [] }
                  (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                               popIndent
                                               return x,
                                            do terminator
                                               return ([], [])]
                  ist <- get
                  let capp = PApp fc (PRef fc n) [pexp l, pexp r]
                  put (ist { lastParse = Just n })
                  return $ PClause fc n capp wargs rs wheres) <|> (do
                   popIndent
                   reserved "with"
                   lchar '(' <?> "parenthesized expression"
                   wval <- bracketed syn
                   openBlock
                   ds <- some $ fnDecl syn
                   closeBlock
                   ist <- get
                   let capp = PApp fc (PRef fc n) [pexp l, pexp r]
                   let withs = map (fillLHSD n capp wargs) $ concat ds
                   put (ist { lastParse = Just n })
                   return $ PWith fc n capp wargs wval withs)
       <|> do pushIndent
              n_in <- fnName; let n = expandNS syn n_in
              cargs <- many (constraintArg syn)
              fc <- getFC
              args <- many (try (implicitArg (syn { inPattern = True } ))
                            <|> (fmap pexp (argExpr syn)))
              wargs <- many (wExpr syn)
              let capp = PApp fc (PRef fc n)
                           (cargs ++ args)
              (do r <- rhs syn n
                  ist <- get
                  let ctxt = tt_ctxt ist
                  let wsyn = syn { syn_namespace = [] }
                  (wheres, nmap) <- choice [do x <- whereBlock n wsyn
                                               popIndent
                                               return x,
                                            do terminator
                                               return ([], [])]
                  ist <- get
                  put (ist { lastParse = Just n })
                  return $ PClause fc n capp wargs r wheres) <|> (do
                   reserved "with"
                   ist <- get
                   put (ist { lastParse = Just n })
                   lchar '(' <?> "parenthesized expression"
                   wval <- bracketed syn
                   openBlock
                   ds <- some $ fnDecl syn
                   let withs = map (fillLHSD n capp wargs) $ concat ds
                   closeBlock
                   popIndent
                   return $ PWith fc n capp wargs wval withs)
      <?> "function clause"
  where
    fillLHS :: Name -> PTerm -> [PTerm] -> PClause -> PClause
    fillLHS n capp owargs (PClauseR fc wargs v ws)
       = PClause fc n capp (owargs ++ wargs) v ws
    fillLHS n capp owargs (PWithR fc wargs v ws)
       = PWith fc n capp (owargs ++ wargs) v
            (map (fillLHSD n capp (owargs ++ wargs)) ws)
    fillLHS _ _ _ c = c

    fillLHSD :: Name -> PTerm -> [PTerm] -> PDecl -> PDecl
    fillLHSD n c a (PClauses fc o fn cs) = PClauses fc o fn (map (fillLHS n c a) cs)
    fillLHSD n c a x = x

{- |Parses with pattern
 WExpr ::= '|' Expr';
-}
wExpr :: SyntaxInfo -> IdrisParser PTerm
wExpr syn = do lchar '|'
               expr' syn
            <?> "with pattern"

{- |Parses a where block
WhereBlock ::= 'where' OpenBlock Decl+ CloseBlock;
 -}
whereBlock :: Name -> SyntaxInfo -> IdrisParser ([PDecl], [(Name, Name)])
whereBlock n syn
    = do reserved "where"
         ds <- indentedBlock1 (decl syn)
         let dns = concatMap (concatMap declared) ds
         return (concat ds, map (\x -> (x, decoration syn x)) dns)
      <?> "where block"

{- |Parses a code generation target language name
Codegen ::= 'C'
        |   'Java'
        |   'JavaScript'
        |   'Node'
        |   'LLVM'
        |   'Bytecode'
        ;
-}
codegen_ :: IdrisParser Codegen
codegen_ = do reserved "C"; return ViaC
       <|> do reserved "Java"; return ViaJava
       <|> do reserved "JavaScript"; return ViaJavaScript
       <|> do reserved "Node"; return ViaNode
       <|> do reserved "LLVM"; return ViaLLVM
       <|> do reserved "Bytecode"; return Bytecode
       <?> "code generation language"

{- |Parses a compiler directive
StringList ::=
  String
  | String ',' StringList
  ;

Directive ::= '%' Directive';

Directive' ::= 'lib'      CodeGen String_t
           |   'link'     CodeGen String_t
           |   'flag'     CodeGen String_t
           |   'include'  CodeGen String_t
           |   'hide'     Name
           |   'freeze'   Name
           |   'access'   Accessibility
           |   'default'  Totality
           |   'logging'  Natural
           |   'dynamic'  StringList
           |   'language' 'TypeProviders'
           |   'language' 'ErrorReflection'
           ;
-}
directive :: SyntaxInfo -> IdrisParser [PDecl]
directive syn = do try (lchar '%' *> reserved "lib"); cgn <- codegen_; lib <- stringLiteral;
                   return [PDirective (do addLib cgn lib
                                          addIBC (IBCLib cgn lib))]
             <|> do try (lchar '%' *> reserved "link"); cgn <- codegen_; obj <- stringLiteral;
                    return [PDirective (do dirs <- allImportDirs
                                           o <- liftIO $ findInPath dirs obj
                                           addIBC (IBCObj cgn obj) -- just name, search on loading ibc
                                           addObjectFile cgn o)]
             <|> do try (lchar '%' *> reserved "flag"); cgn <- codegen_;
                    flag <- stringLiteral
                    return [PDirective (do addIBC (IBCCGFlag cgn flag)
                                           addFlag cgn flag)]
             <|> do try (lchar '%' *> reserved "include"); cgn <- codegen_; hdr <- stringLiteral;
                    return [PDirective (do addHdr cgn hdr
                                           addIBC (IBCHeader cgn hdr))]
             <|> do try (lchar '%' *> reserved "hide"); n <- iName []
                    return [PDirective (do setAccessibility n Hidden
                                           addIBC (IBCAccess n Hidden))]
             <|> do try (lchar '%' *> reserved "freeze"); n <- iName []
                    return [PDirective (do setAccessibility n Frozen
                                           addIBC (IBCAccess n Frozen))]
             <|> do try (lchar '%' *> reserved "access"); acc <- accessibility
                    return [PDirective (do i <- get
                                           put(i { default_access = acc }))]
             <|> do try (lchar '%' *> reserved "default"); tot <- totality
                    i <- get
                    put (i { default_total = tot } )
                    return [PDirective (do i <- get
                                           put(i { default_total = tot }))]
             <|> do try (lchar '%' *> reserved "logging"); i <- natural;
                    return [PDirective (setLogLevel (fromInteger i))]
             <|> do try (lchar '%' *> reserved "dynamic"); libs <- sepBy1 stringLiteral (lchar ',');
                    return [PDirective (do added <- addDyLib libs
                                           case added of
                                             Left lib -> addIBC (IBCDyLib (lib_name lib))
                                             Right msg ->
                                                 fail $ msg)]
             <|> do try (lchar '%' *> reserved "language"); ext <- pLangExt;
                    return [PDirective (addLangExt ext)]
             <?> "directive"

pLangExt :: IdrisParser LanguageExt
pLangExt = (reserved "TypeProviders" >> return TypeProviders)
       <|> (reserved "ErrorReflection" >> return ErrorReflection)

{- | Parses a totality
Totality ::= 'partial' | 'total'
-}
totality :: IdrisParser Bool
totality
        = do reserved "total";   return True
      <|> do reserved "partial"; return False

{- | Parses a type provider
Provider ::= '%' 'provide' '(' FnName TypeSig ')' 'with' Expr;
 -}
provider :: SyntaxInfo -> IdrisParser [PDecl]
provider syn = do try (lchar '%' *> reserved "provide");
                  lchar '('; n <- fnName; lchar ':'; t <- typeExpr syn; lchar ')'
                  fc <- getFC
                  reserved "with"
                  e <- expr syn
                  return  [PProvider syn fc n t e]
               <?> "type provider"

{- | Parses a transform
Transform ::= '%' 'transform' Expr '==>' Expr
-}
transform :: SyntaxInfo -> IdrisParser [PDecl]
transform syn = do try (lchar '%' *> reserved "transform")
                    -- leave it unchecked, until we work out what this should
                    -- actually mean...
--                     safety <- option True (do reserved "unsafe"
--                                               return False)
                   l <- expr syn
                   fc <- getFC
                   symbol "==>"
                   r <- expr syn
                   return [PTransform fc False l r]
                <?> "transform"

{- | Parses a tactic script
Tactic ::= 'intro' NameList?
       |   'intros'
       |   'refine'      Name Imp+
       |   'mrefine'     Name
       |   'rewrite'     Expr
       |   'equiv'       Expr
       |   'let'         Name ':' Expr' '=' Expr
       |   'let'         Name           '=' Expr
       |   'focus'       Name
       |   'exact'       Expr
       |   'applyTactic' Expr
       |   'reflect'     Expr
       |   'fill'        Expr
       |   'try'         Tactic '|' Tactic
       |   '{' TacticSeq '}'
       |   'compute'
       |   'trivial'
       |   'solve'
       |   'attack'
       |   'state'
       |   'term'
       |   'undo'
       |   'qed'
       |   'abandon'
       |   ':' 'q'
       ;

Imp ::= '?' | '_';

TacticSeq ::=
    Tactic ';' Tactic
  | Tactic ';' TacticSeq
  ;

-}

tactic :: SyntaxInfo -> IdrisParser PTactic
tactic syn = do reserved "intro"; ns <- sepBy name (lchar ',')
                return $ Intro ns
          <|> do reserved "intros"; return Intros
          <|> try (do reserved "refine"; n <- name
                      imps <- some imp
                      return $ Refine n imps)
          <|> do reserved "refine"; n <- name
                 i <- get
                 return $ Refine n []
          <|> do reserved "mrefine"; n <- name
                 i <- get
                 return $ MatchRefine n
          <|> do reserved "rewrite"; t <- expr syn;
                 i <- get
                 return $ Rewrite (desugar syn i t)
          <|> do reserved "equiv"; t <- expr syn;
                 i <- get
                 return $ Equiv (desugar syn i t)
          <|> try (do reserved "let"; n <- name; lchar ':';
                      ty <- expr' syn; lchar '='; t <- expr syn;
                      i <- get
                      return $ LetTacTy n (desugar syn i ty) (desugar syn i t))
          <|> try (do reserved "let"; n <- name; lchar '=';
                      t <- expr syn;
                      i <- get
                      return $ LetTac n (desugar syn i t))
          <|> do reserved "focus"; n <- name
                 return $ Focus n
          <|> do reserved "exact"; t <- expr syn;
                 i <- get
                 return $ Exact (desugar syn i t)
          <|> do reserved "applyTactic"; t <- expr syn;
                 i <- get
                 return $ ApplyTactic (desugar syn i t)
          <|> do reserved "reflect"; t <- expr syn;
                 i <- get
                 return $ Reflect (desugar syn i t)
          <|> do reserved "fill"; t <- expr syn;
                 i <- get
                 return $ Fill (desugar syn i t)
          <|> do reserved "try"; t <- tactic syn;
                 lchar '|';
                 t1 <- tactic syn
                 return $ Try t t1
          <|> do lchar '{'
                 t <- tactic syn;
                 lchar ';';
                 ts <- sepBy1 (tactic syn) (lchar ';')
                 lchar '}'
                 return $ TSeq t (mergeSeq ts)
          <|> do reserved "compute"; return Compute
          <|> do reserved "trivial"; return Trivial
          <|> do reserved "solve"; return Solve
          <|> do reserved "attack"; return Attack
          <|> do reserved "state"; return ProofState
          <|> do reserved "term"; return ProofTerm
          <|> do reserved "undo"; return Undo
          <|> do reserved "qed"; return Qed
          <|> do reserved "abandon"; return Abandon
          <|> do lchar ':'; reserved "q"; return Abandon
          <?> "tactic"
  where
    imp :: IdrisParser Bool
    imp = do lchar '?'; return False
      <|> do lchar '_'; return True
    mergeSeq :: [PTactic] -> PTactic
    mergeSeq [t]    = t
    mergeSeq (t:ts) = TSeq t (mergeSeq ts)

{- | Parses a tactic as a whole -}
fullTactic :: SyntaxInfo -> IdrisParser PTactic
fullTactic syn = do t <- tactic syn
                    eof
                    return t

{- * Loading and parsing -}
{- | Parses an expression from input -}
parseExpr :: IState -> String -> Result PTerm
parseExpr st = parseString (evalStateT (fullExpr defaultSyntax) st) (Directed (UTF8.fromString "(input)") 0 0 0 0)

{- | Parses a tactic from input -}
parseTactic :: IState -> String -> Result PTactic
parseTactic st = parseString (evalStateT (fullTactic defaultSyntax) st) (Directed (UTF8.fromString "(input)") 0 0 0 0)

-- | Parse module header and imports
parseImports :: FilePath -> String -> Idris ([String], [String], Maybe Delta)
parseImports fname input
    = do i <- getIState
         case parseString (evalStateT imports i) (Directed (UTF8.fromString fname) 0 0 0 0) input of
              Failure err    -> fail (show err)
              Success (x, i) -> do -- Discard state updates (there should be
                                   -- none anyway)
                                   return x
  where imports :: IdrisParser (([String], [String], Maybe Delta), IState)
        imports = do whiteSpace
                     mname <- moduleHeader
                     ps    <- many import_
                     mrk   <- mark
                     isEof <- lookAheadMatches eof
                     let mrk' = if isEof
                                   then Nothing
                                   else Just mrk
                     i     <- get
                     return ((mname, ps, mrk'), i)


-- | A program is a list of declarations, possibly with associated
-- documentation strings.
parseProg :: SyntaxInfo -> FilePath -> String -> Maybe Delta ->
             Idris [PDecl]
parseProg syn fname input mrk
    = do i <- getIState
         case parseString (evalStateT mainProg i) (Directed (UTF8.fromString fname) 0 0 0 0) input of
            Failure doc     -> do iputStrLn (show doc)
                                  -- FIXME: Get error location from trifecta
                                  --let errl = sourceLine (errorPos err)
                                  i <- getIState
                                  putIState (i { errLine = Just 0 }) -- Just errl })
                                  return []
            Success (x, i)  -> do putIState i
                                  return $ collect x
  where mainProg :: IdrisParser ([PDecl], IState)
        mainProg = case mrk of
                        Nothing -> do i <- get; return ([], i)
                        Just mrk -> do
                          release mrk
                          ds <- prog syn
                          i' <- get
                          return (ds, i')

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

{- | Load idris module -}
loadModule :: FilePath -> Idris String
loadModule f
   = idrisCatch (do i <- getIState
                    let file = takeWhile (/= ' ') f
                    ibcsd <- valIBCSubDir i
                    ids <- allImportDirs
                    fp <- liftIO $ findImport ids ibcsd file
                    if file `elem` imported i
                       then iLOG $ "Already read " ++ file
                       else do putIState (i { imported = file : imported i })
                               case fp of
                                   IDR fn  -> loadSource False fn
                                   LIDR fn -> loadSource True  fn
                                   IBC fn src ->
                                     idrisCatch (loadIBC fn)
                                                (\c -> do iLOG $ fn ++ " failed " ++ show c
                                                          case src of
                                                            IDR sfn -> loadSource False sfn
                                                            LIDR sfn -> loadSource True sfn)
                    let (dir, fh) = splitFileName file
                    return (dropExtension fh))
                (\e -> do let msg = show e
                          setErrLine (getErrLine msg)
                          iputStrLn msg
                          return "")

{- | Load idris code from file -}
loadFromIFile :: IFileType -> Idris ()
loadFromIFile i@(IBC fn src)
   = do iLOG $ "Skipping " ++ getSrcFile i
        idrisCatch (loadIBC fn)
                (\c -> do fail $ fn ++ " failed " ++ show c)
  where
    getSrcFile (IDR fn) = fn
    getSrcFile (LIDR fn) = fn
    getSrcFile (IBC f src) = getSrcFile src

loadFromIFile (IDR fn) = loadSource' False fn
loadFromIFile (LIDR fn) = loadSource' True fn

{-| Load idris source code and show error if something wrong happens -}
loadSource' :: Bool -> FilePath -> Idris ()
loadSource' lidr r
   = idrisCatch (loadSource lidr r)
                (\e -> do let msg = show e
                          setErrLine (getErrLine msg)
                          iputStrLn msg)

{- | Load Idris source code-}
loadSource :: Bool -> FilePath -> Idris ()
loadSource lidr f
             = do iLOG ("Reading " ++ f)
                  i <- getIState
                  let def_total = default_total i
                  file_in <- liftIO $ readFile f
                  file <- if lidr then tclift $ unlit f file_in else return file_in
                  (mname, modules, pos) <- parseImports f file
                  i <- getIState
                  putIState (i { default_access = Hidden })
                  clearIBC -- start a new .ibc file
                  mapM_ (addIBC . IBCImport) modules
                  ds' <- parseProg (defaultSyntax {syn_namespace = reverse mname })
                                   f file pos
                  unless (null ds') $ do
                    let ds = namespaces mname ds'
                    logLvl 3 (dumpDecls ds)
                    i <- getIState
                    logLvl 10 (show (toAlist (idris_implicits i)))
                    logLvl 3 (show (idris_infixes i))
                    -- Now add all the declarations to the context
                    v <- verbose
                    when v $ iputStrLn $ "Type checking " ++ f
                    -- we totality check after every Mutual block, so if
                    -- anything is a single definition, wrap it in a
                    -- mutual block on its own
                    elabDecls toplevel (map toMutual ds)
                    i <- getIState
                    -- simplify every definition do give the totality checker
                    -- a better chance
                    mapM_ (\n -> do logLvl 5 $ "Simplifying " ++ show n
                                    updateContext (simplifyCasedef n))
                             (map snd (idris_totcheck i))
                    -- build size change graph from simplified definitions
                    iLOG "Totality checking"
                    i <- getIState
                    mapM_ buildSCG (idris_totcheck i)
                    mapM_ checkDeclTotality (idris_totcheck i)
                    iLOG ("Finished " ++ f)
                    ibcsd <- valIBCSubDir i
                    iLOG "Universe checking"
                    iucheck
                    let ibc = ibcPathNoFallback ibcsd f
                    i <- getIState
                    addHides (hide_list i)
                    ok <- noErrors
                    when ok $
                      idrisCatch (do writeIBC f ibc; clearIBC)
                                 (\c -> return ()) -- failure is harmless
                    i <- getIState
                    putIState (i { default_total = def_total,
                                   hide_list = [] })
                    return ()
                  return ()
  where
    namespaces :: [String] -> [PDecl] -> [PDecl]
    namespaces []     ds = ds
    namespaces (x:xs) ds = [PNamespace x (namespaces xs ds)]

    toMutual :: PDecl -> PDecl
    toMutual m@(PMutual _ d) = m
    toMutual x = let r = PMutual (FC "single mutual" 0) [x] in
                 case x of
                   PClauses _ _ _ _ -> r
                   PClass _ _ _ _ _ _ _ -> r
                   PInstance _ _ _ _ _ _ _ _ -> r
                   _ -> x

{- | Adds names to hide list -}
addHides :: [(Name, Maybe Accessibility)] -> Idris ()
addHides xs = do i <- getIState
                 let defh = default_access i
                 let (hs, as) = partition isNothing xs
                 unless (null as) $
                   mapM_ doHide
                     (map (\ (n, _) -> (n, defh)) hs ++
                       map (\ (n, Just a) -> (n, a)) as)
  where isNothing (_, Nothing) = True
        isNothing _            = False

        doHide (n, a) = do setAccessibility n a
                           addIBC (IBCAccess n a)

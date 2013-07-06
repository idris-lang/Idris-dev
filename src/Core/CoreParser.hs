{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Core.CoreParser(parseTerm, parseFile, parseDef, pTerm, iName, 
                       idrisLexer, maybeWithNS, pDocComment, opChars) where

import Core.TT

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Prim
import Text.ParserCombinators.Parsec.Char
import Text.ParserCombinators.Parsec.Combinator
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Control.Monad.State
import Control.Monad.Identity
import Data.Char
import Data.List
import Debug.Trace

type TokenParser a = PTok.TokenParser a

idrisDef = haskellDef { 
              opStart = iOpStart,
              opLetter = iOpLetter,
              identLetter = identLetter haskellDef <|> lchar '.',
              reservedOpNames 
                 = [":", "..", "=", "\\", "|", "<-", "->", "=>", "**"],
              reservedNames 
                 = ["let", "in", "data", "codata", "record", "Type", 
                    "do", "dsl", "import", "impossible", 
                    "case", "of", "total", "partial", "mutual",
                    "infix", "infixl", "infixr", "rewrite",
                    "where", "with", "syntax", "proof", "postulate",
                    "using", "namespace", "class", "instance",
                    "public", "private", "abstract", "implicit",
                    "Int", "Integer", "Float", "Char", "String", "Ptr",
                    "Bits8", "Bits16", "Bits32", "Bits64",
                    "Bits8x16", "Bits16x8", "Bits32x4", "Bits64x2"]
           } 

-- | The characters allowed in operator names
opChars = ":!#$%&*+./<=>?@\\^|-~"

iOpStart = oneOf opChars
iOpLetter = oneOf opChars
--          <|> letter

idrisLexer :: TokenParser a
idrisLexer  = idrisMakeTokenParser idrisDef 

lexer = idrisLexer

-- Taken from Parsec source code
lexWS = do i <- getInput
           skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")
  where

    simpleSpace = skipMany1 (satisfy isSpace)
    oneLineComment =
      try (void $ string "--\n") <|>
      do try (do string "--"
                 satisfy (\x -> x /= '|' && x /= '^'))
         skipMany (satisfy (/= '\n'))
    multiLineComment =
      try (void $ string "{--}") <|>
      do try (do string "{-"
                 satisfy (\x -> x /= '|' && x /= '^'))
         inCommentMulti

    inCommentMulti
        =   do{ try (string "-}") ; return () }
        <|> do{ multiLineComment                     ; inCommentMulti }
        <|> do{ skipMany1 (noneOf startEnd)          ; inCommentMulti }
        <|> do{ oneOf startEnd                       ; inCommentMulti }
        <?> "end of comment"
        where
          startEnd   = "-}{"

whiteSpace= PTok.whiteSpace lexer
lexeme    = PTok.lexeme lexer
symbol    = PTok.symbol lexer
natural   = PTok.natural lexer
parens    = PTok.parens lexer
semi      = PTok.semi lexer
comma     = PTok.comma lexer
identifier= PTok.identifier lexer
reserved  = PTok.reserved lexer
operator  = PTok.operator lexer
reservedOp= PTok.reservedOp lexer
strlit    = PTok.stringLiteral lexer
lchar = lexeme.char

type CParser a = GenParser Char a

parseFile = runParser pTestFile () "(input)"
parseDef = runParser pDef () "(input)"
parseTerm = runParser pTerm () "(input)"

pTestFile :: CParser a RProgram
pTestFile = do p <- many1 pDef ; eof
               return p

iName :: [String] -> CParser a Name
iName bad = maybeWithNS identifier False bad

-- Enhances a given parser to accept an optional namespace.  All possible
-- namespace prefixes are tried in ascending / descending order, and
-- identifiers of a given list fail.
maybeWithNS :: CParser a String -> Bool -> [String] -> CParser a Name
maybeWithNS parser ascend bad = do
  i <- option "" (lookAhead identifier)
  when (i `elem` bad) $ fail "Reserved identifier"
  let transf = if ascend then id else reverse
  (x, xs) <- choice $ transf (parserNoNS : parsersNS i)
  return $ mkName (x, xs)
  where
    parserNoNS = do x <- parser; return (x, "")
    parserNS ns = do xs <- string ns; lchar '.'; x <- parser; return (x, xs)
    parsersNS i = [try (parserNS ns) | ns <- (initsEndAt (=='.') i)]

-- List of all initial segments in ascending order of a list.  Every such
-- initial segment ends right before an element satisfying the given
-- condition.
initsEndAt :: (a -> Bool) -> [a] -> [[a]]
initsEndAt p [] = []
initsEndAt p (x:xs) | p x = [] : x_inits_xs
                    | otherwise = x_inits_xs
  where x_inits_xs = [x : cs | cs <- initsEndAt p xs]

-- Create a `Name' from a pair of strings representing a base name and its
-- namespace.
mkName :: (String, String) -> Name
mkName (n, "") = UN n 
mkName (n, ns) = NS (UN n) (reverse (parseNS ns))
  where parseNS x = case span (/= '.') x of
                      (x, "")    -> [x]
                      (x, '.':y) -> x : parseNS y

pDocComment :: Char -> CParser a String
pDocComment c 
   = try (do string ("--")
             char c
             skipMany simpleSpace
             i <- getInput
             let (doc, rest) = span (/='\n') i
             setInput rest
             whiteSpace
             return doc)
 <|> try (do string ("{-")
             char c
             skipMany simpleSpace
             i <- getInput
             -- read to '-}'
             let (doc, rest) = spanComment "" i
             setInput rest
             whiteSpace
             return doc)
  where spanComment acc ('-':'}':xs) = (reverse acc, xs)
        spanComment acc (x:xs) = spanComment (x : acc) xs
        spanComment acc [] = (acc, [])
        simpleSpace = skipMany1 (satisfy isSpace)

pDef :: CParser a (Name, RDef)
pDef = try (do x <- iName []; lchar ':'; ty <- pTerm
               lchar '='
               tm <- pTerm
               lchar ';'
               return (x, RFunction (RawFun ty tm)))
       <|> do x <- iName []; lchar ':'; ty <- pTerm; lchar ';'
              return (x, RConst ty)
       <|> do (x, d) <- pData; lchar ';'
              return (x, RData d)

app :: CParser a (Raw -> Raw -> Raw)
app = do whiteSpace ; return RApp

arrow :: CParser a (Raw -> Raw -> Raw)
arrow = do symbol "->" ; return $ \s t -> RBind (MN 0 "X") (Pi s) t

pTerm :: CParser a Raw
pTerm = try (do chainl1 pNoApp app)
           <|> pNoApp

pNoApp :: CParser a Raw
pNoApp = try (chainr1 pExp arrow)
           <|> pExp
pExp :: CParser a Raw
pExp = do lchar '\\'; x <- iName []; lchar ':'; ty <- pTerm
          symbol "=>";
          sc <- pTerm
          return (RBind x (Lam ty) sc)
       <|> try (do lchar '?'; x <- iName []; lchar ':'; ty <- pTerm
                   lchar '.';
                   sc <- pTerm
                   return (RBind x (Hole ty) sc))
       <|> try (do lchar '('; 
                   x <- iName []; lchar ':'; ty <- pTerm
                   lchar ')';
                   symbol "->";
                   sc <- pTerm
                   return (RBind x (Pi ty) sc))
       <|> try (do lchar '('; 
                   t <- pTerm
                   lchar ')'
                   return t)
       <|> try (do symbol "??";
                   x <- iName []; lchar ':'; ty <- pTerm
                   lchar '=';
                   val <- pTerm
                   sc <- pTerm
                   return (RBind x (Guess ty val) sc))
       <|> try (do reserved "let"; 
                   x <- iName []; lchar ':'; ty <- pTerm
                   lchar '=';
                   val <- pTerm
                   reserved "in";
                   sc <- pTerm
                   return (RBind x (Let ty val) sc))
       <|> try (do lchar '_'; 
                   x <- iName []; lchar ':'; ty <- pTerm
                   lchar '.';
                   sc <- pTerm
                   return (RBind x (PVar ty) sc))
       <|> try (do reserved "Type"
                   return RType)
       <|> try (do x <- iName []
                   return (Var x))

pData :: CParser a (Name, RawDatatype)
pData = do reserved "data"; x <- iName []; lchar ':'; ty <- pTerm; reserved "where"
           cs <- many pConstructor
           return (x, RDatatype x ty cs)

pConstructor :: CParser a (Name, Raw)
pConstructor = do lchar '|'
                  c <- iName []; lchar ':'; ty <- pTerm
                  return (c, ty)

------ borrowed from Parsec 
-- (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007

idrisMakeTokenParser languageDef
    = PTok.TokenParser{ 
                   PTok.identifier = identifier
                 , PTok.reserved = reserved
                 , PTok.operator = operator
                 , PTok.reservedOp = reservedOp

                 , PTok.charLiteral = charLiteral
                 , PTok.stringLiteral = stringLiteral
                 , PTok.natural = natural
                 , PTok.integer = integer
                 , PTok.float = float
                 , PTok.naturalOrFloat = naturalOrFloat
                 , PTok.decimal = decimal
                 , PTok.hexadecimal = hexadecimal
                 , PTok.octal = octal

                 , PTok.symbol = symbol
                 , PTok.lexeme = lexeme
                 , PTok.whiteSpace = lexWS

                 , PTok.parens = parens
                 , PTok.braces = braces
                 , PTok.angles = angles
                 , PTok.brackets = brackets
                 , PTok.squares = brackets
                 , PTok.semi = semi
                 , PTok.comma = comma
                 , PTok.colon = colon
                 , PTok.dot = dot
                 , PTok.semiSep = semiSep
                 , PTok.semiSep1 = semiSep1
                 , PTok.commaSep = commaSep
                 , PTok.commaSep1 = commaSep1
                 }
    where

    -----------------------------------------------------------
    -- Bracketing
    -----------------------------------------------------------
    parens p        = between (symbol "(") (symbol ")") p
    braces p        = between (symbol "{") (symbol "}") p
    angles p        = between (symbol "<") (symbol ">") p
    brackets p      = between (symbol "[") (symbol "]") p

    semi            = symbol ";"
    comma           = symbol ","
    dot             = symbol "."
    colon           = symbol ":"

    commaSep p      = sepBy p comma
    semiSep p       = sepBy p semi

    commaSep1 p     = sepBy1 p comma
    semiSep1 p      = sepBy1 p semi


    -----------------------------------------------------------
    -- Chars & Strings
    -----------------------------------------------------------
    charLiteral     = lexeme (between (char '\'')
                                      (char '\'' <?> "end of character")
                                      characterChar )
                    <?> "character"

    characterChar   = charLetter <|> charEscape
                    <?> "literal character"

    charEscape      = do{ char '\\'; escapeCode }
    charLetter      = satisfy (\c -> (c /= '\'') && (c /= '\\') && (c > '\026'))



    stringLiteral   = lexeme (
                      do{ str <- between (char '"')
                                         (char '"' <?> "end of string")
                                         (many stringChar)
                        ; return (foldr (maybe id (:)) "" str)
                        }
                      <?> "literal string")

    stringChar      =   do{ c <- stringLetter; return (Just c) }
                    <|> stringEscape
                    <?> "string character"

    stringLetter    = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

    stringEscape    = do{ char '\\'
                        ;     do{ escapeGap  ; return Nothing }
                          <|> do{ escapeEmpty; return Nothing }
                          <|> do{ esc <- escapeCode; return (Just esc) }
                        }

    escapeEmpty     = char '&'
    escapeGap       = do{ many1 space
                        ; char '\\' <?> "end of string gap"
                        }



    -- escape codes
    escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                    <?> "escape code"

    charControl     = do{ char '^'
                        ; code <- upper
                        ; return (toEnum (fromEnum code - fromEnum 'A'))
                        }

    charNum         = do{ code <- decimal
                                  <|> do{ char 'o'; number 8 octDigit }
                                  <|> do{ char 'x'; number 16 hexDigit }
                        ; return (toEnum (fromInteger code))
                        }

    charEsc         = choice (map parseEsc escMap)
                    where
                      parseEsc (c,code)     = do{ char c; return code }

    charAscii       = choice (map parseAscii asciiMap)
                    where
                      parseAscii (asc,code) = try (do{ string asc; return code })


    -- escape code tables
    escMap          = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
    asciiMap        = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2)

    ascii2codes     = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                       "FS","GS","RS","US","SP"]
    ascii3codes     = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                       "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                       "CAN","SUB","ESC","DEL"]

    ascii2          = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
                       '\EM','\FS','\GS','\RS','\US','\SP']
    ascii3          = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
                       '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
                       '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']


    -----------------------------------------------------------
    -- Numbers
    -----------------------------------------------------------
    naturalOrFloat  = lexeme (natFloat) <?> "number"

    float           = lexeme floating   <?> "float"
    integer         = lexeme int        <?> "integer"
    natural         = lexeme nat        <?> "natural"


    -- floats
    floating        = do{ n <- decimal
                        ; fractExponent n
                        }


    natFloat        = do{ char '0'
                        ; zeroNumFloat
                        }
                      <|> decimalFloat

    zeroNumFloat    =  do{ n <- hexadecimal <|> octal
                         ; return (Left n)
                         }
                    <|> decimalFloat
                    <|> fractFloat 0
                    <|> return (Left 0)

    decimalFloat    = do{ n <- decimal
                        ; option (Left n)
                                 (fractFloat n)
                        }

    fractFloat n    = do{ f <- fractExponent n
                        ; return (Right f)
                        }

    fractExponent n = do{ fract <- fraction
                        ; expo  <- option 1.0 exponent'
                        ; return ((fromInteger n + fract)*expo)
                        }
                    <|>
                      do{ expo <- exponent'
                        ; return ((fromInteger n)*expo)
                        }

    fraction        = do{ char '.'
                        ; digits <- many1 digit <?> "fraction"
                        ; return (foldr op 0.0 digits)
                        }
                      <?> "fraction"
                    where
                      op d f    = (f + fromIntegral (digitToInt d))/10.0

    exponent'       = do{ oneOf "eE"
                        ; f <- sign
                        ; e <- decimal <?> "exponent"
                        ; return (power (f e))
                        }
                      <?> "exponent"
                    where
                       power e  | e < 0      = 1.0/power(-e)
                                | otherwise  = fromInteger (10^e)


    -- integers and naturals
    int             = do{ f <- lexeme sign
                        ; n <- nat
                        ; return (f n)
                        }

    sign            =   (char '-' >> return negate)
                    <|> (char '+' >> return id)
                    <|> return id

    nat             = zeroNumber <|> decimal

    zeroNumber      = do{ char '0'
                        ; hexadecimal <|> octal <|> decimal <|> return 0
                        }
                      <?> ""

    decimal         = number 10 digit
    hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
    octal           = do{ oneOf "oO"; number 8 octDigit  }

    number base baseDigit
        = do{ digits <- many1 baseDigit
            ; let n = foldl' (\x d -> base*x + toInteger (digitToInt d)) 0 digits
            ; seq n (return n)
            }

    -----------------------------------------------------------
    -- Operators & reserved ops
    -----------------------------------------------------------
    reservedOp name =
        lexeme $ try $
        do{ string name
          ; notFollowedBy (opLetter languageDef) <?> ("end of " ++ show name)
          }

    operator =
        lexeme $ try $
        do{ name <- oper
          ; if (isReservedOp name)
             then unexpected ("reserved operator " ++ show name)
             else return name
          }

    oper =
        do{ c <- (opStart languageDef)
          ; cs <- many (opLetter languageDef)
          ; return (c:cs)
          }
        <?> "operator"

    isReservedOp name =
        isReserved (sort (reservedOpNames languageDef)) name


    -----------------------------------------------------------
    -- Identifiers & Reserved words
    -----------------------------------------------------------
    reserved name =
        lexeme $ try $
        do{ caseString name
          ; notFollowedBy (identLetter languageDef) <?> ("end of " ++ show name)
          }

    caseString name
        | caseSensitive languageDef  = string name
        | otherwise               = do{ walk name; return name }
        where
          walk []     = return ()
          walk (c:cs) = do{ caseChar c <?> msg; walk cs }

          caseChar c  | isAlpha c  = char (toLower c) <|> char (toUpper c)
                      | otherwise  = char c

          msg         = show name


    identifier =
        lexeme $ try $
        do{ name <- ident
          ; if (isReservedName name)
             then unexpected ("reserved word " ++ show name)
             else return name
          }


    ident
        = do{ c <- identStart languageDef
            ; cs <- many (identLetter languageDef)
            ; return (c:cs)
            }
        <?> "identifier"

    isReservedName name
        = isReserved theReservedNames caseName
        where
          caseName      | caseSensitive languageDef  = name
                        | otherwise               = map toLower name


    isReserved names name
        = scan names
        where
          scan []       = False
          scan (r:rs)   = case (compare r name) of
                            LT  -> scan rs
                            EQ  -> True
                            GT  -> False

    theReservedNames
        | caseSensitive languageDef  = sortedNames
        | otherwise               = map (map toLower) sortedNames
        where
          sortedNames   = sort (reservedNames languageDef)



    -----------------------------------------------------------
    -- White space & symbols
    -----------------------------------------------------------
    symbol name
        = lexeme (string name)

    lexeme p
        = do{ x <- p; whiteSpace; return x  }

    --whiteSpace
    whiteSpace = lexWS

{-
  Simple monadic parser module, based heavily on that by
  Graham Hutton.
-}

module SimpleParser

import Prelude
import Prelude.Monad
import Prelude.Applicative
import Prelude.List
import Builtins

%access public


--------------------------------------------------------------------------------
-- The monad of parsers
--------------------------------------------------------------------------------

data Parser a = P (String -> Either String (a, String))

parse : Parser a -> String -> Either String (a, String)
parse (P p) inp = p inp

instance Functor Parser where
  map f p = P (\inp => case parse p inp of
                          Left err        => Left err
                          Right (v, rest) => Right ((f v), rest))

instance Applicative Parser where
  pure v  = P (\inp => Right (v, inp))
  a <$> b = P (\inp => do (f, rest) <- parse a inp
                          (x, rest') <- parse b rest
                          pure ((f x), rest'))

instance Monad Parser where
  p >>= f = P (\inp => case parse p inp of
                         Left err       => Left err
                         Right (v,rest) => parse (f v) rest)

instance Alternative Parser where
  empty   = P (const (Left "empty"))
  p <|> q = P (\inp => case parse p inp of
                         Left msg      => parse q inp
                         Right (v,out) => Right (v,out))


--------------------------------------------------------------------------------
-- Basic parsers
--------------------------------------------------------------------------------

failure : String -> Parser a
failure msg = P (\inp => Left msg)

item : Parser Char
item = P (\inp => case unpack inp of
                    []      => Left "Error! Parsing empty list."
                    (x::xs) => Right (x, pack xs))


--------------------------------------------------------------------------------
-- Derived primitives
--------------------------------------------------------------------------------

sat : (Char -> Bool) -> Parser Char
sat p = do x <- item
           guard (p x)
           pure x

oneof : List Char -> Parser Char
oneof xs = sat (\x => elem x xs)

digit : Parser Char
digit = sat isDigit

lower : Parser Char
lower = sat isLower

upper : Parser Char
upper = sat isUpper

letter : Parser Char
letter = sat isAlpha

alphanum : Parser Char
alphanum = sat isAlphaNum

char : Char -> Parser Char
char x = sat (== x)

string : String -> Parser String
string s = map pack (traverse char (unpack s))

many1 : Parser a -> Parser (List a)
many : Parser a -> Parser (List a)

many1 p = [| p :: many p |]

many p = lazy (many1 p) <|> pure []

bool : Parser Bool
bool = parseTrue <|> parseFalse
  where parseTrue : Parser Bool
        parseTrue  = do oneof ['T', 't']
                        string "rue"
                        pure True
        parseFalse = do oneof ['F', 'f']
                        string "alse"
                        pure False

ident : Parser String
ident = map pack [| letter :: many1 alphanum |]

nat : Parser Int
nat = do xs <- many digit
         pure (cast (cast xs))

int : Parser Int
int = neg <|> nat
  where neg : Parser Int
        neg = do char '-'
                 n <- nat
                 pure (-n)

space : Parser ()
space = do many (sat isSpace)
           pure ()


--------------------------------------------------------------------------------
-- Ignoring spacing
--------------------------------------------------------------------------------

token : Parser a -> Parser a
token p = space $> p <$ space

identifier : Parser String
identifier = token ident

natural : Parser Int
natural = token nat

integer : Parser Int
integer = token int

symbol : String -> Parser String
symbol xs = token (string xs)

strToken : Parser String
strToken = map pack (token (many1 alphanum))

--------------------------------------------------------------------------------
-- combinators
--------------------------------------------------------------------------------

optional : Parser a -> Parser (Maybe a)
optional p = map Just p <|> pure Nothing

sepBy1 : Parser a -> Parser b -> Parser (List a)
sepBy1 p s = [| p :: many (s $> p) |]

sepBy : Parser a -> Parser b -> Parser (List a)
sepBy p s = sepBy1 p s <|> pure Nil

manyTil : Parser a -> Parser b -> Parser (List a)
manyTil p e = (e $> pure Nil) <|> lazy [| p :: manyTil p e |] <|> pure Nil

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

expr   : Parser Int
factor : Parser Int
term   : Parser Int

expr = do t <- term
          map (t+) (symbol "+" $> expr) <|> pure t

factor = (symbol "(" $> expr <$ symbol ")") <|> natural

term = do f <- factor
          map (f*) (symbol "*" $> term) <|> pure f

eval : String -> Maybe Int
eval xs = case (parse expr xs) of
            Right (n,rest) => if rest == "" then Just n else Nothing
            Left msg       => Nothing

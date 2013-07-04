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

infixr 5 |||

{-
The monad of parsers
--------------------
-}

data Parser a                 =  P (String -> Either String (a, String))

parse                         : Parser a -> String -> Either String (a, String)
parse (P p) inp               =  p inp

instance Functor Parser where 
    -- fmap : (a -> b) -> f a -> f b
    -- fmap : (a -> b) -> Parser a -> Parser b
    -- Given a function (a -> b), and a parser a, make a parser b
    fmap f p = P (\inp => case parse p inp of
                                  (Left err) => Left err
                                  -- Apply f to the v that we got from parsing
                                  (Right (v, rest)) => Right ((f v), rest))
    

instance Applicative Parser where 
    pure v      = P (\inp => Right (v, inp)) 
    -- Parse to get the function, then parse to get the first argument
    a <$> b = P (\inp => do (f, rest) <- parse a inp
                            (x, rest') <- parse b rest
                            pure ((f x), rest'))

instance Monad Parser where
--    pure v                  =  P (\inp => Right (v,inp))
    -- m a -> (a -> m b) -> m b
    p >>= f                   =  P (\inp => case parse p inp of
                                               (Left err)       => Left err
                                               (Right (v,rest)) => parse (f v) rest)
                                               
--mplus : Monad m => m a -> m a -> m a
mplus : Parser a -> Parser a -> Parser a
mplus p q                  =  P (\inp => case parse p inp of
                                       Left msg      => parse q inp
                                       Right (v,out) => Right(v,out))


{-
Basic parsers
-------------
-}

failure                       : String -> Parser a
failure msg                   = P (\inp => Left msg)

item                          : Parser Char
item                          =  P (\inp => case unpack inp of
                                               []      => Left "Error! Parsing empty list."
                                               (x::xs) => Right (x, pack xs))
                                               

{-
Choice
--------
---}

(|||)                         : Parser a -> Parser a -> Parser a
p ||| q                       =  p `mplus` q


--{-
--Derived primitives
---}

sat                           : (Char -> Bool) -> Parser Char
sat p                         = item >>= (\x => if p x then pure x else failure "failed")                 
                                    
oneof                         : List Char -> Parser Char
oneof xs                      = sat (\x => elem x xs) 

digit                         : Parser Char
digit                         =  sat isDigit

lower                         : Parser Char
lower                         =  sat isLower

upper                         : Parser Char
upper                         =  sat isUpper

letter                        : Parser Char
letter                        =  sat isAlpha

alphanum                      : Parser Char
alphanum                      =  sat isAlphaNum

char                          : Char -> Parser Char
char x                        =  sat (== x)

helper                        : List Char -> Parser (List Char)
string                        : String -> Parser String
string s                      = do result <- helper (unpack s)
                                   pure (pack result)
                                  
helper []                     =  pure Prelude.List.Nil
helper (x::xs)                =  do char x
                                    string (cast xs) 
                                    pure (x :: xs)

many                          : Parser a -> Parser (List a)
many1                         : Parser a -> Parser (List a)
many1 p                       = do v <- p
                                   vs <- many p
                                   pure $ Prelude.List.(::) v vs


bool : Parser Bool
bool = parseTrue ||| parseFalse
  where parseTrue : Parser Bool
        parseTrue  = do oneof ['T', 't']
                        string "rue"
                        pure True
        parseFalse = do oneof ['F', 'f']
                        string "alse"
                        pure False



                          
many p                        =  many1 p `mplus` pure Prelude.List.Nil



ident                         : Parser String
ident                         =  do x  <- letter
                                    xs <- many1 alphanum
                                    pure (pack(x::xs))

nat                           : Parser Int
nat                           =  do xs <- many digit
                                    pure (cast (cast xs))


int                           : Parser Int
int                           =  neg ||| nat
  where neg : Parser Int
        neg = do char '-'
                 n <- nat
                 pure (-n)

space                         : Parser ()
space                         =  do many (sat isSpace)
                                    pure ()
--{-
--Ignoring spacing
---}

token                         : Parser a -> Parser a
token p                       =  do space
                                    v <- p
                                    space
                                    pure v

identifier                    : Parser String
identifier                    =  token ident

natural                       : Parser Int
natural                       =  token nat

integer                       : Parser Int
integer                       =  token int

symbol                        : String -> Parser String
symbol xs                     =  token (string xs)

strToken : Parser String
strToken = fmap pack (token (many1 alphanum))

--apply                           : Parser a -> String -> List (a,String)
--apply p                     = parse (space >>= (\_ => p))

--{-
-- Expressions
---}

factor                        : Parser Int
term                          : Parser Int
expr                          : Parser Int
expr                          =  do t <- term
                                    do symbol "+"               
                                       e <- expr
                                       pure $ t + e
                                  `mplus` pure t  
                                                     

factor                        =  do symbol "("
                                    do e <- expr
                                       symbol ")"
                                       pure e
                                  `mplus` natural

term                          =  do f <- factor
                                    do symbol "*"
                                       t <- term
                                       pure (f * t)
                                  `mplus` pure f



eval                          : String -> Maybe Int
eval xs                       =  case (parse expr xs) of
                                     Right (n,rest) => if rest == "" then Just n else Nothing
                                     Left msg  => Nothing

module Parsing

import prelude
import builtins

infixr 5 |||

{-
The monad of parsers
--------------------
-}

data Parser a              =  P (String -> Either String (a,String))

parse                         : Parser a -> String ->Either String (a,String)
parse (P p) inp               =  p inp

instance Monad Parser where
   return v                   =  P (\inp => Right (v,inp))
   p >>= f                    =  P (\inp => case parse p inp of
                                               Left err  	  => Left err
                                               Right (v,rest) => parse (f v) rest)
                                               

instance MonadPlus Parser where
   mzero                      =  P (\inp => Left "Parse Error")
   mplus p q                  =  P (\inp => case parse p inp of
                                               Left msg 	 => parse q inp
                                               Right (v,out) => Right(v,out))



{-
Basic parsers
-------------
-}

failure                       : String -> Parser a
failure msg                   = P (\inp => Left msg)

item                          : Parser Char
item 		               	  =  P (\inp => case unpack inp of
                                               []	   => Left "Error! Parsing empty list."
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
sat p 	                      = item >>= (\x => if p x then return x else failure "failed")					
									
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

string                        : String -> Parser String
helper                        : List Char -> Parser (List Char)
string s                      = do result <- helper (unpack s)
                                   return (pack result)
                                  
helper []                     =  return []
helper (x::xs)                =  do char x
                                    string (cast xs) 
                                    return (x :: xs)

many1                         : Parser a -> Parser (List a)
many                          : Parser a -> Parser (List a)
many1 p                       =  do v  <- p
                                    vs <- many p
                                    return (v::vs)

                          
many p                        =  many1 p `mplus` return []



ident                         : Parser String
ident                         =  do x  <- letter
                                    xs <- many1 alphanum
                                    return (pack(x::xs))


nat                           : Parser Int
nat                           =  do xs <- many digit
                                    return (cast (cast xs))


int                           : Parser Int
int                           =  do char '-'
                                    n <- nat
                                    return (-n)
                                  `mplus` nat

space                         : Parser ()
space                         =  do many (sat isSpace)
                                    return ()
--{-
--Ignoring spacing
---}

token                         : Parser a -> Parser a
token p                       =  do space
                                    v <- p
                                    space
                                    return v

identifier                    : Parser String
identifier                    =  token ident

natural                       : Parser Int
natural                       =  token nat

integer                       : Parser Int
integer                       =  token int

symbol                        : String -> Parser String
symbol xs                     =  token (string xs)

--apply 						  : Parser a -> String -> List (a,String)
--apply p 					  = parse (space >>= (\_ => p))

--{-
-- Expressions
---}

factor                        : Parser Int
term                          : Parser Int
expr                          : Parser Int
expr                          =  do t <- term
                                    do symbol "+"               
                                       e <- expr
	                                   Right (t+e)
	                               |||  Right t	
                                      				 

factor                        =  do symbol "("
                                    e <- expr
                                    symbol ")"
                                    return e
                                  ||| natural

term                          =  do f <- factor
                                    symbol "*"
                                    t <- term
                                    return (f * t)
                                  ||| return f



eval                          : String -> Maybe Int
eval xs                       =  case (parse expr xs) of
                                     Right (n,rest) => if rest == "" then Just n else Nothing
                                     Left msg  => Nothing
                                    
                                            
									   

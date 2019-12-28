Lexer
=====

On this page we will implement a lexer to lex a very simple expression, on the
next page we will go on to implement a parser for it.

.. code-block:: idris

  module ParserExample

  import Text.Lexer
  import public Text.Parser.Core
  import public Text.Parser


to run:

.. code-block:: idris

  cd Idris-dev/libs/contrib
  idris -p contrib parserEx.idr
       ____    __     _
      /  _/___/ /____(_)____
      / // __  / ___/ / ___/     Version 1.3.2
    _/ // /_/ / /  / (__  )      http://www.idris-lang.org/
   /___/\__,_/_/  /_/____/       Type :? for help

  Idris is free software with ABSOLUTELY NO WARRANTY.
  For details type :warranty.
  Type checking ./Text/Token.idr
  Type checking ./Text/Quantity.idr
  Type checking ./Control/Delayed.idr
  Type checking ./Data/Bool/Extra.idr
  Type checking ./Text/Lexer/Core.idr
  Type checking ./Text/Lexer.idr
  Type checking ./parserEx.idr

.. code-block:: idris

  *parserEx> lex expressionTokens "1+2"
  ([MkToken 0 0 (Number 1),
    MkToken 0
          (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "1" of
             (incol, "") => c + cast (length incol)
             (incol, b) => cast (length incol))
          (Operator "+"),
    MkToken 0
          (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "+" of
             (incol, "") => c + cast (length incol)
             (incol, b) => cast (length incol))
          (Number 2)],
   0,
   case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "2" of
     (incol, "") => c + cast (length incol)
     (incol, b) => cast (length incol),
   getString (MkStrLen "" 0)) : (List (TokenData ExpressionToken),
                               Int,
                               Int,
                               String)
  *parserEx>

The lexer uses potentially infinite data structures. It has recursive arguments (codata type) so code is lazy.

.. code-block:: idris

  %default total

  public export
  data ExpressionToken = Number Integer
           | Operator String
           | OParen
           | CParen
           | EndInput

.. code-block:: idris

  export
  Show ExpressionToken where
    show (Number x) = "number " ++ show x
    show (Operator x) = "operator " ++ x
    show OParen = "("
    show CParen = ")"
    show EndInput = "end of input"

.. code-block:: idris

  export
  Show (TokenData ExpressionToken) where
    show (MkToken l c t) = "line=" ++ show l ++ " col=" ++ show c ++ "tok=" ++ show t

.. code-block:: idris

  -- integer arithmetic operators plus, minus and multiply.
  export
  opChars : String
  opChars = "+-*"

  operator : Lexer
  operator = some (oneOf opChars)

.. code-block:: idris

  toInt' : String -> Integer
  toInt' = cast

  expressionTokens : TokenMap ExpressionToken
  expressionTokens =
    [(digits, \x => Number (toInt' x)),
     (operator, \x => Operator x),
     (is '(' ,\x => OParen),
     (is ')' ,\x => CParen)]

Lexer
-----

.. image:: ../image/tokenise.png
   :width: 484px
   :height: 147px
   :alt: diagram illustrating these stages of lexer and parser

To lex some string to a list of tokens we define the structures using recognisers:

img src="recogniser.png" alt="recognisers" width="487" height="249"

There are constructors and combinators to allow the construction of the lexer definition:

A simple recogniser is 'Pred' which uses a predicate (Char -> Bool) to test whether to accept the character. It can be constructed using the 'is' function:

.. code-block:: idris

  Idris> :module Lexer2
  *Lexer2> is 'a'
  Pred (\ARG =>
           intToBool (prim__eqChar ARG 'a'))
                              : Recognise True

Recognisers can be combined, for example,

.. list-table::

  * - <+> means sequence two recognisers. If either consumes a character, the sequence
          is guaranteed to consume a character.

      .. code-block:: idris

         *Lexer2> is 'a' <+> is 'b'
         SeqEat (Pred (\ARG => intToBool (prim__eqChar ARG 'a')))
               (Delay (is 'b')) : Recognise True
         *Lexer2> 

    - <|> means if both consume, the combination is guaranteed
          to consumer a character:

      .. code-block:: idris

        *Lexer2> is 'a' <|> is 'b'
        Alt (Pred (\ARG => intToBool (prim__eqChar ARG 'a')))
            (Pred (\ARG => intToBool (prim__eqChar ARG 'b'))) : Recognise True
        *Lexer2> 

So far, this is static code, to define the lexical structure. To lex a given text we need to pass this to the runtime code.

However this can only  cut up the string into a list of substrings, these must be converted into tokens so we need a way to construct tokens. This will also depend on the  lexical structure we require.

TokenMap
--------

We then need to generate a TokenMap. This is a  mapping from lexers to the tokens they produce. This is a list of pairs:

.. code-block:: idris

  (Lexer, String -> tokenType)

For each Lexer in the list, if a substring in the input matches, run
the associated function to produce a token of type `tokenType`

from Core:

.. code-block:: idris

  TokenMap : (tokenType : Type) -> Type
  TokenMap tokenType = List (Lexer, String -> tokenType)

Here is the code that generates the TokenMap for Idris2 lexer from 

_`TokenMap for Idris2 lexer`: https://github.com/edwinb/Idris2/blob/master/src/Parser/Lexer.idr">src/Parser/Lexer.idr

So, for our code, we can then turn this into a tokenMap by using a function like this:.

.. _parserLibraryWhitespace:

Whitespace and Comments
=======================

The previous two pages introduced the lexer and parser but have not yet
discussed how to handle whitespace and comments.

In some grammars whitespace and comments would not be considered significant and
so we might be tempted not to generate any tokens for them. However, in the
running example, we may want to make spaces significant in the future. For
example, we might want to implement function application expressed by
juxtaposition as in Haskell and Idris like this: ``f x``.

So, on this page, we will add a token for whitespace and comments. We will
then consider two ways to process this:

- Filter all whitespace tokens from the lexer results before passing to
  the parser.
- Process the whitespace tokens in the parser.

Whitespace and Comments in Lexer
--------------------------------

To start with we can use the same token for both whitespace and comments. Here
it is called ``Comment`` and added to the ``ExpressionToken`` data structure
like this:

.. code-block:: idris

  public export
  data ExpressionToken = Number Integer
           | Operator String
           | OParen
           | CParen
           | Comment String
           | EndInput

This is added to the ``TokenMap`` like this:

.. code-block:: idris

  ||| from https://github.com/edwinb/Idris2/blob/master/src/Parser/Lexer.idr
  comment : Lexer
  comment = is '-' <+> is '-' <+> many (isNot '\n')

  expressionTokens : TokenMap ExpressionToken
  expressionTokens =
    [(digits, \x => Number (toInt' x)),
     (operator, \x => Operator x),
     (is '(' ,\x => OParen),
     (is ')' ,\x => CParen),
     (spaces, Comment),
     (comment, Comment)]

As you can see, the comment is defined like a single line Idris comment,
it starts with ``--`` and continues for the remainder of the line.

We don't need to define ``spaces`` because it is already defined in
: https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Text/Lexer.idr
like this:

.. code-block:: idris

  ||| Recognise a single whitespace character
  ||| /\\s/
  space : Lexer
  space = pred isSpace

  ||| Recognise one or more whitespace characters
  ||| /\\s+/
  spaces : Lexer
  spaces = some space

If these whitespace tokens are not significant, that is, they can appear
anywhere and they are optional then we can filter them out before the parser
gets them like this:

.. code-block:: idris

  processWhitespace : (List (TokenData ExpressionToken), Int, Int, String)
                  -> (List (TokenData ExpressionToken), Int, Int, String)
  processWhitespace (x,l,c,s) = ((filter notComment x),l,c,s) where
      notComment : TokenData ExpressionToken -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True

  calc : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  calc s = parse expr (fst (processWhitespace (lex expressionTokens s)))


Whitespace and Comments in Parser
---------------------------------

If we sometimes require whitespace to be significant then we can't filter
them out as above. In this case the ``Comment`` tokens are sent to the parser
which now needs to be able to handle them.

.. code-block:: idris

  commentSpace : Rule Integer
  commentSpace = terminal (\x => case tok x of
                           Comment s => Just 0
                           _ => Nothing)

So far we don't have any syntax that requires spaces to be significant so we
need to define the grammar so that it will parse with, or without, spaces.
This needs to be done in a systematic way, here I have defined the grammar so
that there is an optional space to the right of every atom or operator.
First add versions of ``intLiteral`` , ``openParen`` , ``closeParen`` 
and ``op`` that allow optional spaces/comments to the right of them:

.. code-block:: idris

  intLiteralC : Rule Integer
  intLiteralC = (intLiteral <* commentSpace) <|> intLiteral

  openParenC : Rule Integer
  openParenC = (openParen <* commentSpace) <|> openParen

  closeParenC : Rule Integer
  closeParenC = (closeParen <* commentSpace) <|> closeParen

  ||| like op but followed by optional comment or space
  opC : String -> Rule Integer
  opC s = ((op s) <* commentSpace) <|> (op s)

Then just use these functions instead of the original functions:

.. code-block:: idris

  expr : Rule Integer

  factor : Rule Integer
  factor = intLiteralC <|> do
                openParenC
                r <- expr
                closeParenC
                pure r

  term : Rule Integer
  term = map multInt factor <*> (
          (opC "*")
          *> factor)
       <|> factor

  expr = map addInt term <*> (
          (opC "+")
          *> term)
       <|> map subInt term <*> (
          (opC "-")
          *> term)
       <|> term

  calc : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  calc s = parse expr (fst (lex expressionTokens s))

  lft : (ParseError (TokenData ExpressionToken)) -> IO ()
  lft (Error s lst) = putStrLn ("error:"++s)

  rht : (Integer, List (TokenData ExpressionToken)) -> IO ()
  rht i = putStrLn ("right " ++ (show i))

  main : IO ()
  main = do
    putStr "alg>"
    x <- getLine
    either lft rht (calc x) -- eliminator for Either


Defining Block Structure using Indents
--------------------------------------

Many languages such as Python, Haskell and Idris use indents to delimit
the block structure of the language.

We can see how Idris2 does it here
: https://github.com/edwinb/Idris2/blob/master/src/Parser/Support.idr

.. code-block:: idris

  export
  IndentInfo : Type
  IndentInfo = Int

  export
  init : IndentInfo
  init = 0

EndInput Token
--------------

So far, the parser will return a successful result even if the full input
is not consumed. To ensure that the top level syntax is fully matched we
add a ``EndInput`` token to indicate the last token.

``EndInput`` is added to the other tokens like this:

.. code-block:: idris

  data ExpressionToken = Number Integer
           | Operator String
           | OParen
           | CParen
           | Comment String
           | EndInput

A rule to consume this token is added:

.. code-block:: idris

  eoi : Rule Integer
  eoi = terminal (\x => case tok x of
                           EndInput => Just 0
                           _ => Nothing)

Instead of using ``expr`` at the top level of the syntax we can now define
``exprFull`` as shown here. This will make sure that only when ``EndInput``
is consumed will the parse be successful:

.. code-block:: idris

  exprFull : Rule Integer
  exprFull = expr <* eoi

The following code makes sure ``EndInput`` is added to the end of the token
list:

.. code-block:: idris

  processWhitespace : (List (TokenData ExpressionToken), Int, Int, String)
                  -> (List (TokenData ExpressionToken), Int, Int, String)
  processWhitespace (x,l,c,s) = ((filter notComment x)++
                                      [MkToken l c EndInput],l,c,s) where
      notComment : TokenData ExpressionToken -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True

All we have to do now is use ``exprFull`` instead of ``expr``:

.. code-block:: idris

  calc : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  calc s = parse exprFull (fst (processWhitespace (lex expressionTokens s)))


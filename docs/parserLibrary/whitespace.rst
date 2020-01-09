.. _parserLibraryWhitespace:

Whitespace and Comments
=======================

The previous two pages introduced the lexer and parser but have not yet
discussed how to handle whitespace and comments.

In some grammars whitespace and comments would not be considered significant and
so we might be tempted not to generate any tokens for them. However, in the
running example, we may want to make spaces significant. For example, we might
want to implement function application expressed by juxtaposition as in
Haskell and Idris like this: ``f x``.

Also, I'm not sure if it is an problem for error messages and so on if some
text does not have corresponding tokens.

So, on this page, we will add a token for whitespace and comments.

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
     (space, Comment),
     (comment, Comment)]

As you can see, the comment is defined like a single line Idris comment,
it starts with ``--`` and continues for the remainder of the line.

We don't need to define ``space`` because it is already defined in
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

Whitespace and Comments in Parser
---------------------------------

Now that there are ``Comment`` tokens the parser needs to be able to handle them.

So far we don't have any syntax that requires spaces to be significant so we
need to define the grammar so that it will parse with, or without, spaces.
This needs to be done in a systematic way, here I have defined the grammar so
that there is an optional space to the right of every atom or operator:

.. code-block:: idris

  commentSpace : Rule Integer
  commentSpace = terminal (\x => case tok x of
                           Comment s => Just 0
                           _ => Nothing)

.. code-block:: idris

  partial
  exprAtom : Rule Integer
  exprAtom = (intLiteral <* commentSpace)
           <|> intLiteral <|> (paren expr)

  partial
  expr1 : Rule Integer
  expr1 = map multInt exprAtom <*> (
          (((op "*") <* commentSpace) <|> (op "*"))
          *> exprAtom)

  partial
  exprMult : Rule Integer
  exprMult = expr1 <|> exprAtom

  partial
  expr2 : Rule Integer
  expr2 = map addInt exprMult <*> (
          (((op "+") <* commentSpace) <|> (op "+"))
          *> exprMult)

  partial
  exprAdd : Rule Integer
  exprAdd = expr2 <|> exprMult

  partial
  expr3 : Rule Integer
  expr3 = map subInt exprAdd <*> (
          (((op "-") <* commentSpace) <|> (op "-"))
          *> expr)

  expr = expr3 <|> exprAdd












           

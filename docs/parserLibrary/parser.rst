.. _parserLibraryParser:

Parser
======

To run the parser we call ``parse``. This requires a grammar and the output
from the lexer (which is a list of tokens).

.. code-block:: idris

  parse : (act : Grammar tok c ty) -> (xs : List tok) ->
        Either (ParseError tok) (ty, List tok)

If successful this returns 'Right' with a pair of

- the parse result.
- the unparsed tokens (the remaining input).

otherwise it returns 'Left' with the error message.

So we need to define the grammar for our parser, this is done using the following
'Grammar' data structure. This is a combinator structure, similar in principle
to the recogniser combinator for the lexer, which was discussed on the
previous page.

As with the Recogniser the ``Grammar`` type is dependent on a boolean 'consumes'
value which allows us to ensure that complicated ``Grammar`` structures will always
consume input.

.. code-block:: idris

  ||| Description of a language's grammar. The `tok` parameter is the type
  ||| of tokens, and the `consumes` flag is True if the language is guaranteed
  ||| to be non-empty - that is, successfully parsing the language is guaranteed
  ||| to consume some input.
  public export
  data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : String -> (tok -> Maybe a) -> Grammar tok True a
     NextIs : String -> (tok -> Bool) -> Grammar tok False tok
     EOF : Grammar tok False ()

     Fail : Bool -> String -> Grammar tok c ty
     Commit : Grammar tok False ()
     MustWork : Grammar tok c a -> Grammar tok c a

     SeqEat : Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
              Grammar tok True b
     SeqEmpty : {c1, c2 : Bool} ->
                Grammar tok c1 a -> (a -> Grammar tok c2 b) ->
                Grammar tok (c1 || c2) b
     Alt : {c1, c2 : Bool} ->
           Grammar tok c1 ty -> Grammar tok c2 ty ->
           Grammar tok (c1 && c2) ty

So an example of a grammar type may look something like this:
``Grammar (TokenData ExpressionToken) True Integer``.
This is a complicated type name and a given parser will need to use it a lot.
So to reduce the amount of typing we can use the following type synonym (similar
to what is done in Idris 2
: https://github.com/edwinb/Idris2/blob/master/src/Parser/Support.idr
)

.. code-block:: idris

  public export
  Rule : Type -> Type
  Rule ty = Grammar (TokenData ExpressionToken) True ty

Parser Example
--------------

On the previous page we implemented a lexer to 'lex' a very simple expression, on
this page we will go on to add a parser for this running example.

.. list-table::

  * - The syntax we are aiming at is something
      like this (expressed in Backus–Naur form (BNF)):
    - .. code-block:: idris

         <expr> ::= <integer literal>
          |  <expr>'+'<expr>
          |  <expr>'-'<expr>
          |  <expr>'*'<expr>
          |  '('<expr>')'

         <integer literal> ::= <digit>|<integer literal><digit>

.. list-table::

  * - To start, here is a grammar to parse an integer literal (that is, a
      sequence of numeric characters).

    - .. code-block:: idris

         export
         intLiteral : Rule Integer
         intLiteral
           = terminal (\x => case tok x of
                           Number i => Just i
                           _ => Nothing)

In order to try this out, here is a temporary function, this calls
parse which takes two parameters:

- The grammar (in this case intLiteral)
- The token list from the lexer.

.. code-block:: idris

  test1 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  test1 s = parse intLiteral (fst (lex expressionTokens s))

As required, if we pass it a string which is a number literal then it will
return the number in the 'Right' option.

.. code-block:: idris

  *parserEx> test1 "123"
  Right (123, []) : Either (ParseError (TokenData ExpressionToken))
                         (Integer, List (TokenData ExpressionToken))

If we pass it a string which is not a number literal then it will return an
error message.

.. code-block:: idris

  *parserEx> test1 "a"
  Left (Error "End of input"
            []) : Either (ParseError (TokenData ExpressionToken))
                         (Integer, List (TokenData ExpressionToken))

If we pass it a number followed by something else, then it will still be
successful, this is because we are not specifically checking for end-of-file.

.. code-block:: idris

  *parserEx> test1 "123a"
  Right (123, []) : Either (ParseError (TokenData ExpressionToken))
                         (Integer, List (TokenData ExpressionToken))
  *parserEx> 

.. list-table::

  * - The ``intLiteral`` function above uses the ``terminal`` function to
      construct the grammar
    - .. code-block:: idris

        ||| Succeeds if running the predicate on the
        ||| next token returns Just x, returning x.
        ||| Otherwise fails.
        export
        terminal : (tok -> Maybe a) -> Grammar tok True a
        terminal = Terminal

This is defined here
: https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Text/Parser/Core.idr
Idris 2 uses a slightly different version which stores an error message like
"Expected integer literal" which can be output if the rule fails
: https://github.com/edwinb/Idris2/blob/master/src/Text/Parser/Core.idr

.. list-table::

  * - The 'terminal' function is also used to construct the other
      elements of the grammar that we require, for instance,
      opening parenthesis:

    - .. code-block:: idris

         openParen : Rule Integer
         openParen = terminal (\x => case tok x of
                           OParen => Just 0
                           _ => Nothing)

Integer value is not really relevant for parenthesis so ``0`` (zero) is used as
a default value.

As before, this can be tested with a function like this:

.. code-block:: idris

  test2 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  test2 s = parse openParen (fst (lex expressionTokens s))

We can see below that it correctly parses an open parenthesis and gives an
error for anything else:

.. code-block:: idris

  *parserEx> test2 "("
  Right (0, []) : Either (ParseError (TokenData ExpressionToken))
                       (Integer, List (TokenData ExpressionToken))
  *parserEx> test2 "123"
  Left (Error "Unrecognised token"
            [MkToken 0
                     0
                     (Number 123)]) : Either (ParseError (TokenData ExpressionToken))
                                             (Integer,
                                              List (TokenData ExpressionToken))

Now we have two Grammars we can try combining them. The following test looks
for ``openParen`` followed by ``intLiteral``, the two Grammars are combined using
``<*>``. The ``map const`` part uses the integer value from the first.

The following test is looking for ``(`` followed by a number:

.. code-block:: idris

  test3 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  test3 s = parse (map const openParen <*> intLiteral) (fst (lex expressionTokens s))

We can see below that ``(`` followed by a number is successfully parsed but, as
required, other token lists are not:

.. code-block:: idris

  *parserEx> test3 "(123"
  Right (0, []) : Either (ParseError (TokenData ExpressionToken))
                       (Integer, List (TokenData ExpressionToken))
  *parserEx> test3 "(("
  Left (Error "Unrecognised token"
            [MkToken 0
                     (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n')))
                                 "(" of
                        (incol, "") => c + cast (length incol)
                        (incol, b) => cast (length incol))
                     OParen]) : Either (ParseError (TokenData ExpressionToken))
                                       (Integer, List (TokenData ExpressionToken))

  *parserEx> test3 "123"
  Left (Error "Unrecognised token"
            [MkToken 0
                     0
                     (Number 123)]) : Either (ParseError (TokenData ExpressionToken))
                                             (Integer,
                                              List (TokenData ExpressionToken))
  *parserEx> test3 "123("
  Left (Error "Unrecognised token"
            [MkToken 0 0 (Number 123),
             MkToken 0
                     (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n')))
                                 "321" of
                        (incol, "") => c + cast (length incol)
                        (incol, b) => cast (length incol))
                     OParen]) : Either (ParseError (TokenData ExpressionToken))
                                       (Integer, List (TokenData ExpressionToken))

.. list-table::

  * - The closing parenthesis is constructed in the same way.

    - .. code-block:: idris

        closeParen : Rule Integer
        closeParen = terminal (\x => case tok x of
                           CParen => Just 0
                           _ => Nothing)

.. list-table::

  * - Now we can generate a Grammar for an expression inside parenthesis
      like this.

    - .. code-block:: idris

        paren : Rule Integer -> Rule Integer
        paren exp = openParen *> exp <* closeParen

The use of ``*>`` and ``<*`` instead of ``<*>`` is an easy way to use the integer
value from the inner expression.

So lets try to use this to define a grammar which recognises either:

- An integer literal
- An integer literal inside parenthesis
- An integer literal inside parenthesis inside parenthesis
- ... and so on.

.. list-table::

  * - This requires a recursively defined structure like this:

    - .. code-block:: idris

        partial
        expr : Rule Integer
        expr = intLiteral <|> (paren expr)

This is a valid grammar because every time it is called it is guaranteed to
consume a token. However, as an Idris structure, it is problematic due to
the recursion. Defining it as partial allows it to compile but at runtime
we are likely to get a crash with an (unhelpful) error message like
``killed by signal 11``.

So a better method is to use ``do`` notation as described in the following
section.

Monadic Combinator
------------------

In addition to ``<|>`` and ``<*>`` there is a ``>>=`` combinator, which is
defined like this:

.. code-block:: idris

  ||| Sequence two grammars. If either consumes some input, the sequence is
  ||| guaranteed to consume some input. If the first one consumes input, the
  ||| second is allowed to be recursive (because it means some input has been
  ||| consumed and therefore the input is smaller)
  export %inline
  (>>=) : {c1 : Bool} ->
        Grammar tok c1 a ->
        inf c1 (a -> Grammar tok c2 b) ->
        Grammar tok (c1 || c2) b
  (>>=) {c1 = False} = SeqEmpty
  (>>=) {c1 = True} = SeqEat

.. list-table::

  * - This allows us to use ``do`` notation for the previous parenthesis example:

    - .. code-block:: idris

         expr = intLiteral <|> do
                openParen
                r <- expr
                closeParen
                pure r

This can be more flexible than using the ``<*>`` operator. Also it is defined
using ``Inf`` so we can implement recursively defined grammars as above.

Implementing the Arithmetic Operators
-------------------------------------

.. list-table::

  * - Now for the operations, in this case: ``+``, ``-`` and ``*``.
      The syntax we require for these infix operators
      would require recursive grammars like this:

    - .. code-block:: idris

        expr = expr (op "+") expr

As already explained, ``do`` notation can allow us to use recursive
definitions but not necessarily left-recursion like this.

In order to work up to this gradually lets start with prefix operators
(sometimes known as Polish notation) then modify later for infix operators.

.. list-table::

  * - So prefix operators would have this sort of form:

    - .. code-block:: idris

        expr = (add (op "+") expr expr)

where ``op`` is defined like this:

.. code-block:: idris

  ||| Matches if this is an operator token and string matches, that is,
  ||| it is the required type of operator.
  op : String -> Rule Integer
  op s = terminal (\x => case tok x of
                           (Operator s1) => if s==s1 then Just 0 else Nothing
                           _ => Nothing)

.. list-table::

  * - and ``add`` is defined like this:

      Where:

      - x is the add operator.
      - y is the first operand.
      - z is the second operand.

    - .. code-block:: idris

        addInt : Integer -> Integer -> Integer
        addInt a b = a+b

        export
        add : Grammar tok c1 Integer ->
            Grammar tok c2 Integer ->
            Grammar tok c3 Integer ->
            Grammar tok ((c1 || c2) || c3) Integer
        add x y z = map addInt (x *> y) <*> z



The resulting integer will be the sum of the two operands.

.. list-table::

  * - The other operators are defined in a similar way:

    - .. code-block:: idris

        subInt : Integer -> Integer -> Integer
        subInt a b = a-b

        export
        sub : Grammar tok c1 Integer ->
            Grammar tok c2 Integer ->
            Grammar tok c3 Integer ->
            Grammar tok ((c1 || c2) || c3) Integer
        sub x y z = map subInt (x *> y) <*> z

        multInt : Integer -> Integer -> Integer
        multInt a b = a*b

        export
        mult : Grammar tok c1 Integer ->
            Grammar tok c2 Integer ->
            Grammar tok c3 Integer ->
            Grammar tok ((c1 || c2) || c3) Integer
        mult x y z = map multInt (x *> y) <*> z

So the top level ``Grammar`` can now be defined as follows. Note that this is
partial as it is a potentially infinite structure and so not total.

.. code-block:: idris

  partial
  expr : Rule Integer
  expr = (add (op "+") expr expr)
       <|> (sub (op "-") expr expr)
       <|> (mult (op "*") expr expr)
       <|> intLiteral <|> (paren expr)

.. list-table::

  * - To make the testing easier we can use this function:

    - .. code-block:: idris

        partial
        test : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
        test s = parse expr (fst (lex expressionTokens s))

.. list-table::

  * - First test a valid (prefix) expression:

    - .. code-block:: idris

        *parserEx> test "+1*6(4)"
        Right (25,
             []) : Either (ParseError (TokenData ExpressionToken))
                    (Integer, List (TokenData ExpressionToken))

Then an invalid syntax:

.. code-block:: idris

  *parserEx> test "))"
  Left (Error "Unrecognised token"
            [MkToken 0 0 CParen,
             MkToken 0
                     (case fspan (\ARG =>
                                    not (intToBool (prim__eqChar ARG
                                                                 '\n')))
                                 ")" of
                        (incol, "") => c + cast (length incol)
                        (incol, b) => cast (length incol))
                     CParen]) : Either (ParseError (TokenData ExpressionToken))
                                       (Integer,
                                        List (TokenData ExpressionToken))

However if we try something that is invalid, but starts with a valid token,
then it will return ``Right`` (to indicate success)

.. code-block:: idris

  *parserEx> test "1))"
  Right (1,
       [MkToken 0
                (case fspan (\ARG =>
                               not (intToBool (prim__eqChar ARG '\n')))
                            "1" of
                   (incol, "") => c + cast (length incol)
                   (incol, b) => cast (length incol))
                CParen,
        MkToken 0
                (case fspan (\ARG =>
                               not (intToBool (prim__eqChar ARG '\n')))
                            ")" of
                   (incol, "") => c + cast (length incol)
                   (incol, b) => cast (length incol))
                CParen]) : Either (ParseError (TokenData ExpressionToken))
                                  (Integer,
                                   List (TokenData ExpressionToken))

Infix Notation
--------------

So far we have implemented a prefix notation for operators (like this:
``+ expr expr``) but the aim is to implemented an infix notation (like this:
``expr + expr``). To do this we must be able to deal with potentially
infinite data structures (see Codata Types here :ref:`sect-typefuns`).

First alter the grammar to have infix operations:

.. code-block:: idris

  addInt : Integer -> Integer -> Integer
  addInt a b = a+b

  export
  add : Grammar tok c1 Integer ->
      Grammar tok c2 Integer ->
      Grammar tok c3 Integer ->
      Grammar tok ((c1 || c2) || c3) Integer
  add x y z = map addInt (x <* y) <*> z

  subInt : Integer -> Integer -> Integer
  subInt a b = a-b

  export
  sub : Grammar tok c1 Integer ->
      Grammar tok c2 Integer ->
      Grammar tok c3 Integer ->
      Grammar tok ((c1 || c2) || c3) Integer
  sub x y z = map subInt (x <* y) <*> z


  multInt : Integer -> Integer -> Integer
  multInt a b = a*b

  export
  mult : Grammar tok c1 Integer ->
      Grammar tok c2 Integer ->
      Grammar tok c3 Integer ->
      Grammar tok ((c1 || c2) || c3) Integer
  mult x y z = map multInt (x <* y) <*> z

  partial
  expr : Rule Integer
  expr = (add expr (op "+") expr)
       <|> (sub expr (op "-") expr)
       <|> (mult expr (op "*") expr)
       <|> intLiteral <|> (paren expr)

However, if this was run, the code would not terminate.

Implement Left Recursion Elimination
------------------------------------

Left factoring, like this, is a general problem.

If we have a rule like this:

.. code-block:: idris

  A -> (x<*>y) <|> (x<*>z)

If ``x<*>y`` fails but ``x<*>z`` would succeed a problem is that, ``x<*>y`` has
already consumed ``x``, so now ``x<*>z`` will fail.

so we could write code to backtrack. That is ``try`` ``x<*>y`` without consuming
so that, if the first token succeeds but the following tokens fail, then the
first tokens would not be consumed.

Another approach is left factoring:

Left Factoring
--------------

Replace the rule with two rules (that is we add a non-terminal symbol) so
for example, instead of:

.. code-block:: idris

  A -> (x<*>y) <|> (x<*>z)

we add an extra rule to give:

.. code-block:: idris

  A -> x<*>N
  N -> y <|> z

That is we convert a general context-free grammar to a LL(1) grammar. Although
not every context-free grammar can be converted to a LL(1) grammar.

This still does not solve the infinite recursion issue and there is another
problem: the precedence of the operators ``+``, ``-`` and ``*`` is not explicit.

.. list-table::

  * - To resolve this we can alter the example to have a BNF like this:
      Where braces ``{ ... }`` mean the contents can occur 1 or more times.

    - .. code-block:: idris

        'expression' ::=  ('+'|'-') 'term' {('+'|'-') 'term'}

        'term' ::=  'factor' {'*' 'factor'}

        'factor' ::=
           number
           | '(' 'expression' ')'


.. code-block:: idris

  expr : Rule Integer

  factor : Rule Integer
  factor = intLiteral <|> do
                openParen
                r <- expr
                closeParen
                pure r

  term : Rule Integer
  term = map multInt factor <*> (
          (op "*")
          *> factor)
       <|> factor

  expr = map addInt term <*> (
          (op "+")
          *> term)
       <|> map subInt term <*> (
          (op "-")
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

As the following tests show, this now handles infix operators and precedence.

.. list-table::

  * - For example '*' is an infix operator:

    - .. code-block:: idris

         *algebraREPL> :exec
         alg>2*3
         right (6, [])

  * - Check that atomic number literals work:

    - .. code-block:: idris

         *algebraREPL> :exec
         alg>2
         right (2, [])

  * - Check that '*' has a higher precedence than '+'.

    - .. code-block:: idris

         *algebraREPL> :exec
         alg>2+3*4
         right (14, [])

  * - Also '*' has a higher precedence than '+' when the order is reversed.

    - .. code-block:: idris

         *algebraREPL> :exec
         alg>3*4+2
         right (14, [])

  * - Also precedence can be overridden by parenthesis.

    - .. code-block:: idris

         *algebraREPL> :exec
         alg>(2+3)*4
         right (20, [])

This is still not correct because it does not correctly parse multiple sums or terms
like ``1+2+3`` or ``1*2*3``.

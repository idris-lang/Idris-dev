Parser
======

On the previous page we implemented a lexer to lex a very simple expression, on this
page we will go on to implement a parser for it.

To run our parser we call 'doParse'. This requires the output from the lexer (a list of tokens) and a Grammar.

.. code-block:: idris

  doParse : {c : Bool} ->
          (commit : Bool) -> (xs : List tok) -> (act : Grammar tok c ty) ->
          ParseResult xs c ty

So we need to define the Grammar for our parser

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

.. code-block:: idris

  -- from  Idris2/src/Parser/Support.idr 
  public export
  Rule : Type -> Type
  Rule ty = Grammar (TokenData ExpressionToken) True ty

.. code-block:: idris

  export
  intLiteral : Rule Integer
  intLiteral
    = terminal --"Expected integer literal"
               (\x => case tok x of
                           Number i => Just i
                           _ => Nothing)

In order to try this out, here is a temporary function, this calls
parse which takes two parameters:
* The grammar (in this case intLiteral)
* The token list from the lexer.

.. code-block:: idris

  test1 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  test1 s = parse intLiteral (fst (lex expressionTokens s))

As required, if we pass it a string which is a number literal then it will return the
number in the 'Right' option.

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

.. code-block:: idris

  ||| Succeeds if running the predicate on the next token returns Just x,
  ||| returning x. Otherwise fails.
  export
  terminal : (tok -> Maybe a) -> Grammar tok True a
  terminal = Terminal

.. code-block:: idris

  openParen : Rule Integer
  openParen = terminal (\x => case tok x of
                           OParen => Just 0
                           _ => Nothing)

.. code-block:: idris

  test2 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  test2 s = parse openParen (fst (lex expressionTokens s))

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
  *parserEx> 

.. code-block:: idris

  test3 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  test3 s = parse (map const openParen <*> intLiteral) (fst (lex expressionTokens s))

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
  *parserEx>

.. code-block:: idris

  closeParen : Rule Integer
  closeParen = terminal (\x => case tok x of
                           CParen => Just 0
                           _ => Nothing)

.. code-block:: idris

  ||| Matches if this is an operator token and string matches, that is,
  ||| it is the required type of operator.
  op : String -> Rule Integer
  op s = terminal (\x => case tok x of
                           (Operator s1) => if s==s1 then Just 0 else Nothing
                           _ => Nothing)

.. code-block:: idris

  paren : Rule Integer -> Rule Integer
  paren exp = openParen *> exp <* closeParen

.. code-block:: idris

  addInt : Integer -> Integer -> Integer
  addInt a b = a+b

  export
  add : Grammar tok c1 Integer ->
      Grammar tok c2 Integer ->
      Grammar tok c3 Integer ->
      Grammar tok ((c1 || c2) || c3) Integer
  add x y z = map addInt (x *> y) <*> z

.. code-block:: idris

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

.. code-block:: idris

  partial
  expr : Rule Integer
  expr = (add (op "+") expr expr)
       <|> (sub (op "-") expr expr)
       <|> (mult (op "*") expr expr)
       <|> intLiteral <|> (paren expr)

.. code-block:: idris

  *parserEx> parse expr (fst (lex expressionTokens "(1)"))
  Right (1, []) : Either (ParseError (TokenData ExpressionToken))
                       (Integer, List (TokenData ExpressionToken))
  *parserEx>

.. code-block:: idris

  parse : (act : Grammar tok c ty) -> (xs : List tok)

  parse intLiteral (fst (lex expressionTokens "1"))

.. code-block:: idris

  *parserEx> parse expr (fst (lex expressionTokens "1+2"))
  Right (1,
       [MkToken 0
                (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "1" of
                   (incol, "") => c + cast (length incol)
                   (incol, b) => cast (length incol))
                (Operator "+"),
        MkToken 0
                (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "+" of
                   (incol, "") => c + cast (length incol)
                   (incol, b) => cast (length incol))
                (Number 2)]) : Either (ParseError (TokenData ExpressionToken))
                                      (Integer, List (TokenData ExpressionToken))
  *parserEx>

.. code-block:: idris

  partial
  test : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
  test s = parse expr (fst (lex expressionTokens s))


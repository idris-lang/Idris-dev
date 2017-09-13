module Text.Parser

%default total

-- TODO: Add some primitives for helping with error messages.
-- e.g. perhaps set a string to state what we're currently trying to
-- parse, or to say what the next expected token is in words

||| Description of a language's grammar. The `tok` parameter is the type
||| of tokens, and the `consumes` flag is True if the language is guaranteed
||| to be non-empty - that is, successfully parsing the language is guaranteed
||| to consume some input.
export
data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : (tok -> Maybe a) -> Grammar tok True a
     NextIs : (tok -> Bool) -> Grammar tok False tok
     EOF : Grammar tok False ()

     Fail : String -> Grammar tok c ty
     Commit : Grammar tok False ()

     SeqEat : Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
              Grammar tok True b
     SeqEmpty : {c1, c2 : Bool} ->
                Grammar tok c1 a -> (a -> Grammar tok c2 b) ->
                Grammar tok (c1 || c2) b
     Alt : {c1, c2 : Bool} ->
           Grammar tok c1 ty -> Grammar tok c2 ty ->
           Grammar tok (c1 && c2) ty

public export
inf : Bool -> Type -> Type
inf True t = Inf t
inf False t = t

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
export %inline
(>>=) : {c1 : Bool} ->
        Grammar tok c1 a -> inf c1 (a -> Grammar tok c2 b) ->
        Grammar tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True} = SeqEat

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export
(<|>) : Grammar tok c1 ty -> Grammar tok c2 ty ->
        Grammar tok (c1 && c2) ty
(<|>) = Alt

export
pure : (val : ty) -> Grammar tok False ty
pure = Empty

||| Check whether the next token satisfies a predicate
export
nextIs : (tok -> Bool) -> Grammar tok False tok
nextIs = NextIs

||| Look at the next token in the input
export
peek : Grammar tok False tok
peek = nextIs (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export
terminal : (tok -> Maybe a) -> Grammar tok True a
terminal = Terminal

||| Always fail with a message
export
fail : String -> Grammar tok c ty
fail = Fail

||| Succeed if the input is empty
export
eof : Grammar tok False ()
eof = EOF

||| Commit to an alternative; if the current branch of an alternative
||| fails to parse, no more branches will be tried
export
commit : Grammar tok False ()
commit = Commit

data ParseResult : List tok -> (consumes : Bool) -> Type -> Type where
     Failure : {xs : List tok} ->
               (committed : Bool) ->
               (err : String) -> (rest : List tok) -> ParseResult xs c ty
     EmptyRes : (committed : Bool) ->
                (val : ty) -> (more : List tok) -> ParseResult more False ty
     NonEmptyRes : (committed : Bool) ->
                   (val : ty) -> (more : List tok) ->
                   ParseResult (x :: xs ++ more) c ty

weakenRes : {whatever, c : Bool} -> {xs : List tok} ->
            ParseResult xs c ty -> ParseResult xs (whatever && c) ty
weakenRes (Failure com msg ts) = Failure com msg ts
weakenRes {whatever=True} (EmptyRes com val xs) = EmptyRes com val xs
weakenRes {whatever=False} (EmptyRes com val xs) = EmptyRes com val xs
weakenRes (NonEmptyRes com val more) = NonEmptyRes com val more

shorter : (more : List tok) -> .(ys : List tok) ->
          LTE (S (length more)) (S (length (ys ++ more)))
shorter more [] = lteRefl
shorter more (x :: xs) = LTESucc (lteSuccLeft (shorter more xs))

doParse : {c : Bool} ->
          (xs : List tok) -> (act : Grammar tok c ty) ->
          ParseResult xs c ty
doParse xs act with (sizeAccessible xs)
  doParse xs (Empty val) | sml = EmptyRes False val xs
  doParse [] (Fail str) | sml = Failure False str []
  doParse (x :: xs) (Fail str) | sml = Failure False str (x :: xs)
  doParse xs Commit | sml = EmptyRes True () xs

  doParse [] (Terminal f) | sml = Failure False "End of input" []
  doParse (x :: xs) (Terminal f) | sml
        = maybe
             (Failure False "Unrecognised token" (x :: xs))
             (\a => NonEmptyRes False {xs=[]} a xs)
             (f x)
  doParse [] EOF | sml = EmptyRes False () []
  doParse (x :: xs) EOF | sml
        = Failure False "Expected end of input" (x :: xs)
  doParse [] (NextIs f) | sml = Failure False "End of input" []
  doParse (x :: xs) (NextIs f) | sml
        = if f x
             then EmptyRes False x (x :: xs)
             else Failure False "Unrecognised token" (x :: xs)
  doParse xs (Alt x y) | sml with (doParse xs x | sml)
    doParse xs (Alt x y) | sml | Failure com' msg ts
          = if com' -- If the alternative had committed, don't try the
                    -- other branch
               then Failure com' msg ts
               else weakenRes (doParse xs y | sml)
    -- Successfully parsed the first option
    doParse xs (Alt x y) | sml | (EmptyRes com' val xs)
          = EmptyRes com' val xs
    doParse (z :: (ys ++ more)) (Alt x y) | sml | (NonEmptyRes com' val more)
          = NonEmptyRes com' val more
  doParse xs (SeqEmpty act next) | (Access morerec)
          = case doParse xs act | Access morerec of
                 Failure com msg ts => Failure com msg ts
                 EmptyRes com val xs =>
                       case doParse xs (next val) | (Access morerec) of
                            Failure com' msg ts => Failure (com || com') msg ts
                            EmptyRes com' val xs => EmptyRes (com || com') val xs
                            NonEmptyRes com' val more => NonEmptyRes (com || com') val more
                 NonEmptyRes {x} {xs=ys} com val more =>
                       case (doParse more (next val) | morerec _ (shorter more ys)) of
                            Failure com' msg ts => Failure (com || com') msg ts
                            EmptyRes com' val _ => NonEmptyRes (com || com') val more
                            NonEmptyRes {x=x1} {xs=xs1} com' val more' =>
                                 rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                                         NonEmptyRes (com || com') val more'
  doParse xs (SeqEat act next) | sml with (doParse xs act | sml)
    doParse xs (SeqEat act next) | sml | Failure com msg ts
         = Failure com msg ts
    doParse (x :: (ys ++ more)) (SeqEat act next) | (Access morerec) | (NonEmptyRes com val more)
         = case doParse more (next val) | morerec _ (shorter more ys) of
                Failure com' msg ts => Failure (com || com') msg ts
                EmptyRes com' val _ => NonEmptyRes (com || com') val more
                NonEmptyRes {x=x1} {xs=xs1} com' val more' =>
                     rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                             NonEmptyRes (com || com') val more'
  -- This next line is not strictly necessary, but it stops the coverage
  -- checker taking a really long time and eating lots of memory...
  doParse _ _ | sml = Failure True "impossible: Help the coverage checker!" []

public export
data ParseError tok = Error String (List tok)

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : (xs : List tok) -> (act : Grammar tok c ty) ->
        Either (ParseError tok) (ty, List tok)
parse xs act
    = case doParse xs act of
           Failure _ msg ts => Left (Error msg ts)
           EmptyRes _ val rest => pure (val, rest)
           NonEmptyRes _ val rest => pure (val, rest)

||| Parse one or more things
export
some : Grammar tok True a ->
       Grammar tok True (List a)
some p = do x <- p
            (do xs <- some p
                pure (x :: xs)) <|> pure [x]

||| Parse zero or more things (may match the empty input)
export
many : Grammar tok True a ->
       Grammar tok False (List a)
many p = some p
     <|> pure []

||| Parse one or more things, separated by another thing
export
sepBy1 : Grammar tok True () -> Grammar tok True a ->
         Grammar tok True (List a)
sepBy1 sep p = do x <- p
                  (do sep
                      xs <- sepBy1 sep p
                      pure (x :: xs)) <|> pure [x]

||| Parse zero or more things, separated by another thing. May
||| match the empty input.
export
sepBy : Grammar tok True () -> Grammar tok True a ->
        Grammar tok False (List a)
sepBy sep p = sepBy1 sep p <|> pure []

||| Optionally parse a thing, with a default value if the grammar doesn't
||| match. May match the empty input.
export
optional : Grammar tok True a -> (ifNothing : a) ->
           Grammar tok False a
optional p def = p <|> pure def


||| Parse an instance of `p` that is between `left` and `right`.
export
between : (left  : Grammar tok True ())
       -> (right : Grammar tok True ())
       -> (p     : Grammar tok True a)
       -> Grammar tok True a
between left right contents = do
   left
   res <- contents
   right
   pure res

||| Parse one or more instances of `p` separated by `s`, returning the
||| parsed items and proof the resulting list is non-empty.
export
sepBy1' : (sep : Grammar tok True ())
       -> (p   : Grammar tok True a)
       -> Grammar tok True (xs : List a ** NonEmpty xs)
sepBy1' sep p
    = do x <- p
         (do sep
             xs <- sepBy1 sep p
             pure (x :: xs ** IsNonEmpty)) <|> pure ([x] ** IsNonEmpty)

||| Parse one or more instances of `p`, returning the parsed items and proof the resulting list is non-empty.
export
some' : (p : Grammar tok True a)
     -> Grammar tok True (xs : List a ** NonEmpty xs)
some' p = do
   x <- p
   (do xs <- some p
       pure (x::xs ** IsNonEmpty)) <|> pure ([x] ** IsNonEmpty)


||| Optionally parse a thing. If the grammar provides a default use `optional` instead.
export
maybe : Grammar tok True a
     -> Grammar tok False (Maybe a)
maybe p =
      (do res <- p; pure $ Just res)
  <|> pure Nothing

module Text.Parser.Core

import public Control.Delayed

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

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume input. This is an explicitly non-infinite version
||| of `>>=`.
export
seq : Grammar tok c1 a ->
      (a -> Grammar tok c2 b) ->
      Grammar tok (c1 || c2) b
seq = SeqEmpty

||| Sequence a grammar followed by the grammar it returns.
export
join : {c1 : Bool} ->
       Grammar tok c1 (Grammar tok c2 a) ->
       Grammar tok (c1 || c2) a
join {c1 = False} p = SeqEmpty p id
join {c1 = True} p = SeqEat p id

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export
(<|>) : Grammar tok c1 ty ->
        Grammar tok c2 ty ->
        Grammar tok (c1 && c2) ty
(<|>) = Alt

||| Allows the result of a grammar to be mapped to a different value.
export
Functor (Grammar tok c) where
  map f (Empty val)  = Empty (f val)
  map f (Fail msg)   = Fail msg
  map f (Terminal g) = Terminal (\t => map f (g t))
  map f (Alt x y)    = Alt (map f x) (map f y)
  map f (SeqEat act next)
      = SeqEat act (\val => map f (next val))
  map f (SeqEmpty act next)
      = SeqEmpty act (\val => map f (next val))
  -- The remaining constructors (NextIs, EOF, Commit) have a fixed type,
  -- so a sequence must be used.
  map {c = False} f p = SeqEmpty p (Empty . f)

||| Sequence a grammar with value type `a -> b` and a grammar
||| with value type `a`. If both succeed, apply the function
||| from the first grammar to the value from the second grammar.
||| Guaranteed to consume if either grammar consumes.
export
(<*>) : Grammar tok c1 (a -> b) ->
        Grammar tok c2 a ->
        Grammar tok (c1 || c2) b
(<*>) x y = SeqEmpty x (\f => map f y)

||| Sequence two grammars. If both succeed, use the value of the first one.
||| Guaranteed to consume if either grammar consumes.
export
(<*) : Grammar tok c1 a ->
       Grammar tok c2 b ->
       Grammar tok (c1 || c2) a
(<*) x y = map const x <*> y

||| Sequence two grammars. If both succeed, use the value of the second one.
||| Guaranteed to consume if either grammar consumes.
export
(*>) : Grammar tok c1 a ->
       Grammar tok c2 b ->
       Grammar tok (c1 || c2) b
(*>) x y = map (const id) x <*> y

||| Produce a grammar that can parse a different type of token by providing a
||| function converting the new token type into the original one.
export
mapToken : (a -> b) -> Grammar b c ty -> Grammar a c ty
mapToken f (Empty val) = Empty val
mapToken f (Terminal g) = Terminal (g . f)
mapToken f (NextIs g) = SeqEmpty (NextIs (g . f)) (Empty . f)
mapToken f EOF = EOF
mapToken f (Fail msg) = Fail msg
mapToken f Commit = Commit
mapToken f (SeqEat act next) = SeqEat (mapToken f act) (\x => mapToken f (next x))
mapToken f (SeqEmpty act next) = SeqEmpty (mapToken f act) (\x => mapToken f (next x))
mapToken f (Alt x y) = Alt (mapToken f x) (mapToken f y)

||| Always succeed with the given value.
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

-- Take the result of an alternative branch, reset the commit flag to
-- the commit flag from the outer alternative, and weaken the 'consumes'
-- flag to take both alternatives into account
weakenRes : {whatever, c : Bool} -> {xs : List tok} ->
            (com' : Bool) ->
						ParseResult xs c ty -> ParseResult xs (whatever && c) ty
weakenRes com' (Failure com msg ts) = Failure com' msg ts
weakenRes {whatever=True} com' (EmptyRes com val xs) = EmptyRes com' val xs
weakenRes {whatever=False} com' (EmptyRes com val xs) = EmptyRes com' val xs
weakenRes com' (NonEmptyRes com val more) = NonEmptyRes com' val more

shorter : (more : List tok) -> .(ys : List tok) ->
          LTE (S (length more)) (S (length (ys ++ more)))
shorter more [] = lteRefl
shorter more (x :: xs) = LTESucc (lteSuccLeft (shorter more xs))

doParse : {c : Bool} ->
          (commit : Bool) -> (xs : List tok) -> (act : Grammar tok c ty) ->
          ParseResult xs c ty
doParse com xs act with (sizeAccessible xs)
  doParse com xs (Empty val) | sml = EmptyRes com val xs
  doParse com [] (Fail str) | sml = Failure com str []
  doParse com (x :: xs) (Fail str) | sml = Failure com str (x :: xs)
  doParse com xs Commit | sml = EmptyRes True () xs

  doParse com [] (Terminal f) | sml = Failure com "End of input" []
  doParse com (x :: xs) (Terminal f) | sml
        = maybe
             (Failure com "Unrecognised token" (x :: xs))
             (\a => NonEmptyRes com {xs=[]} a xs)
             (f x)
  doParse com [] EOF | sml = EmptyRes com () []
  doParse com (x :: xs) EOF | sml
        = Failure com "Expected end of input" (x :: xs)
  doParse com [] (NextIs f) | sml = Failure com "End of input" []
  doParse com (x :: xs) (NextIs f) | sml
        = if f x
             then EmptyRes com x (x :: xs)
             else Failure com "Unrecognised token" (x :: xs)
  doParse com xs (Alt x y) | sml with (doParse False xs x | sml)
    doParse com xs (Alt x y) | sml | Failure com' msg ts
          = if com' -- If the alternative had committed, don't try the
                    -- other branch (and reset commit flag)
               then Failure com msg ts
               else weakenRes com (doParse False xs y | sml)
    -- Successfully parsed the first option, so use the outer commit flag
    doParse com xs (Alt x y) | sml | (EmptyRes _ val xs)
          = EmptyRes com val xs
    doParse com (z :: (ys ++ more)) (Alt x y) | sml | (NonEmptyRes _ val more)
          = NonEmptyRes com val more
  doParse com xs (SeqEmpty act next) | (Access morerec)
          = case doParse com xs act | Access morerec of
                 Failure com msg ts => Failure com msg ts
                 EmptyRes com val xs =>
                       case doParse com xs (next val) | (Access morerec) of
                            Failure com' msg ts => Failure com' msg ts
                            EmptyRes com' val xs => EmptyRes com' val xs
                            NonEmptyRes com' val more => NonEmptyRes com' val more
                 NonEmptyRes {x} {xs=ys} com val more =>
                       case (doParse com more (next val) | morerec _ (shorter more ys)) of
                            Failure com' msg ts => Failure com' msg ts
                            EmptyRes com' val _ => NonEmptyRes com' val more
                            NonEmptyRes {x=x1} {xs=xs1} com' val more' =>
                                 rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                                         NonEmptyRes com' val more'
  doParse com xs (SeqEat act next) | sml with (doParse com xs act | sml)
    doParse com xs (SeqEat act next) | sml | Failure com' msg ts
         = Failure com' msg ts
    doParse com (x :: (ys ++ more)) (SeqEat act next) | (Access morerec) | (NonEmptyRes com' val more)
         = case doParse com' more (next val) | morerec _ (shorter more ys) of
                Failure com' msg ts => Failure com' msg ts
                EmptyRes com' val _ => NonEmptyRes com' val more
                NonEmptyRes {x=x1} {xs=xs1} com' val more' =>
                     rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                             NonEmptyRes com' val more'
  -- This next line is not strictly necessary, but it stops the coverage
  -- checker taking a really long time and eating lots of memory...
  doParse _ _ _ | sml = Failure True "Help the coverage checker!" []

public export
data ParseError tok = Error String (List tok)

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : (act : Grammar tok c ty) -> (xs : List tok) ->
        Either (ParseError tok) (ty, List tok)
parse act xs
    = case doParse False xs act of
           Failure _ msg ts => Left (Error msg ts)
           EmptyRes _ val rest => pure (val, rest)
           NonEmptyRes _ val rest => pure (val, rest)

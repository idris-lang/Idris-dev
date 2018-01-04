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
data GrammarT : (state : Type) -> (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> GrammarT st tok False ty
     Terminal : (tok -> Maybe a) -> GrammarT st tok True a
     NextIs : (tok -> Bool) -> GrammarT st tok False tok
     EOF : GrammarT st tok False ()

     Fail : String -> GrammarT st tok c ty
     Commit : GrammarT st tok False ()

     SeqEat : GrammarT st tok True a -> Inf (a -> GrammarT st tok c2 b) ->
              GrammarT st tok True b
     SeqEmpty : {c1, c2 : Bool} ->
                GrammarT st tok c1 a -> (a -> GrammarT st tok c2 b) ->
                GrammarT st tok (c1 || c2) b
     Alt : {c1, c2 : Bool} ->
           GrammarT st tok c1 ty -> GrammarT st tok c2 ty ->
           GrammarT st tok (c1 && c2) ty

     Get : GrammarT st tok False st
     Put : st -> GrammarT st tok False ()


public export
Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type
Grammar tok consumes ty = GrammarT () tok consumes ty

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
export %inline
(>>=) : {c1 : Bool} ->
        GrammarT st tok c1 a ->
        inf c1 (a -> GrammarT st tok c2 b) ->
        GrammarT st tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True} = SeqEat

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume input. This is an explicitly non-infinite version
||| of `>>=`.
export
seq : GrammarT st tok c1 a ->
      (a -> GrammarT st tok c2 b) ->
      GrammarT st tok (c1 || c2) b
seq = SeqEmpty

||| Sequence a grammar followed by the grammar it returns.
export
join : {c1 : Bool} ->
       GrammarT st tok c1 (GrammarT st tok c2 a) ->
       GrammarT st tok (c1 || c2) a
join {c1 = False} p = SeqEmpty p id
join {c1 = True} p = SeqEat p id

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export
(<|>) : GrammarT st tok c1 ty ->
        GrammarT st tok c2 ty ->
        GrammarT st tok (c1 && c2) ty
(<|>) = Alt

||| Allows the result of a grammar to be mapped to a different value.
export
Functor (GrammarT st tok c) where
  map f (Empty val)  = Empty (f val)
  map f (Fail msg)   = Fail msg
  map f (Terminal g) = Terminal (\t => map f (g t))
  map f (Alt x y)    = Alt (map f x) (map f y)
  map f (SeqEat act next)
      = SeqEat act (\val => map f (next val))
  map f (SeqEmpty act next)
      = SeqEmpty act (\val => map f (next val))
  -- The remaining constructors (NextIs, EOF, Commit, Get, Put) have a fixed type,
  -- so a sequence must be used.
  map {c = False} f p = SeqEmpty p (Empty . f)

||| Sequence a grammar with value type `a -> b` and a grammar
||| with value type `a`. If both succeed, apply the function
||| from the first grammar to the value from the second grammar.
||| Guaranteed to consume if either grammar consumes.
export
(<*>) : GrammarT st tok c1 (a -> b) ->
        GrammarT st tok c2 a ->
        GrammarT st tok (c1 || c2) b
(<*>) x y = SeqEmpty x (\f => map f y)

||| Sequence two grammars. If both succeed, use the value of the first one.
||| Guaranteed to consume if either grammar consumes.
export
(<*) : GrammarT st tok c1 a ->
       GrammarT st tok c2 b ->
       GrammarT st tok (c1 || c2) a
(<*) x y = map const x <*> y

||| Sequence two grammars. If both succeed, use the value of the second one.
||| Guaranteed to consume if either grammar consumes.
export
(*>) : GrammarT st tok c1 a ->
       GrammarT st tok c2 b ->
       GrammarT st tok (c1 || c2) b
(*>) x y = map (const id) x <*> y

||| Produce a grammar that can parse a different type of token by providing a
||| function converting the new token type into the original one.
export
mapToken : (a -> b) -> GrammarT st b c ty -> GrammarT st a c ty
mapToken f (Empty val) = Empty val
mapToken f (Terminal g) = Terminal (g . f)
mapToken f (NextIs g) = SeqEmpty (NextIs (g . f)) (Empty . f)
mapToken f EOF = EOF
mapToken f (Fail msg) = Fail msg
mapToken f Commit = Commit
mapToken f (SeqEat act next) = SeqEat (mapToken f act) (\x => mapToken f (next x))
mapToken f (SeqEmpty act next) = SeqEmpty (mapToken f act) (\x => mapToken f (next x))
mapToken f (Alt x y) = Alt (mapToken f x) (mapToken f y)
mapToken f Get = Get
mapToken f (Put x) = Put x

||| Always succeed with the given value.
export
pure : (val : ty) -> GrammarT st tok False ty
pure = Empty

||| Check whether the next token satisfies a predicate
export
nextIs : (tok -> Bool) -> GrammarT st tok False tok
nextIs = NextIs

||| Look at the next token in the input
export
peek : GrammarT st tok False tok
peek = nextIs (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export
terminal : (tok -> Maybe a) -> GrammarT st tok True a
terminal = Terminal

||| Always fail with a message
export
fail : String -> GrammarT st tok c ty
fail = Fail

||| Succeed if the input is empty
export
eof : GrammarT st tok False ()
eof = EOF

||| Commit to an alternative; if the current branch of an alternative
||| fails to parse, no more branches will be tried
export
commit : GrammarT st tok False ()
commit = Commit

||| Get the current parser state.
export
get : GrammarT st tok False st
get = Get

||| Write a new state.
export
put : st -> GrammarT st tok False ()
put = Put

||| Modify the state.
export
modify : (st -> st) -> GrammarT st tok False ()
modify f = put (f !get)

||| Evaluate a function in the context of this grammar's state.
export
gets : (st -> a) -> GrammarT st tok False a
gets f = pure (f !get)

data ParseResult : (st : Type) -> List tok -> (consumes : Bool) -> Type -> Type where
     Failure : {xs : List tok} ->
               (state : st) ->
               (committed : Bool) ->
               (err : String) -> (rest : List tok) -> ParseResult st xs c ty
     EmptyRes : (state : st) ->
                (committed : Bool) ->
                (val : ty) -> (more : List tok) -> ParseResult st more False ty
     NonEmptyRes : (state : st) ->
                   (committed : Bool) ->
                   (val : ty) -> (more : List tok) ->
                   ParseResult st (x :: xs ++ more) c ty

-- Take the result of an alternative branch, reset the commit flag to
-- the commit flag from the outer alternative, and weaken the 'consumes'
-- flag to take both alternatives into account
weakenRes : {whatever, c : Bool} -> {xs : List tok} ->
            (com' : Bool) ->
						ParseResult st xs c ty -> ParseResult st xs (whatever && c) ty
weakenRes com' (Failure state com msg ts) = Failure state com' msg ts
weakenRes {whatever=True} com' (EmptyRes state com val xs) = EmptyRes state com' val xs
weakenRes {whatever=False} com' (EmptyRes state com val xs) = EmptyRes state com' val xs
weakenRes com' (NonEmptyRes state com val more) = NonEmptyRes state com' val more

shorter : (more : List tok) -> .(ys : List tok) ->
          LTE (S (length more)) (S (length (ys ++ more)))
shorter more [] = lteRefl
shorter more (x :: xs) = LTESucc (lteSuccLeft (shorter more xs))

doParse : {c : Bool} ->
          (state : st) ->
          (commit : Bool) -> (xs : List tok) -> (act : GrammarT st tok c ty) ->
          ParseResult st xs c ty
doParse state com xs act with (sizeAccessible xs)
  doParse state com xs Get | sml = EmptyRes state com state xs
  doParse state com xs (Put newState) | sml = EmptyRes newState com () xs
  doParse state com xs (Empty val) | sml = EmptyRes state com val xs
  doParse state com [] (Fail str) | sml = Failure state com str []
  doParse state com (x :: xs) (Fail str) | sml = Failure state com str (x :: xs)
  doParse state com xs Commit | sml = EmptyRes state True () xs

  doParse state com [] (Terminal f) | sml = Failure state com "End of input" []
  doParse state com (x :: xs) (Terminal f) | sml
        = maybe
             (Failure state com "Unrecognised token" (x :: xs))
             (\a => NonEmptyRes state com {xs=[]} a xs)
             (f x)
  doParse state com [] EOF | sml = EmptyRes state com () []
  doParse state com (x :: xs) EOF | sml
        = Failure state com "Expected end of input" (x :: xs)
  doParse state com [] (NextIs f) | sml = Failure state com "End of input" []
  doParse state com (x :: xs) (NextIs f) | sml
        = if f x
             then EmptyRes state com x (x :: xs)
             else Failure state com "Unrecognised token" (x :: xs)
  doParse state com xs (Alt x y) | sml with (doParse state False xs x | sml)
    doParse state com xs (Alt x y) | sml | Failure state' com' msg ts
          = if com' -- If the alternative had committed, don't try the
                    -- other branch (and reset commit flag)
               then Failure state' com msg ts
               else weakenRes com (doParse state False xs y | sml)
    -- Successfully parsed the first option, so use the outer commit flag
    doParse state com xs (Alt x y) | sml | (EmptyRes state' _ val xs)
          = EmptyRes state' com val xs
    doParse state com (z :: (ys ++ more)) (Alt x y) | sml | (NonEmptyRes state' _ val more)
          = NonEmptyRes state' com val more
  doParse state com xs (SeqEmpty act next) | (Access morerec)
          = case doParse state com xs act | Access morerec of
                 Failure state' com msg ts => Failure state' com msg ts
                 EmptyRes state' com val xs =>
                       case doParse state' com xs (next val) | (Access morerec) of
                            Failure state'' com' msg ts => Failure state'' com' msg ts
                            EmptyRes state'' com' val xs => EmptyRes state'' com' val xs
                            NonEmptyRes state'' com' val more => NonEmptyRes state'' com' val more
                 NonEmptyRes state' {x} {xs=ys} com val more =>
                       case (doParse state' com more (next val) | morerec _ (shorter more ys)) of
                            Failure state'' com' msg ts => Failure state'' com' msg ts
                            EmptyRes state'' com' val _ => NonEmptyRes state'' com' val more
                            NonEmptyRes state'' {x=x1} {xs=xs1} com' val more' =>
                                 rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                                         NonEmptyRes state'' com' val more'
  doParse state com xs (SeqEat act next) | sml with (doParse state com xs act | sml)
    doParse state com xs (SeqEat act next) | sml | Failure state' com' msg ts
         = Failure state' com' msg ts
    doParse state com (x :: (ys ++ more)) (SeqEat act next) | (Access morerec) | (NonEmptyRes state' com' val more)
         = case doParse state' com' more (next val) | morerec _ (shorter more ys) of
                Failure state'' com' msg ts => Failure state'' com' msg ts
                EmptyRes state'' com' val _ => NonEmptyRes state'' com' val more
                NonEmptyRes state'' {x=x1} {xs=xs1} com' val more' =>
                     rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                             NonEmptyRes state'' com' val more'
  -- This next line is not strictly necessary, but it stops the coverage
  -- checker taking a really long time and eating lots of memory...
  doParse state _ _ _ | sml = Failure state True "Help the coverage checker!" []

public export
data ParseError tok = Error String (List tok)

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parseState : (act : GrammarT st tok c ty) -> 
          (initial : st) ->
          (xs : List tok) ->
          Either (ParseError tok) (ty, List tok)
parseState act initial xs
    = case doParse initial False xs act of
           Failure _ _ msg ts => Left (Error msg ts)
           EmptyRes _ _ val rest => pure (val, rest)
           NonEmptyRes _ _ val rest => pure (val, rest)

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : (act : Grammar tok c ty) ->
        (xs : List tok) ->
        Either (ParseError tok) (ty, List tok)
parse act = parseState act ()

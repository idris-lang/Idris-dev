module Text.Parser

import Data.Bool.Extra

import public Text.Parser.Core

%access export
%default total

||| Optionally parse a thing, with a default value if the grammar doesn't
||| match. May match the empty input.
option : {c : Bool} ->
         (def : a) -> (p : Grammar tok c a) ->
         Grammar tok False a
option {c} def p = rewrite sym (andFalseFalse c) in
                           p <|> pure def

||| Optionally parse a thing.
||| To provide a default value, use `option` instead.
optional : (p : Grammar tok c a) ->
           Grammar tok False (Maybe a)
optional p = option Nothing (map Just p)

||| Try each grammar in a container until the first one succeeds.
||| Fails if the container is empty.
choice : {c : Bool} ->
         Foldable t => t (Grammar tok c a) ->
         Grammar tok c a
choice {c} xs = foldr (\x, acc => rewrite sym (andSameNeutral c) in
                                          x <|> acc)
                      (fail "No more options") xs

mutual
  ||| Parse one or more things
  some : Grammar tok True a ->
         Grammar tok True (List a)
  some p = pure (!p :: !(many p))

  ||| Parse zero or more things (may match the empty input)
  many : Grammar tok True a ->
         Grammar tok False (List a)
  many p = option [] (some p)

||| Parse one or more instances of `p`, returning the parsed items and proof
||| that the resulting list is non-empty.
some' : (p : Grammar tok True a) ->
        Grammar tok True (xs : List a ** NonEmpty xs)
some' p = pure (!p :: !(many p) ** IsNonEmpty)

||| Parse one or more things, each separated by another thing.
sepBy1 : {c : Bool} ->
         (sep : Grammar tok True s) ->
         (p : Grammar tok c a) ->
         Grammar tok c (List a)
sepBy1 {c} sep p = rewrite sym (orFalseNeutral c) in
                           [| p :: many (sep *> p) |]

||| Parse zero or more things, each separated by another thing. May
||| match the empty input.
sepBy : (sep : Grammar tok True s) ->
        (p : Grammar tok c a) ->
        Grammar tok False (List a)
sepBy sep p = option [] $ sepBy1 sep p

||| Parse one or more instances of `p` separated by `sep`, returning the
||| parsed items and proof that the resulting list is non-empty.
sepBy1' : {c : Bool} ->
         (sep : Grammar tok True s) ->
         (p : Grammar tok c a) ->
         Grammar tok c (xs : List a ** NonEmpty xs)
sepBy1' {c} sep p
  = rewrite sym (orFalseNeutral c) in
            seq p (\x => do xs <- many (sep *> p)
                            pure (x :: xs ** IsNonEmpty))

||| Parse an instance of `p` that is between `left` and `right`.
between : (left : Grammar tok True l) ->
          (right : Grammar tok True r) ->
          (p : Grammar tok c a) ->
          Grammar tok True a
between left right contents = left *> contents <* right

module Text.Parser

import Data.Bool.Extra

import public Text.Parser.Core
import public Text.Quantity
import public Text.Token

%access export
%default total

||| Parse a terminal based on a kind of token.
match : (Eq k, TokenKind k) =>
        (kind : k) ->
        Grammar (Token k) True (TokType kind)
match kind = terminal $
  \(Tok kind' text) => if kind' == kind
                          then Just $ tokValue kind text
                          else Nothing

||| Optionally parse a thing, with a default value if the grammar doesn't
||| match. May match the empty input.
option : {c : Bool} ->
         (def : a) -> (p : Grammar tok c a) ->
         Grammar tok False a
option {c = False} def p = p <|> pure def
option {c = True} def p = p <|> pure def

||| Optionally parse a thing.
||| To provide a default value, use `option` instead.
optional : (p : Grammar tok c a) ->
           Grammar tok False (Maybe a)
optional p = option Nothing (map Just p)

||| Try to parse one thing or the other, producing a value that indicates
||| which option succeeded. If both would succeed, the left option
||| takes priority.
choose : (l : Grammar tok c1 a) ->
         (r : Grammar tok c2 b) ->
         Grammar tok (c1 && c2) (Either a b)
choose l r = map Left l <|> map Right r

||| Produce a grammar by applying a function to each element of a container,
||| then try each resulting grammar until the first one succeeds. Fails if the
||| container is empty.
choiceMap : {c : Bool} ->
            (a -> Grammar tok c b) ->
            Foldable t => t a ->
            Grammar tok c b
choiceMap {c} f xs = foldr (\x, acc => rewrite sym (andSameNeutral c) in
                                               f x <|> acc)
                           (fail "No more options") xs

||| Try each grammar in a container until the first one succeeds.
||| Fails if the container is empty.
choice : Foldable t => t (Grammar tok c a) ->
         Grammar tok c a
choice = choiceMap id

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

mutual
  private
  count1 : (q : Quantity) ->
           (p : Grammar tok True a) ->
           Grammar tok True (List a)
  count1 q p = do x <- p
                  seq (count q p)
                      (\xs => pure (x :: xs))

  ||| Parse `p`, repeated as specified by `q`, returning the list of values.
  count : (q : Quantity) ->
          (p : Grammar tok True a) ->
          Grammar tok (isSucc (min q)) (List a)
  count (Qty Z Nothing) p = many p
  count (Qty Z (Just Z)) _ = pure []
  count (Qty Z (Just (S max))) p = option [] $ count1 (atMost max) p
  count (Qty (S min) Nothing) p = count1 (atLeast min) p
  count (Qty (S min) (Just Z)) _ = fail "Quantity out of order"
  count (Qty (S min) (Just (S max))) p = count1 (between (S min) max) p

mutual
  ||| Parse one or more instances of `p` until `end` succeeds, returning the
  ||| list of values from `p`. Guaranteed to consume input.
  someTill : {c : Bool} ->
             (end : Grammar tok c e) ->
             (p : Grammar tok True a) ->
             Grammar tok True (List a)
  someTill {c} end p = do x <- p
                          seq (manyTill end p)
                              (\xs => pure (x :: xs))

  ||| Parse zero or more instances of `p` until `end` succeeds, returning the
  ||| list of values from `p`. Guaranteed to consume input if `end` consumes.
  manyTill : {c : Bool} ->
             (end : Grammar tok c e) ->
             (p : Grammar tok True a) ->
             Grammar tok c (List a)
  manyTill {c} end p = rewrite sym (andTrueNeutral c) in
                               map (const []) end <|> someTill end p

||| Parse one or more instances of `p` until `end` succeeds, returning the
||| list of values from `p`, along with a proof that the resulting list is
||| non-empty.
someTill' : {c : Bool} ->
            (end : Grammar tok c e) ->
            (p : Grammar tok True a) ->
            Grammar tok True (xs : List a ** NonEmpty xs)
someTill' end p
  = do x <- p
       seq (manyTill end p)
           (\xs => pure (x :: xs ** IsNonEmpty))

mutual
  ||| Parse one or more instance of `skip` until `p` is encountered,
  ||| returning its value.
  afterSome : (skip : Grammar tok True s) ->
              (p : Grammar tok c a) ->
              Grammar tok True a
  afterSome skip p = do skip
                        afterMany skip p

  ||| Parse zero or more instance of `skip` until `p` is encountered,
  ||| returning its value.
  afterMany : {c : Bool} ->
              (skip : Grammar tok True s) ->
              (p : Grammar tok c a) ->
              Grammar tok c a
  afterMany {c} skip p = rewrite sym (andTrueNeutral c) in
                                 p <|> afterSome skip p

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

||| Parse one or more instances of `p` separated by and optionally terminated by
||| `sep`.
sepEndBy1 : {c : Bool} ->
            (sep : Grammar tok True s) ->
            (p : Grammar tok c a) ->
            Grammar tok c (List a)
sepEndBy1 {c} sep p = rewrite sym (orFalseNeutral c) in
                              sepBy1 sep p <* optional sep

||| Parse zero or more instances of `p`, separated by and optionally terminated
||| by `sep`. Will not match a separator by itself.
sepEndBy : (sep : Grammar tok True s) ->
           (p : Grammar tok c a) ->
           Grammar tok False (List a)
sepEndBy sep p = option [] $ sepEndBy1 sep p

||| Parse zero or more instances of `p`, separated by and optionally terminated
||| by `sep`, returning the parsed items and a proof that the resulting list
||| is non-empty.
sepEndBy1' : {c : Bool} ->
             (sep : Grammar tok True s) ->
             (p : Grammar tok c a) ->
             Grammar tok c (xs : List a ** NonEmpty xs)
sepEndBy1' {c} sep p = rewrite sym (orFalseNeutral c) in
                               sepBy1' sep p <* optional sep

||| Parse one or more instances of `p`, separated and terminated by `sep`.
endBy1 : {c : Bool} ->
         (sep : Grammar tok True s) ->
         (p : Grammar tok c a) ->
         Grammar tok True (List a)
endBy1 {c} sep p = some $ rewrite sym (orTrueTrue c) in
                                  p <* sep

endBy : (sep : Grammar tok True s) ->
        (p : Grammar tok c a) ->
        Grammar tok False (List a)
endBy sep p = option [] $ endBy1 sep p

||| Parse zero or more instances of `p`, separated and terminated by `sep`,
||| returning the parsed items and a proof that the resulting list is non-empty.
endBy1' : {c : Bool} ->
          (sep : Grammar tok True s) ->
          (p : Grammar tok c a) ->
          Grammar tok True (xs : List a ** NonEmpty xs)
endBy1' {c} sep p = some' $ rewrite sym (orTrueTrue c) in
                                    p <* sep

||| Parse an instance of `p` that is between `left` and `right`.
between : (left : Grammar tok True l) ->
          (right : Grammar tok True r) ->
          (p : Grammar tok c a) ->
          Grammar tok True a
between left right contents = left *> contents <* right

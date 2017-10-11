module Text.Parser

import Text.Parser.Core

%default total

mutual
  ||| Parse one or more things
  export
  some : Grammar tok True a ->
         Grammar tok True (List a)
  some p = pure (!p :: !(many p))

  ||| Parse zero or more things (may match the empty input)
  export
  many : Grammar tok True a ->
         Grammar tok False (List a)
  many p = some p <|> pure []

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

||| Fold over a list of grammars until the first one succeeds.
choice : Foldable t => t (Grammar tok True a) -> Grammar tok True a
choice xs = foldr (<|>) (fail "No more options") xs

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

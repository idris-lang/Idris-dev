module Data.List.Extra

%default total
%access export

||| The final segment of the accumulator is the final segment of the result.
reverseOntoAcc : (xs, ys, zs : List a) ->
  reverseOnto (ys ++ zs) xs = (reverseOnto ys xs) ++ zs
reverseOntoAcc [] _ _ = Refl
reverseOntoAcc (x :: xs) (ys) (zs) = reverseOntoAcc xs (x :: ys) zs

||| Serves as a specification for reverseOnto.
reverseOntoSpec : (xs, ys : List a) -> reverseOnto xs ys = reverse ys ++ xs
reverseOntoSpec xs ys = reverseOntoAcc ys [] xs

||| The reverse of an empty list is an empty list.  Together with reverseCons,
||| serves as a specification for reverse.
reverseNil : reverse [] = []
reverseNil = Refl

||| The reverse of a cons is the reverse of the tail followed by the head.
||| Together with reverseNil serves as a specification for reverse.
reverseCons : (x : a) -> (xs : List a) -> reverse (x::xs) = reverse xs ++ [x]
reverseCons x xs = reverseOntoSpec [x] xs

||| Reversing an append is appending reversals backwards.
reverseAppend : (xs, ys : List a) ->
  reverse (xs ++ ys) = reverse ys ++ reverse xs
reverseAppend [] ys = sym (appendNilRightNeutral (reverse ys))
reverseAppend (x :: xs) ys =
  rewrite reverseCons x (xs ++ ys) in
    rewrite reverseAppend xs ys in
      rewrite reverseCons x xs in
        sym $ appendAssociative (reverse ys) (reverse xs) [x]

||| Reversing a singleton list is a no-op.
reverseSingletonId : (x : a) -> reverse [x] = [x]
reverseSingletonId _ = Refl

||| Reversing a reverse gives the original.
reverseReverseId : (xs : List a) -> reverse (reverse xs) = xs
reverseReverseId [] = Refl
reverseReverseId (x :: xs) =
  rewrite reverseCons x xs in
    rewrite reverseAppend (reverse xs) [x] in
      cong $ reverseReverseId xs

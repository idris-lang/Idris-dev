module Data.List.Extra

%default total
%access export

||| Serves as a specification for reverseOnto.
reverseOntoSpec : (xs, ys : List a) -> reverseOnto xs ys = reverse ys ++ xs
reverseOntoSpec _  [] = Refl
reverseOntoSpec xs (y::ys) =
  trans (reverseOntoSpec (y::xs) ys)
        (trans (appendAssociative (reverse ys) [y] xs)
               (cong {f = \l => l ++ xs} (sym (reverseOntoSpec [y] ys))))

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
  trans (trans (reverseCons x (xs ++ ys))
               (cong {f = \l => l ++ [x]} (reverseAppend xs ys)))
        (sym (trans (cong (reverseCons x xs))
                    (appendAssociative (reverse ys) (reverse xs) [x])))

||| Reversing a singleton list is a no-op.
reverseSingletonId : (x : a) -> reverse [x] = [x]
reverseSingletonId _ = Refl

||| Reversing a reverse gives the original.
reverseReverseId : (xs : List a) -> reverse (reverse xs) = xs
reverseReverseId [] = Refl
reverseReverseId (x :: xs) =
  trans (cong (reverseCons x xs))
        (trans (reverseAppend (reverse xs) [x])
               (cong (reverseReverseId xs)))

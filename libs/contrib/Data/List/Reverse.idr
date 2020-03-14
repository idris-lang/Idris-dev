||| Properties of the reverse function.
module Data.List.Reverse

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

||| A recursive definition of reverse.
reverseRec : List a -> List a
reverseRec [] = []
reverseRec (x :: xs) = reverseRec xs ++ [x]

||| The iterative and recursive defintions of reverse are the same.
reverseEquiv : (xs : List a) -> reverseRec xs = reverse xs
reverseEquiv [] = Refl
reverseEquiv (x :: xs) =
  rewrite reverseEquiv xs in
    rewrite reverseAppend [x] xs in
      Refl

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

||| Reversing onto preserves list length.
reverseOntoLength : (xs, acc : List a) ->
  length $ reverseOnto acc xs = length acc + length xs
reverseOntoLength [] acc = rewrite plusZeroRightNeutral (length acc) in Refl
reverseOntoLength (x :: xs) acc =
  rewrite reverseOntoLength xs (x :: acc) in
    plusSuccRightSucc (length acc) (length xs)

||| Reversing preserves list length.
reverseLength : (xs : List a) -> length $ reverse xs = length xs
reverseLength xs = reverseOntoLength xs []

||| Equal reversed lists are equal.
reverseEqual : (xs, ys : List a) -> reverse xs = reverse ys -> xs = ys
reverseEqual xs ys prf =
  rewrite sym $ reverseReverseId xs in
    rewrite prf in
      reverseReverseId ys

||| Do geese see God?
data Palindrome : (xs : List a) -> Type where
  Empty : Palindrome []
  Single : Palindrome [_]
  Multi : Palindrome xs -> Palindrome $ [x] ++ xs ++ [x]

||| A Palindrome reversed is itself.
palindromeReverse : (xs : List a) -> Palindrome xs -> reverse xs = xs
palindromeReverse [] Empty = Refl
palindromeReverse [_] Single = Refl
palindromeReverse ([x] ++ ys ++ [x]) (Multi pf) =
  rewrite reverseAppend ([x] ++ ys) [x] in
    rewrite reverseAppend [x] ys in
      rewrite palindromeReverse ys pf in
        Refl

||| Only Palindromes are equal to their own reverse.
postulate  -- This is a tough one. Any takers?
reversePalindrome : (xs : List a) -> reverse xs = xs -> Palindrome xs

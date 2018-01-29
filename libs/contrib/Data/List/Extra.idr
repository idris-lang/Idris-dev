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

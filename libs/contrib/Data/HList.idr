||| A heterogenous list
module Data.HList

%access public export

data HList : List Type -> Type where
    Nil : HList []
    (::) : a -> HList xs -> HList (a :: xs)

||| Extract an element from an HList
index : (i : Nat) -> HList ts -> {auto ok : InBounds i ts } -> List.index i ts
index Z (x::xs) {ok} = x
index (S j) (x::xs) {ok = InLater p}= index j xs

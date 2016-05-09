module Set
 
public export
interface SetSig a where
  data Set : Type -> Type where MkSet : List a -> Set a

  new : Set a
  insert : a -> Set a -> Set a
  member : a -> Set a -> Bool

data Tree a = Leaf | Node (Tree a) a (Tree a)

mkTree : Type -> Type
mkTree = Tree

namespace TreeSet
  export
  [TreeSet] Ord a => SetSig a where

    Set = Tree 

    new = Leaf

    insert x Leaf = Node Leaf x Leaf
    insert x (Node l val r) = case compare x val of
                                   LT => Node (insert x l) val r
                                   EQ => Node l val r
                                   GT => Node l val (insert x r)

    member x Leaf = False
    member x (Node l val r) = case compare x val of
                                   LT => member x l
                                   EQ => True
                                   GT => member x r

using implementation TreeSet

  test : Set @{TreeSet {a=Nat}} Nat
  test = insert 3 $ 
         insert 2 $ 
         insert 7 $ 
         insert 3 $ 
         insert 4 $ 
         insert 5 new 

  foo : Bool
  foo = member 6 test

  bar : Bool
  bar = member 3 test

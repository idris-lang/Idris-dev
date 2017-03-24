module Set
 
public export
interface SetSig a where
  data SetT : Type -> Type

  new : SetT a
  insert : a -> SetT a -> SetT a
  member : a -> SetT a -> Bool

Set : (a : Type) -> SetSig a => Type
Set (a) @{sig} = SetT @{sig} a

data Tree a = Leaf | Node (Tree a) a (Tree a)

mkTree : Type -> Type
mkTree = Tree

namespace TreeSet
  export
  [TreeSet] Ord a => SetSig a where

    SetT = Tree 

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

  test : Set Nat
  test = -- insert (the Nat 3) $ 
--          insert 2 $ 
--          insert 7 $ 
--          insert 3 $ 
--          insert 4 $ 
        insert {a = Nat} (the Nat 5) new

  foo : Bool
  foo = member (the Nat 6) test

  bar : Bool
  bar = member (the Nat 3) test

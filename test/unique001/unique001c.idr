
data UList : Type -> UniqueType where
     UNil : UList a
     UCons : {a : Type} -> a -> UList a -> UList a

uapp : UList a -> UList a -> UList a
uapp UNil xs = xs
uapp (UCons x xs) ys = UCons x (UCons x (uapp xs ys))

data UTree : UniqueType where
     ULeaf : UTree
     UNode : UTree -> Int -> UTree -> UTree

data UPair : UniqueType -> UniqueType -> UniqueType where
  MkUPair : {a,b:UniqueType} -> a -> b -> UPair a b

dup : UTree -> UPair UTree UTree
dup ULeaf = MkUPair ULeaf ULeaf
dup (UNode l y r) = let MkUPair l1 l2 = dup l
                        MkUPair r1 r2 = dup r in
                        MkUPair (UNode l1 y r1) (UNode l2 y r2)

data Tree : Type where
     Leaf : Tree
     Node : Tree -> Int -> Tree -> Tree

share : UTree -> Tree
share ULeaf = Leaf
share (UNode x y z) = Node (share x) y (share z)

class UFunctor (f : Type -> Type*) where
    fmap : (a -> b) -> f a -> f b

instance UFunctor List where
    fmap f [] = []
    fmap f (x :: xs) = f x :: fmap f xs

instance UFunctor UList where
    fmap f UNil = UNil
    fmap f (UCons x xs) = UCons (f x) (fmap f xs)

uconst : {a : Type*} -> a -> b -> a
uconst x y = x

data MPair : Type* -> Type* -> Type* where
     MkMPair : {a, b : Type*} -> a -> b -> MPair a b

ndup : {a : UniqueType} -> a -> UPair a a
ndup {a} x = (\f : Int -> a => MkUPair (f 0) (f 1)) (uconst x)





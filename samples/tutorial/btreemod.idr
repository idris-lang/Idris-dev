module btree

abstract data BTree a = Leaf
                      | Node (BTree a) a (BTree a)

abstract
insert : Ord a => a -> BTree a -> BTree a
insert x Leaf = Node Leaf x Leaf
insert x (Node l v r) = if (x < v) then (Node (insert x l) v r)
                                   else (Node l v (insert x r))

abstract
toList : BTree a -> List a
toList Leaf = []
toList (Node l v r) = btree.toList l ++ (v :: btree.toList r)

abstract
toTree : Ord a => List a -> BTree a
toTree [] = Leaf
toTree (x :: xs) = insert x (toTree xs)

module Main

import Effects
import Effect.State

data BTree a = Leaf
             | Node (BTree a) a (BTree a)

implementation Show a => Show (BTree a) where
  show Leaf = "[]"
  show (Node l x r) = "[" ++ show l ++ " "
                          ++ show x ++ " "
                          ++ show r ++ "]"

testTree : BTree String
testTree = Node (Node Leaf "Jim" Leaf)
                "Fred"
                (Node (Node Leaf "Alice" Leaf)
                      "Sheila"
                      (Node Leaf "Bob" Leaf))

treeTagAux : BTree a -> { [STATE Int] } Eff (BTree (Int, a))
treeTagAux Leaf = pure Leaf
treeTagAux (Node l x r)
    = do l' <- treeTagAux l
         i <- get
         put (i + 1)
         r' <- treeTagAux r
         pure (Node l' (i, x) r')

treeTag : (i : Int) -> BTree a -> BTree (Int, a)
treeTag i x = runPure (do put i
                          treeTagAux x)

treeTagIO : (i : Int) -> BTree a -> IO (BTree (Int, a))
treeTagIO i x = run (do put i
                        treeTagAux x)

main : IO ()
main = print (treeTag 1 testTree)

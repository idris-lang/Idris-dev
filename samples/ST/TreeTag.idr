import Control.ST

data BTree a = Leaf
             | Node (BTree a) a (BTree a)

testTree : BTree String
testTree = Node (Node Leaf "Jim" Leaf)
                "Fred"
                (Node (Node Leaf "Alice" Leaf)
                      "Sheila"
                      (Node Leaf "Bob" Leaf))


treeTagAux : (tag : Var) -> BTree a -> ST m (BTree (Int, a)) [tag ::: State Int]
treeTagAux tag Leaf = pure Leaf
treeTagAux tag (Node left val right) 
    = do left' <- treeTagAux tag left
         thisTag <- read tag
         write tag (thisTag + 1)
         right' <- treeTagAux tag right
         pure (Node left' (thisTag, val) right')

treeTag : (i : Int) -> BTree a -> BTree (Int, a)
treeTag i tree = runPure (do tag <- new i
                             t <- treeTagAux tag tree
                             delete tag
                             pure t)
            


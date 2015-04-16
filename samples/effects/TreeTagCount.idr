import Effects
import Effect.State
import Effect.StdIO

data BTree a = Leaf
             | Node (BTree a) a (BTree a)

testTree : BTree String
testTree = Node (Node Leaf "Jim" Leaf)
                "Fred"
                (Node (Node Leaf "Alice" Leaf)
                      "Sheila"
                      (Node Leaf "Bob" Leaf))

treeTagAux : BTree a -> { ['Tag ::: STATE Int,
                           'Leaves ::: STATE Int] } Eff (BTree (Int, a))
treeTagAux Leaf = do 'Leaves :- update (+1)
                     pure Leaf
treeTagAux (Node l x r)
    = do l' <- treeTagAux l
         i <- 'Tag :- get
         'Tag :- put (i + 1)
         r' <- treeTagAux r
         pure (Node l' (i, x) r')

treeTag : (i : Int) -> BTree a -> (BTree (Int, a), Int)
treeTag i x = runPureInit ['Tag := i, 'Leaves := 0]
                         (do x' <- treeTagAux x
                             pure (x', !('Leaves :- get)))

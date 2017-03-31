module Main

import BTree

main : IO ()
main = do let t = toTree [1,8,2,7,9,3]
          printLn (btree.toList t)


module Main

import btree

main : UnsafeIO ()
main = do let t = toTree [1,8,2,7,9,3] 
          print (toList t)


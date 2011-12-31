module main;

import btree;

main : IO ();
main = do { let t = toTree [1,8,2,7,9,3]; 
            print (toList t);
          };


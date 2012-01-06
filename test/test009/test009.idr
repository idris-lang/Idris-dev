module main;

pythag : Int -> List (Int, Int, Int);
pythag n = do { z <- [1..n];
                y <- [1..z];
                x <- [1..y];
                if (x * x + y * y == z * z) then (return (x, y, z)) else [];
              };

main : IO ();
main = print (pythag 50);
      

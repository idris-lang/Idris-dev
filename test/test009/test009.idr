module main

pythag : Int -> List (Int, Int, Int)
pythag n = [ (x, y, z) | z <- [1..n], y <- [1..z], x <- [1..y],
                           x*x + y*y == z*z ]

main : IO ()
main = print (pythag 50)
      

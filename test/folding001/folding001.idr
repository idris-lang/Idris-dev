module Main

import Data.Vect

-- foldr (::) [] converts to lists
foldToList : (Foldable t) => t a -> List a
foldToList = foldr (::) [] 

showTestLine : List Int -> Vect n Int -> IO ()
showTestLine xs ys =
  putStrLn $ "(" ++ 
    show xs ++ ", " ++ 
    show ys ++ ") " ++ 
    "-> (" ++ 
    show (foldToList xs) ++ ", " ++ 
    show (foldToList ys) ++ ")"

main : IO ()
main = do
  showTestLine [] []
  showTestLine [1] [1]
  showTestLine [1, 2, 3] [1, 2, 3]
  showTestLine [3, 2, 1] [3, 2, 1]



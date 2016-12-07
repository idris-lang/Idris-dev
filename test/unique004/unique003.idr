module Main

%language UniquenessTypes

data UList : Type -> UniqueType where
     Nil   : UList a
     (::)  : a -> UList a -> UList a

showU : Show a => Borrowed (UList a) -> String
showU xs = "[" ++ showU' xs ++ "]" where
  showU' : Borrowed (UList a) -> String
  showU' [] = ""
  showU' [x] = show x
  showU' (x :: xs) = show x ++ ", " ++ showU' xs

free : {a : UniqueType} -> a -> String
free xs = ""

foo : UList Int -> IO ()
foo xs = do let f = \x : Int => showU xs -- can't build this in unique context
            putStrLn (f 10) 
            putStrLn $ free xs
            putStrLn (f 10) 
            pure ()

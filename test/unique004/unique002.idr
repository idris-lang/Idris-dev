data UList : Type -> UniqueType where
     Nil   : UList a
     (::)  : a -> UList a -> UList a

free : {a : UniqueType} -> a -> String
free xs = ""

showU : Show a => Borrowed (UList a) -> String
showU xs = "[" ++ showU' xs ++ "]" where
    showU' : Borrowed (UList a) -> String
    showU' [] = ""
    showU' (x :: xs) = show x ++ ", " ++ showU xs

foo : UList Int -> IO ()
foo xs = do -- let f = \x : Int => showU xs
            putStrLn $ free xs
            putStrLn $ f 42 xs
            return ()
    where f : Int -> Borrowed (UList Int) -> String
          f x xs = showU xs

module Main

%language UniquenessTypes

data UList : Type -> UniqueType where
     Nil   : UList a
     (::)  : a -> UList a -> UList a

umap : (a -> b) -> UList a -> UList b
umap f [] = []
umap f (x :: xs) = f x :: umap f xs

free : {a : UniqueType} -> a -> String
free xs = ""

showU : Show a => Borrowed (UList a) -> String
showU [] = "END"
showU (x :: xs) = show x ++ "," ++ showU xs

mkUList : Nat -> UList Int
mkUList Z = []
mkUList (S k) = cast k :: mkUList k

showStuff : UList Int -> IO ()
showStuff xs = do
          putStrLn (showU xs)
          putStrLn (showU xs)
          let xs' = umap (*2) xs
          putStrLn (showU xs')
          putStrLn (showU xs')

main : IO ()
main = showStuff (mkUList 20)


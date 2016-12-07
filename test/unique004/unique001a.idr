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

showIt : UList Int -> Int -> String
showIt xs x = let xs' = umap (*2) xs in ""

printThings : (Int -> String) -> IO ()
printThings f = do putStrLn (f 10)
                   putStrLn (f 20)

double : Int -> Int
double x = x * 2

showStuff : UList Int -> IO ()
showStuff xs = do
          putStrLn (showU xs)
          putStrLn (showU xs)
          -- xsFn gets a unique type since we're in a unique context
          -- now, but function built has a non-unique type
          (\xsFn : Int -> String =>
                   do putStrLn "Hello"
                      putStrLn (xsFn 42))
                (\dummy => showU (umap double xs))

showStuff' : UList Int -> IO ()
showStuff' xs = do
          putStrLn (showU xs)
          putStrLn (showU xs)
          -- xsFn gets a unique type since we're in a unique context
          -- now, but function built has a non-unique type
          let xsFn = \dummy : Int => showU (umap double xs)
          putStrLn "Hello"
          putStrLn (xsFn 42)
          putStrLn (xsFn 42)

showThings : UList Int -> IO ()
showThings xs = do
          putStrLn (showU xs)
          putStrLn (showU xs)
          -- showIt has a unique type, printThings wants a non-unique
          -- type
          printThings (showIt xs)



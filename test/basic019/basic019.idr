printRange : (t : Type) -> (Show t, Num t, Enum t) => IO ()
printRange t = do printLn [(the t 1)..10]
                  printLn [(the t 10),9..1]
                  printLn (take 10 [(the t 1)..])
                  printLn (take 10 [(the t 1),3..])

main : IO ()
main = do printRange Nat
          printRange Int
          printRange Integer

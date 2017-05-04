data InfIO : Type where
     Do : IO a -> (a -> Inf InfIO) -> InfIO

foo : InfIO
foo = Do (putStr "Foo") (\x => foo)

total
run : InfIO -> IO ()
run (Do x f) = do r <- x
                  run (f r)


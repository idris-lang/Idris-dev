module LazyExec

-- The regression that this tests for is broken laziness in the executor.

covering
countdown : Int -> Lazy (List Int)
countdown n = if n > 0
                 then (n :: countdown (n-1))
                 else []

go : IO ()
go = putStrLn $ show (Force (countdown 3))

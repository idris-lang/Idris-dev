module Main
-- Tests issue #2125 (divNat segfaults)
main : IO ()
main = do
    putStrLn $ show $ divNat 1809022195644390369852458 91238741987

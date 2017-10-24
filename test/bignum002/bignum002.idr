module Main

main : IO ()
main = do
    printLn $ divNat 1809022195644390369852458 91238741987
    printLn $ div (-432642342742368327462378462387) 36473264372

    -- values at the border between C ints and bignums
    printLn $ div 1073741822 73892
    printLn $ div 1073741823 73892
    printLn $ div 1073741824 73892
    printLn $ div (-1073741823) 73892
    printLn $ div (-1073741824) 73892
    printLn $ div (-1073741825) 73892

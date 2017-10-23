module basic024

namespace Main
  main : IO ()
  main = do
    printLn $ div (the Integer 5) 2
    printLn $ div (the Int 5) 2
    printLn $ div (the Bits8 5) 2
    printLn $ div (the Bits16 5) 2
    printLn $ div (the Bits32 5) 2
    printLn $ div (the Bits64 5) 2
    printLn $ div (the Nat 5) 2

    printLn $ mod (the Integer 5) 2
    printLn $ mod (the Int 5) 2
    printLn $ mod (the Bits8 5) 2
    printLn $ mod (the Bits16 5) 2
    printLn $ mod (the Bits32 5) 2
    printLn $ mod (the Bits64 5) 2
    printLn $ mod (the Nat 5) 2

    printLn $ div (the Integer 3) 5
    printLn $ div (the Int 3) 5
    printLn $ div (the Bits8 3) 5
    printLn $ div (the Bits16 3) 5
    printLn $ div (the Bits32 3) 5
    printLn $ div (the Bits64 3) 5
    printLn $ div (the Nat 3) 5

    printLn $ mod (the Integer 3) 5
    printLn $ mod (the Int 3) 5
    printLn $ mod (the Bits8 3) 5
    printLn $ mod (the Bits16 3) 5
    printLn $ mod (the Bits32 3) 5
    printLn $ mod (the Bits64 3) 5
    printLn $ mod (the Nat 3) 5

    printLn $ div (the Integer (-5)) 2
    printLn $ div (the Int (-5)) 2

    printLn $ mod (the Integer (-5)) 2
    printLn $ mod (the Int (-5)) 2

    printLn $ div (the Integer (-3)) 5
    printLn $ div (the Int (-3)) 5

    printLn $ mod (the Integer (-3)) 5
    printLn $ mod (the Int (-3)) 5

    printLn $ div (-432642342742368327462378462387) 36473264372
    printLn $ mod (-432642342742368327462378462387) 36473264372

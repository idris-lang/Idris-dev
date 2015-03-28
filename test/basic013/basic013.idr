foo : String
foo = "λx→x"

bar : String
bar = "λx→x"

baz : Char
baz = 'λ'

quux : String
quux = "\x0a\x80\xC9\xFF\n3\n4"

appMany : Nat -> String
appMany Z = foo
appMany (S k) = bar ++ appMany k

main : IO ()
main = do putStrLn foo
          putStrLn (foo ++ bar)
          putStrLn (reverse (foo ++ bar))
          printLn (length foo)
          printLn baz
          let x = 4
          let newstr = appMany (toNat x)
          putStrLn newstr
          printLn (strHead newstr)
          printLn (length newstr)
          printLn (strIndex newstr 4)
          putStrLn (strCons (strIndex newstr 4) "")
          putStrLn ("Tail: " ++ strTail newstr)
          putStrLn ("Tail Tail: " ++ strTail (strTail newstr))
          putStrLn ("Cons: " ++ strCons 'λ' newstr)
          putStrLn ("Reverse: " ++ reverse newstr)


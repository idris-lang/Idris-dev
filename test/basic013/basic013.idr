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
          printLn [1..5]
          printLn [5..1]
          printLn [(-9), (-7)..(-1)]
          printLn [17,15..1]
          printLn [19,15..2]
          printLn [-2,0..4]
          printLn [1,0..-2]
          printLn [3,5..3]
          printLn [2,1..2]
          printLn [4,1..3]
          printLn [1,4..2]
          printLn [3,5..1]
          printLn [4,1..5]
          printLn [1,1..2]
          printLn [2,2..1]
          printLn $ the (List Nat) [1..5]
          printLn $ the (List Nat) [5..1]
          printLn $ the (List Nat) [5,4..1]
          printLn $ the (List Nat) [1,3..5]
          printLn $ the (List Nat) [5,3..1]
          printLn $ the (List Nat) [3,5..3]
          printLn $ the (List Nat) [2,1..2]
          printLn $ the (List Nat) [4,1..3]
          printLn $ the (List Nat) [1,4..2]
          printLn $ the (List Nat) [3,5..1]
          printLn $ the (List Nat) [4,1..5]
          printLn $ the (List Nat) [1,1..2]
          printLn $ the (List Nat) [2,2..1]
          printLn $ the (List Int) [(-1)..(-5)]
          printLn $ the (List Int) [-2,0..4]
          printLn $ the (List Int) [1,0..-2]
          printLn $ the (List Int) [3,5..3]
          printLn $ the (List Int) [2,1..2]
          printLn $ the (List Int) [4,1..3]
          printLn $ the (List Int) [1,4..2]
          printLn $ the (List Int) [3,5..1]
          printLn $ the (List Int) [4,1..5]
          printLn $ the (List Int) [1,1..2]
          printLn $ the (List Int) [2,2..1]
          printLn ['z'..'x']
          printLn ['g','e'..'a']
          printLn ['x'..'z']
          printLn ['a','c'..'g']

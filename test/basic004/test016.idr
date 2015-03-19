module Main

%default total

codata Stream' a = Nil | (::) a (Stream' a)

countFrom : Int -> Stream' Int
countFrom x = x :: countFrom (x + 1)

take : Nat -> Stream' a -> List a
take Z _ = []
take (S n) (x :: xs) = x :: take n xs
take n [] = []

main : IO ()
main = do printLn (take 10 (Main.countFrom 10))


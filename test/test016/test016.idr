module Main

%default total

codata Stream a = Nil | (::) a (Stream a)

countFrom : Int -> Stream Int
countFrom x = x :: countFrom (x + 1)

take : Int -> Stream a -> List a
take 0 _ = []
take n (x :: xs) = x :: take (n - 1) xs
take n [] = []

-- foo : main.countFrom 4 = 4 :: main.countFrom 5
-- foo = refl

main : IO ()
main = do print (take 10 (Main.countFrom 10))


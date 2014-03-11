-- perform a very large foldr to test tail recursion
addAll : (Foldable t, Num a) => t a -> a
addAll = foldr (+) 0

n : Integer
n = 1000000

numbersList : List Bits64
numbersList = numbersList' n []
 where
   numbersList' : Integer -> List Bits64 -> List Bits64
   numbersList' 0 xs = xs
   numbersList' k xs = numbersList' (k - 1) (fromInteger k :: xs)

numbersVect : Vect (length numbersList) Bits64
numbersVect = fromList numbersList

main : IO ()
main = do
  putStrLn . show . prim__zextB64_BigInt $ addAll numbersVect
  putStrLn . show . prim__zextB64_BigInt $ addAll numbersList



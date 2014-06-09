-- perform a very large foldr to test tail recursion
addAll : (Foldable t, Num a) => t a -> a
addAll = foldr (+) 0

n : Integer
n = 1000000

numbersList : List Integer
numbersList = numbersList' n []
 where
   numbersList' : Integer -> List Integer -> List Integer
   numbersList' 0 xs = xs
   numbersList' k xs = numbersList' (k - 1) (fromInteger k :: xs)

numbersVect : Vect (length numbersList) Integer
numbersVect = fromList numbersList

main : IO ()
main = do
  putStrLn . show . addAll $ numbersVect
  putStrLn . show . addAll $ numbersList



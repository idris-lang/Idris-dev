module Main 

import Data.Vect
import Data.Fin

test : DecEq a => a -> a -> Bool
test i1 i2 with (decEq i1 i2)
  test i1 i1 | Yes Refl = True
  test i1 i2 | No p = False

main : IO ()
main = do
-- Primitives
  putStrLn . show $ test (the Int 3) (the Int 3)
  putStrLn . show $ test (the Integer 3) (the Integer 4)
  putStrLn . show $ test "hello" "hello"
  putStrLn . show $ test "hello" "world"
  putStrLn . show $ test (the Char '\0') (the Char '\0')
  putStrLn . show $ test (the Char '\1') (the Char '\2')
-- Non-primitives
  -- Vect
  putStrLn . show $ 
    test (the (Vect _ Int) [1,2,3]) (the (Vect _ Int) [1,2,3])
  putStrLn . show $ 
    test (the (Vect _ Int) [1,2,3]) (the (Vect _ Int) [1,2,4])
  -- List
  putStrLn . show $ 
    test (the (List Int) [1,2,3]) (the (List Int) [1,2,3])
  putStrLn . show $ 
    test (the (List Int) [1,2,3]) (the (List Int) [1,2])
  putStrLn . show $ 
    test (the (List Int) [1,2,3]) (the (List Int) [1,2,4])
  -- Tuple
  putStrLn . show $
    test (the (Int, Int) (1, 1)) (the (Int, Int) (1, 1))
  putStrLn . show $
    test (the (Int, Int) (1, 2)) (the (Int, Int) (1, 1))
  -- Unit
  putStrLn . show $ test () ()
  -- Booleans
  putStrLn . show $ test True True
  putStrLn . show $ test True False
  -- Maybe
  putStrLn . show $ test (Just "hello") (Just "hello")
  putStrLn . show $ test (Just "hello") (Just "world")
  putStrLn . show $ test (Just "hello") Nothing
  -- Either
  putStrLn . show $ test (the (Either String Bool) (Left "hello")) 
                         (the (Either String Bool) (Left "hello"))
  putStrLn . show $ test (the (Either String Bool) (Left "hello")) 
                         (the (Either String Bool) (Left "world"))
  putStrLn . show $ test (Left "hello") (Right "world")
  putStrLn . show $ test (Left "hello") (Right False)
  -- Fin
  putStrLn . show $ test (the (Fin (S (S (S (Z))))) (FS (FS (FZ)))) 
                         (the (Fin (S (S (S (Z))))) (FS (FS (FZ))))
  putStrLn . show $ test (the (Fin (S (S (S (Z))))) (FS (FS (FZ)))) 
                         (the (Fin (S (S (S (Z))))) (FS (FZ)))
  -- Nat
  putStrLn . show $ test (S (S (S Z))) (S (S (S Z)))
  putStrLn . show $ test (S (S (S Z))) (S (S Z))


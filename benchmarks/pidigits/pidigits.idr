import System

{- Toy program that outputs the n first digits of Pi.

   Inspired from http://www.haskell.org/haskellwiki/Shootout/Pidigits. 
   The original ns and str lazy lists have been replaced by strict functions.

   Memory usage seems to be excessive. One of the branches of str is tail recursive, and 
   the other one only needs to cons an extra Integer.

   For reference, the Haskell version runs in 0m0.230s when printing to /dev/null. 
   It almost runs in constant space.
-}

data F = mkF Integer Integer Integer

-- Prints the list of digits by groups of 10
loop : Nat -> Nat -> List Integer -> IO()
loop n k' Nil         = putStrLn $ (pack $ Vect.replicate n ' ') ++ "\t:" ++ show k'
loop Z k' xs          = do putStrLn ("\t:"++show k')
                           loop 10 k' xs
loop (S k) k' (x::xs) = do putStr (show x)
                           loop k (S k') xs

fn : Integer -> F
fn k = mkF k (4*k+2) (2*k+1)

flr : Integer -> F -> Integer
flr x (mkF q r t) = (q*x + r) `div` t

comp : F -> F -> F
comp (mkF q r t) (mkF u v x) = mkF (q*u) (q*v+r*x) (t*x)

-- Returns the list of digits of pi. Memory hungry.
str : F -> Integer -> Nat -> List Integer
str _ _ Z     = Nil
str z k (S n) = if(y == flr 4 z)
                   then y :: str (comp (mkF 10 (-10*y) 1) z    ) k     n
                   else      str (comp z                 (fn k)) (k+1) (S n)
  where y = flr 3 z

pidigit : IO()
pidigit = do
  [_,a] <- getArgs
  let n = fromIntegerNat (the Integer (cast a))
  let l = str (mkF 1 0 1) 1 n
  loop 10 0 l
  return ()

main : IO ()
main = pidigit


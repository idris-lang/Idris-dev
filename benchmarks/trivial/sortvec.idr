module Main

import System
import Effect.Random

total
insert : Ord a => a -> Vect n a -> Vect (S n) a
insert x [] = [x]
insert x (y :: ys) = if (x < y) then x :: y :: ys else y :: insert x ys

vsort : Ord a => Vect n a -> Vect n a
vsort [] = []
vsort (x :: xs) = insert x (vsort xs)

mkSortVec : (n : Nat) -> Eff m [RND] (Vect n Int)
mkSortVec Z = return [] 
mkSortVec (S k) = return (fromInteger !(rndInt 0 10000) :: !(mkSortVec k))

main : IO ()
main = do (_ :: arg :: _) <- getArgs
--           let arg = "2000"
          let vec = runPure [123456789] (mkSortVec (fromInteger (cast arg)))
          putStrLn "Made vector"
          print (vsort vec)
          

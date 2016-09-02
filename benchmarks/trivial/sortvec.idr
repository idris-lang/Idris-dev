module Main

import System
import Effects
import Effect.Random
import Data.Vect

total
insert : Ord a => a -> Vect n a -> Vect (S n) a
insert x [] = [x]
insert x (y :: ys) = if (x < y) then x :: y :: ys else y :: insert x ys

vsort : Ord a => Vect n a -> Vect n a
vsort [] = []
vsort (x :: xs) = insert x (vsort xs)

mkSortVec : (n : Nat) -> Eff (Vect n Int) [RND]
mkSortVec Z = pure []
mkSortVec (S k) = pure (fromInteger !(rndInt 0 10000) :: !(mkSortVec k))

main : IO ()
main = do (_ :: arg :: _) <- getArgs
          let vec = runPure $ (srand 123456789 *> mkSortVec (fromInteger (cast arg)))
          putStrLn "Made vector"
          printLn (vsort vec)

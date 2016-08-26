module Effect.Random

import Effects
import Data.Vect

%access public export

data Random : Effect where 
     GetRandom : sig Random Integer Integer
     SetSeed   : Integer -> sig Random () Integer

implementation Handler Random m where
  handle seed GetRandom k
           = let seed' = assert_total ((1664525 * seed + 1013904223) `prim__sremBigInt` (pow 2 32)) in
                 k seed' seed'
  handle seed (SetSeed n) k = k () n

RND : EFFECT
RND = MkEff Integer Random

||| Generates a random Integer in a given range
rndInt : Integer -> Integer -> Eff Integer [RND]
rndInt lower upper = do v <- call $ GetRandom
                        pure ((v `prim__sremBigInt` (upper - lower)) + lower)

||| Generate a random number in Fin (S `k`)
||| 
||| Note that rndFin k takes values 0, 1, ..., k.
rndFin : (k : Nat) -> Eff (Fin (S k)) [RND]
rndFin k = do let v = assert_total $ !(call GetRandom) `prim__sremBigInt` (cast (S k))
              pure (toFin v)
 where toFin : Integer -> Fin (S k) 
       toFin x = case integerToFin x (S k) of
                      Just v => v
                      Nothing => toFin (assert_smaller x (x - cast (S k)))

||| Select a random element from a vector
rndSelect' : Vect (S k) a -> Eff a [RND]
rndSelect' {k} xs = pure (Vect.index !(rndFin k)  xs)

||| Select a random element from a list, or Nothing if the list is empty
rndSelect : List a -> Eff (Maybe a) [RND]
rndSelect []      = pure Nothing
rndSelect (x::xs) = pure (Just !(rndSelect' (x::(fromList xs))))

||| Sets the random seed
srand : Integer -> Eff () [RND]
srand n = call $ SetSeed n


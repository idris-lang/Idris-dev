module Effect.Random

import Effects

data Random : Effect where 
     getRandom : { Integer } Random Integer 
     setSeed   : Integer -> { Integer } Random () 

using (m : Type -> Type)
  instance Handler Random m where
     handle seed getRandom k
              = let seed' = (1664525 * seed + 1013904223) `prim__sremBigInt` (pow 2 32) in
                    k seed' seed'
     handle seed (setSeed n) k = k () n

RND : EFFECT
RND = MkEff Integer Random

||| Generates a random Integer in a given range
rndInt : Integer -> Integer -> { [RND] } Eff m Integer
rndInt lower upper = do v <- getRandom
                        return (v `prim__sremBigInt` (upper - lower) + lower)

||| Generate a random number in Fin (S `k`)
||| 
||| Note that rndFin k takes values 0, 1, ..., k.
rndFin : (k : Nat) -> { [RND] } Eff m (Fin (S k))
rndFin k = do let v = !getRandom `prim__sremBigInt` (cast (S k))
              return (toFin v)
 where toFin : Integer -> Fin (S k) 
       toFin x = case integerToFin x (S k) of
                      Just v => v
                      Nothing => toFin (assert_smaller x (x - cast (S k)))

||| Select a random element from a vector
rndSelect' : Vect (S k) a -> { [RND] } Eff IO a
rndSelect' {k} xs = return (Vect.index !(rndFin k)  xs)

||| Select a random element from a list, or Nothing if the list is empty
rndSelect : List a -> { [RND] } Eff IO (Maybe a)
rndSelect []      = return Nothing
rndSelect (x::xs) = return (Just !(rndSelect' (x::(fromList xs))))

||| Sets the random seed
srand : Integer -> { [RND] } Eff m ()
srand n = setSeed n


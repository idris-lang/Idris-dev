module Control.ST.Random

import Control.ST
import Data.Vect

%access public export

Random : Type
Random = State Integer

getRandom : (rnd : Var) -> ST m Integer [rnd ::: Random]
getRandom rnd =
  do
    st <- read rnd
    let st' = assert_total ((1664525 * st + 1013904223) `prim__sremBigInt` (pow 2 32))
    write rnd st'
    pure st'

||| Generates a random Integer in a given range
rndInt : (rnd : Var) -> Integer -> Integer -> ST m Integer [rnd ::: Random]
rndInt rnd lower upper = do v <- getRandom rnd
                            pure $ assert_total ((v `prim__sremBigInt` (upper - lower)) + lower)

||| Generate a random number in `Fin (S k)`
|||
||| Note that rndFin k takes values 0, 1, ..., k.
rndFin : (rnd : Var) -> (k : Nat) -> ST m (Fin (S k)) [rnd ::: Random]
rndFin rnd k = do let v = assert_total $ !(getRandom rnd) `prim__sremBigInt` (cast (S k))
                  pure (toFin v)
 where toFin : Integer -> Fin (S k)
       toFin x = case integerToFin x (S k) of
                      Just v => v
                      Nothing => toFin (assert_smaller x (x - cast (S k)))

||| Select a random element from a vector
rndSelect' : (rnd : Var) -> Vect (S k) a -> ST m a [rnd ::: Random]
rndSelect' {k} rnd xs = pure (Vect.index !(rndFin rnd k)  xs)

||| Select a random element from a non-empty list
rndSelect : (rnd : Var) -> (xs : List a) -> {auto ok : NonEmpty xs} -> ST m a [rnd ::: Random]
rndSelect rnd (x::xs) {ok=NonEmpty} = pure ( !(rndSelect' rnd (x::(fromList xs))))
rndSelect rnd [] {ok=NonEmpty} impossible

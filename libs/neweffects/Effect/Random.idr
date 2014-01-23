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

rndInt : Integer -> Integer -> { [RND] } Eff m Integer
rndInt lower upper = do v <- getRandom
                        return (v `prim__sremBigInt` (upper - lower) + lower)

srand : Integer -> { [RND] } Eff m ()
srand n = setSeed n


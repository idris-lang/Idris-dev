module Effect.Random

import Effects

data Random : Type -> Type -> Type -> Type where
     getRandom : Random Integer Integer Integer

using (m : Type -> Type)
  instance Handler Random m where
     handle seed getRandom k
              = let seed' = (1664525 * seed + 1013904223) `prim__sremBigInt` (pow 2 32) in
                    k seed' seed'

RND : EFFECT
RND = MkEff Integer Random

rndInt : Integer -> Integer -> Eff m [RND] Integer
rndInt lower upper = do v <- getRandom
                        return (v `prim__sremBigInt` (upper - lower) + lower)



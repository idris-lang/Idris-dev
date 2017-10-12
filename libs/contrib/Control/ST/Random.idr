module Control.ST.Random

import Control.ST

public export
Random : Type
Random = State Integer

export
getRandom : (rnd : Var) -> ST m Integer [rnd ::: Random]
getRandom rnd =
  do
    st <- read rnd
    let st' = assert_total ((1664525 * st + 1013904223) `prim__sremBigInt` (pow 2 32))
    write rnd st'
    pure st'

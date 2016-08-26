module Effect.State

import Effects

%access public export

data State : Effect where
  Get :      sig State a  a
  Put : b -> sig State () a b

-- using (m : Type -> Type)
implementation Handler State m where
     handle st Get     k = k st st
     handle st (Put n) k = k () n

STATE : Type -> EFFECT
STATE t = MkEff t State

get : Eff x [STATE x]
get = call $ Get

put : x -> Eff () [STATE x]
put val = call $ Put val

putM : y -> Eff () [STATE x] [STATE y]
putM val = call $ Put val

update : (x -> x) -> Eff () [STATE x]
update f = put (f !get)

updateM : (x -> y) -> Eff () [STATE x] [STATE y]
updateM f = putM (f !get)

locally : x -> (Eff t [STATE x]) -> Eff t [STATE y]
locally newst prog = do st <- get
                        putM newst
                        val <- prog
                        putM st
                        pure val


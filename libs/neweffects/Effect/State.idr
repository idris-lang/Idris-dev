module Effect.State

import Effects

%access public

data State : Effect where
  Get :      { a }       State a
  Put : b -> { a ==> b } State () 

using (m : Type -> Type)
  instance Handler State m where
     handle st Get     k = k st st
     handle st (Put n) k = k () n

STATE : Type -> EFFECT
STATE t = MkEff t State

get : { [STATE x] } Eff x
get = call $ Get

put : x -> { [STATE x] } Eff () 
put val = call $ Put val

putM : y -> { [STATE x] ==> [STATE y] } Eff () 
putM val = call $ Put val

update : (x -> x) -> { [STATE x] } Eff () 
update f = put (f !get)

updateM : (x -> y) -> { [STATE x] ==> [STATE y] } Eff () 
updateM f = putM (f !get)

locally : x -> ({ [STATE x] } Eff t) -> { [STATE y] } Eff t 
locally newst prog = do st <- get
                        putM newst
                        val <- prog
                        putM st
                        return val


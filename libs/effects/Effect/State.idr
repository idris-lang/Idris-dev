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

get : { [STATE x] } Eff m x
get = effect $ Get

put : x -> { [STATE x] } Eff m () 
put val = effect $ Put val

putM : y -> { [STATE x] ==> [STATE y] } Eff m () 
putM val = effect $ Put val

update : (x -> x) -> { [STATE x] } Eff m () 
update f = put (f !get)

updateM : (x -> y) -> { [STATE x] ==> [STATE y] } Eff m () 
updateM f = putM (f !get)

locally : x -> ({ [STATE x] } Eff m t) -> { [STATE y] } Eff m t 
locally newst prog = do st <- get
                        putM newst
                        val <- prog
                        putM st
                        return val


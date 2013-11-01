module Effect.State

import Effects

%access public

data State : Effect where
     Get :      State a a a
     Put : b -> State a b ()

using (m : Type -> Type)
  instance Handler State m where
     handle st Get     k = k st st
     handle st (Put n) k = k n ()

STATE : Type -> EFFECT
STATE t = MkEff t State

get : Eff m [STATE x] x
get = Get

put : x -> Eff m [STATE x] ()
put val = Put val

putM : y -> EffM m [STATE x] [STATE y] ()
putM val = Put val

update : (x -> x) -> Eff m [STATE x] ()
update f = put (f !get)

updateM : (x -> y) -> EffM m [STATE x] [STATE y] ()
updateM f = putM (f !get)

locally : x -> Eff m [STATE x] t -> Eff m [STATE y] t
locally newst prog = do st <- get
                        putM newst
                        val <- prog
                        putM st
                        return val


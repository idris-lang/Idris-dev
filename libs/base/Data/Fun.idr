module Data.Fun

--------------------------------------------------------------------------------
-- Build an n-ary function type from a Vect of Types and a result type
--------------------------------------------------------------------------------
Fun : Vect n Type -> Type -> Type
Fun [] r = r
Fun (t::ts) r = t -> Fun ts r

target : {ts : Vect n Type} -> Fun ts r -> Type
target {r} _ = r 


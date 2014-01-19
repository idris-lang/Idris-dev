module Data.FunN

--------------------------------------------------------------------------------
-- Build an n-ary function type from a Vect of Types and a result type
--------------------------------------------------------------------------------
FunN : Vect n Type -> Type -> Type
FunN [] r = r
FunN (t::ts) r = t -> FunN ts r

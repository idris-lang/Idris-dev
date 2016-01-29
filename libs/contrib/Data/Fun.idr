module Data.Fun

import public Data.Vect

%default total
%access public export

||| Build an n-ary function type from a Vect of Types and a result type
Fun : Vect n Type -> Type -> Type
Fun [] r = r
Fun (t::ts) r = t -> Fun ts r

chain : {ts : Vect n Type} -> Fun [r] r' -> Fun ts r -> Fun ts r'
chain {ts = []} g r  = g r
chain {ts = (_::_)} g f = \ x => chain g (f x)

target : {ts : Vect n Type} -> Fun ts r -> Type
target {r} _ = r

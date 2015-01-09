module Effect.Protocols

-- Helpers for writing and using effects that implement protocols with
-- state transitions

import public Effects

infix 5 :=>

-- 'sig' gives the signature for an effect. There are three versions
-- depending on whether there is no state change, a non-dependent change,
-- or a dependent change. These are easily disambiguated by type.

namespace NoUpdateEffect
  sig : Effect -> Type -> Type -> Type
  sig e r e_in = e r e_in (\v => e_in)

namespace UpdateEffect
  sig : Effect -> Type -> Type -> Type -> Type
  sig e r e_in e_out = e r e_in (\v => e_out)

namespace DepUpdateEffect
  sig : Effect -> (x : Type) -> Type -> (x -> Type) -> Type
  sig e r e_in e_out = e r e_in e_out


-- a single effect transition.

data EffTrans : Type -> Type -> Type where
     (:=>) : a -> b -> EffTrans a b

-- 'trans' gives a single effect transition. Again three versions, for
-- no transition, non-dependent transition and dependent transition, again
-- disambiguated by type, but the one with no update can be implicit.

namespace NoUpdateTrans
  implicit
  trans : a -> EffTrans a (x -> a)
  trans t = t :=> (\v => t)

namespace UpdateTrans
  trans : a -> b -> EffTrans a (x -> b)
  trans s t = s :=> (\v => t)

namespace DepUpdateTrans
  trans : a -> b -> EffTrans a b
  trans s t = s :=> t

Proto : (x : Type) -> 
      List (EffTrans EFFECT (x -> EFFECT)) ->
      Type
Proto x xs = Eff x (proto_in xs) (\val : x => proto_out xs val)
  where
    proto_out : List (EffTrans EFFECT (x -> EFFECT)) -> x -> List EFFECT
    proto_out [] val = []
    proto_out ((e_in :=> e_out) :: xs) val 
        = let rec = proto_out xs val in e_out val :: rec 

    proto_in : List (EffTrans EFFECT (x -> EFFECT)) -> List EFFECT
    proto_in [] = []
    proto_in ((e_in :=> e_out) :: xs) 
        = let rec = proto_in xs in e_in :: rec 


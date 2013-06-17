module Decidable.Decidable

%access public

--------------------------------------------------------------------------------
-- Typeclass for decidable n-ary Relations
--------------------------------------------------------------------------------

PredicateFunctor : Type
PredicateFunctor = (Type -> Type) -> Type

class Decidable (R : PredicateFunctor) where
  total decide : R Dec


using (P : Type, p : P)
  data Given : Dec P -> Type where
    always : Given (Yes p)


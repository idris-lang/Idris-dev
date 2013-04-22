module Decidable.Decidable

%access public

--------------------------------------------------------------------------------
-- Typeclass for decidable n-ary Relations
--------------------------------------------------------------------------------

using (t : Type)
  class Rel (p : t) where
    total liftRel : (Type -> Type) -> Type

  class (Rel p) => Decidable (p : t) where
    total decide : liftRel Dec

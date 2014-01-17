module Decidable.Decidable

%access public

--------------------------------------------------------------------------------
-- Typeclass for decidable n-ary Relations
--------------------------------------------------------------------------------

This can't work yet! The class parameters must appear in the method type
signatures otherwise when defining the instances class resolution doesn't
have any clues...

using (t : Type)
  class Rel (p : t) where
    total liftRel : (Type -> Type) -> Type

  class (Rel p) => Decidable (p : t) where
    total decide : liftRel Dec

using (P : Type, p : P)
  data Given : Dec P -> Type where
    always : Given (Yes p)

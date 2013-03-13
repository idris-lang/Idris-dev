module usubst

total unsafeSubst : (P : a -> Type) -> (x : a) -> (y : a) -> P x -> P y
unsafeSubst P x y px with (O)
  unsafeSubst P x x px | _ = px

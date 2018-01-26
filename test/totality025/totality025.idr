total
bad1 : (f : Type -> Type) -> (x, y : Type) -> f x = f y -> Void
bad1 _ _ _ Refl impossible

total
ohoh : Void
ohoh = bad1 id Unit Unit Refl

-- of course, these shouldn't be provable as well:
total
bad2 : (f, g : Type -> Type) -> (x : Type) -> f x = g x -> Void
bad2 _ _ _ Refl impossible

total
bad3 : (f, g : Type -> Type) -> (x, y : Type) -> f x = g y -> Void
bad3 _ _ _ _ Refl impossible


Symmetric : {c : Type} -> (c -> c -> Type) -> Type
Symmetric {c} rel = {a : c} -> {b : c} -> rel a b -> rel b a

record Symmetry (t : Type) (rel : t -> t -> Type) where
  constructor MkSymmetry
  is_symmetric : Symmetric {c=t} rel

symmetry : {ty : Type} -> Symmetry ty (=)
symmetry = MkSymmetry sym


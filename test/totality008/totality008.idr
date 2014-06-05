 data T : Type -> Type where
  c1 : T Nat
  c2 : T (T Nat)

total
ElimT : (A : Type) -> T A -> A
ElimT _ c1 = 3
ElimT _ c2 = c1

 data T : Type -> Type where
  C1 : T Nat
  C2 : T (T Nat)

total
ElimT : (A : Type) -> T A -> A
ElimT _ C1 = 3
ElimT _ C2 = C1

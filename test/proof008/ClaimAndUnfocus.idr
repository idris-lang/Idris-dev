module ClaimAndUnfocus

foo : Nat -> Nat
foo = ?foo_rhs

---------- Proofs ----------

ClaimAndUnfocus.foo_rhs = proof
  claim bar Nat -> Nat -> Nat
  unfocus
  intro x
  exact bar x x
  intro x,y
  refine plus
  refine x
  refine y


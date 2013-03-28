using (A : Type, B : A->Type, C : Type)
  foo : ((x:A) -> B x -> C) -> ((x:A ** B x) -> C)
  foo f p = f (getWitness p) (getProof p)

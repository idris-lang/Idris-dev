sigmaEq2 : {A : Type} ->
           {P : A -> Type} ->
           {s1: DPair A P} ->
           {s2: DPair A P} ->
           fst s1 = fst s2 ->
           snd s1 = snd s2 ->
           s1 = s2
sigmaEq2 {A} {P} {s1 = (x ** prf)} {s2 = (x ** prf)} Refl Refl = Refl

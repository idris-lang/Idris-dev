sigmaEq2 : {A : Type} ->
           {P : A -> Type} ->
           {s1: DepPair A P} ->
           {s2: DepPair A P} ->
           fst s1 = fst s2 ->
           snd s1 = snd s2 ->
           s1 = s2
sigmaEq2 {A} {P} {s1 = (x ** prf)} {s2 = (x ** prf)} Refl Refl = Refl

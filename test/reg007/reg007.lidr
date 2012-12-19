> module B

> import A

> isSame  : A.n = A.lala
> isSame  = refl

> A.n     = O    -- This is where it's at!
> A.lala  = S O

> hurrah  : O = S O
> hurrah  = isSame

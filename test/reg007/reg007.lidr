> module B

> import A

> isSame  : A.n = A.lala
> isSame  = Refl

> A.n     = Z    -- This is where it's at!
> A.lala  = S Z

> hurrah  : Z = S Z
> hurrah  = isSame

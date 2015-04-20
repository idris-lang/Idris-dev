module MinCrash

-- Test that #2130 stays fixed. It's important that the first argument
-- to revInduction be called `pred` here, because the bug was
-- triggered by looking up a bound variable in the global context and
-- getting an ambiguous result in a context where fully-qualified
-- names were expected.

revInduction : (P : List a -> Type) -> P [] -> ((xs : List a) -> (x : a) -> P xs -> P (xs ++ [x]))
               -> (ys : List a) -> P ys
revInduction pred base ind ys with (reverse ys)
  revInduction pred base ind _ | revys =
    ?revInduction_rhs

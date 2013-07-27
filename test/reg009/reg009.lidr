> isAnyBy : (alpha -> Bool) -> (n : Nat ** Vect alpha n) -> Bool
> isAnyBy _ (_ ** Nil) = False
> isAnyBy p (_ ** (a :: as)) = p a || isAnyBy p (_ ** as)


> filterTagP : (p  : alpha -> Bool) -> 
>              (as : Vect alpha n) -> 
>              so (isAnyBy p (n ** as)) ->
>              (m : Nat ** (Vect (a : alpha ** so (p a)) m, so (m > Z)))
> filterTagP {n = S m} p (a :: as) q with (p a)
>   | True  = (_
>              ** 
>              ((a ** believe_me oh) 
>               :: 
>               (fst (getProof (filterTagP p as (believe_me oh)))),
>               oh
>              )
>             )
>   | False = filterTagP p as (believe_me oh)

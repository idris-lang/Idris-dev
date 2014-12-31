> import Data.So
> import Data.Vect

> isAnyBy : (alpha -> Bool) -> (n : Nat ** Vect n alpha) -> Bool
> isAnyBy _ (_ ** Nil) = False
> isAnyBy p (_ ** (a :: as)) = p a || isAnyBy p (_ ** as)

> filterTagP : (p  : alpha -> Bool) ->
>              (as : Vect n alpha) ->
>              So (isAnyBy p (n ** as)) ->
>              (m : Nat ** (Vect m (a : alpha ** So (p a)), So (m > Z)))
> filterTagP {n = S m} p (a :: as) q with (p a)
>   | True  = (_
>              **
>              ((a ** believe_me Oh)
>               ::
>               (fst (getProof (filterTagP p as (believe_me Oh)))),
>               Oh
>              )
>             )
>   | False = filterTagP p as (believe_me Oh)

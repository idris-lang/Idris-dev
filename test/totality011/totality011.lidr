> %default total

> X       :  Nat -> Type
> Y       :  (t : Nat) -> X t -> Type
> step    :  (t : Nat) -> (x : X t) -> Y t x -> X (S t)

> Pred : X t -> X (S t) -> Type
> Pred {t} x x' = Subset (Y t x) (\ y => (x' = step t x y))

> ReachableFrom : X t'' -> X t -> Type
> ReachableFrom {t'' = Z   } {t} x'' x  =  
>   (Z = t , x'' = x) 
> ReachableFrom {t'' = S t'} {t} x'' x  = 
>   Either (S t' = t , x'' = x) 
>          (Subset (X t') (\ x' => (x' `ReachableFrom` x , x' `Pred` x'')))

> weCanOnlyGetOlder : (x'' : X t'') -> 
>                     (x   : X t) ->
>                     x'' `ReachableFrom` x ->
>                     t'' `GTE` t

> weCanOnlyGetOlder {t'' = Z} {t = Z}   _ _ _  =  LTEZero
> weCanOnlyGetOlder {t'' = Z} {t = S m} _ _ (Zeqt , _)  = 
>   void (uninhabited u) where
>     u : Z = S m 
>     u = trans Zeqt Refl

> weCanOnlyGetOlder {t'' = S _} {t = S _} _ _ _ = ?foo

-- > weCanOnlyGetOlder {t'' = S _} {t = S _} _ _ (_, _) = ?foo


> module Set

> %default total

> postulate soAndIntro : (p : alpha -> Bool) ->
>                        (q : beta -> Bool) -> 
>                        (a : alpha) ->
>                        (b : beta) ->
>                        so (p a) ->
>                        so (q b) ->
>                        so (p a && q b)

> hasNoDuplicates : (Eq alpha) => List alpha -> Bool
> hasNoDuplicates as = as == nub as

> %assert_total
> setEq : (Eq alpha) => List alpha -> List alpha -> Bool
> setEq Nil Nil = True
> setEq Nil (y :: ys) = False
> setEq (x :: xs) Nil = False
> setEq {alpha} (x :: xs) (y :: ys) =
>   (x == y && setEq xs ys) 
>   ||
>   (elem x ys && elem y xs && 
>    setEq (filter (/= y) xs) (filter (/= x) ys)
>   )

> data Set : Type -> Type where
>   setify : (as : List a) -> Set a

> instance (Eq a) => Eq (Set a) where
>   (==) (setify as) (setify bs) = setEq as bs

> postulate reflexive_Set_eqeq : (Eq a) => 
>                                (as : Set a) -> 
>                                so (as == as)

> unwrap : Set a -> List a
> unwrap (setify as) = as

> union : Set (Set a) -> Set a
> union (setify ss) = setify (concat (map unwrap ss)) 

> listify : (Eq a) => Set a -> List a
> listify = nub . unwrap

> arePairwiseDisjoint : (Eq a) => Set (Set a) -> Bool
> arePairwiseDisjoint (setify ss) = 
>   hasNoDuplicates (concat (map listify ss))

> isPartition : (Eq a) => Set (Set a) -> Set a -> Bool
> isPartition ass as = arePairwiseDisjoint ass && union ass == as

> partitionLemma0 : (Eq alpha) => 
>                   (ass : Set (Set alpha)) -> 
>                   so (arePairwiseDisjoint ass) ->
>                   so (ass `isPartition` union ass)
> partitionLemma0 ass asspd = (soAndIntro (\ xss => arePairwiseDisjoint xss)
>                                        (\ xs => union ass == xs)
>                                        ass
>                                        (union ass)
>                                        asspd 
>                                        uasseqas) where
>   uasseqas : so (union ass == union ass)
>   uasseqas = reflexive_Set_eqeq (union ass)


> module Set

> import Data.So

> %default total

> postulate soAndIntro : (p : alpha -> Bool) ->
>                        (q : beta -> Bool) -> 
>                        (a : alpha) ->
>                        (b : beta) ->
>                        So (p a) ->
>                        So (q b) ->
>                        So (p a && q b)

> hasNoDuplicates : (Eq alpha) => List alpha -> Bool
> hasNoDuplicates as = as == nub as

> setEq : (Eq alpha) => List alpha -> List alpha -> Bool
> setEq Nil Nil = True
> setEq Nil (y :: ys) = False
> setEq (x :: xs) Nil = False
> setEq {alpha} (x :: xs) (y :: ys) =
>   assert_total $ (x == y && setEq xs ys) 
>   ||
>   (elem x ys && elem y xs && 
>    setEq (filter (/= y) xs) (filter (/= x) ys)
>   )

> data Set : Type -> Type where
>   Setify : (as : List a) -> Set a

> implementation (Eq a) => Eq (Set a) where
>   (==) (Setify as) (Setify bs) = setEq as bs

> postulate reflexive_Set_eqeq : (Eq a) => 
>                                (as : Set a) -> 
>                                So (as == as)

> unwrap : Set a -> List a
> unwrap (Setify as) = as

> union : Set (Set a) -> Set a
> union (Setify ss) = Setify (concat (map unwrap ss)) 

> listify : (Eq a) => Set a -> List a
> listify = nub . unwrap

> arePairwiseDisjoint : (Eq a) => Set (Set a) -> Bool
> arePairwiseDisjoint (Setify ss) = 
>   hasNoDuplicates (concat (map listify ss))

> isPartition : (Eq a) => Set (Set a) -> Set a -> Bool
> isPartition ass as = arePairwiseDisjoint ass && union ass == as

> partitionLemma0 : (Eq alpha) => 
>                   (ass : Set (Set alpha)) -> 
>                   So (arePairwiseDisjoint ass) ->
>                   So (ass `isPartition` union ass)
> partitionLemma0 ass asspd = (soAndIntro (\ xss => arePairwiseDisjoint xss)
>                                        (\ xs => union ass == xs)
>                                        ass
>                                        (union ass)
>                                        asspd 
>                                        uasseqas) where
>   uasseqas : So (union ass == union ass)
>   uasseqas = reflexive_Set_eqeq (union ass)


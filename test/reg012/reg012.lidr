> total soElim            :  (C : (b : Bool) -> so b -> Type) ->
>                            C True oh                       ->
>                            (b : Bool) -> (s : so b) -> (C b s)
> soElim C coh .True .oh  =  coh

> soFalseElim             :  so False -> a
> soFalseElim x           =  FalseElim (soElim C () False x)
>                            where
>                            C : (b : Bool) -> so b -> Type
>                            C True s = ()
>                            C False s = _|_

> soTrue                  :  so b -> b = True
> soTrue {b = False} x    =  soFalseElim x
> soTrue {b = True}  x    =  refl
                             
> class Eq alpha => ReflEqEq alpha where
>   reflexive_eqeq : (a : alpha) -> so (a == a)

> modifyFun : (Eq alpha) => 
>             (alpha -> beta) -> 
>             (alpha, beta) -> 
>             (alpha -> beta)
> modifyFun f (a, b) a' = if a' == a then b else f a'

> modifyFunLemma : (ReflEqEq alpha) => 
>                  (f : alpha -> beta) ->
>                  (ab : (alpha, beta)) ->
>                  modifyFun f ab (fst ab) = snd ab
> modifyFunLemma f (a,b) = 
>   replace {P = \ z => boolElim (a == a) b (f a) = boolElim z b (f a)} 
>           (soTrue (reflexive_eqeq a)) refl

> import Data.So

> total soElim            :  (C : (b : Bool) -> So b -> Type) ->
>                            C True Oh                       ->
>                            (b : Bool) -> (s : So b) -> (C b s)
> soElim C coh True Oh  =  coh

> soFalseElim             :  So False -> a
> soFalseElim x           =  void (soElim C () False x)
>                            where
>                            C : (b : Bool) -> So b -> Type
>                            C True s = ()
>                            C False s = Void

> soTrue                  :  So b -> b = True
> soTrue {b = False} x    =  soFalseElim x
> soTrue {b = True}  x    =  Refl

> class Eq alpha => ReflEqEq alpha where
>   reflexive_eqeq : (a : alpha) -> So (a == a)

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
>   rewrite soTrue (reflexive_eqeq a) in Refl

   replace {P = \ z => ifThenElse (a == a) b (f a) = ifThenElse z b (f a)}
           (soTrue (reflexive_eqeq a)) Refl

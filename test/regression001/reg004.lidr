> %default total
> %access public export
> %auto_implicits off

> Natural : {F, G : Type -> Type} -> 
>           (Functor F) => (Functor G) =>
>           (t : {A : Type} -> F A -> G A) -> 
>           Type            
> Natural {F=fF} {G=gG} t = {A, B : Type} -> 
>                     (f : A -> B) ->
>                     (x : fF A) -> 
>                     t (map f x) = map f  (t x) 

> Monotone : {B, C : Type} -> {F : Type -> Type} -> (Functor F) => 
>            (LTE_B : B -> B -> Type) -> 
>            (LTE_C : C -> C -> Type) -> 
>            (measure : F B -> C) -> 
>            Type
> Monotone {B=bB} {C=cC} {F=fF} lte_B lte_C measure =
>   {A : Type} ->
>   (f : A -> bB) -> 
>   (g : A -> bB) -> 
>   (p : (a : A) -> f a `lte_B` g a) -> 
>   (x : fF A) -> 
>   measure (map f x) `lte_C` measure (map g x)  

> monotoneNaturalLemma: {B, C : Type} -> {F : Type -> Type} -> (Functor F) => 
>                       (LTE_B : B -> B -> Type) -> 
>                       (LTE_C : C -> C -> Type) -> 
>                       (measure : F B -> C) ->
>                       Monotone LTE_B LTE_C measure -> 
>                       (t : {A : Type} -> F A -> F A) -> 
>                       Natural t -> 
>                       Monotone LTE_B LTE_C (measure . t)
> monotoneNaturalLemma {B=bB} {C=cC} {F=fF} lte_B lte_C m mm t nt = mmt where
>   mmt : {A : Type} -> 
>         (f : A -> bB) -> 
>         (g : A -> bB) -> 
>         (p : (a : A) -> f a `lte_B` g a) ->
>         (x : fF A) -> 
>         m (t {A = bB} (map f x)) `lte_C` m (t {A = bB} (map g x))   
>   mmt = ?kika


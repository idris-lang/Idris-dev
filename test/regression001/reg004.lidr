> %default total
> %access public export
> %auto_implicits off

> Natural : {F, G : Type -> Type} -> 
>           (Functor F) => (Functor G) =>
>           (t : {A : Type} -> F A -> G A) -> 
>           Type            
> Natural {F} {G} t = {A, B : Type} -> 
>                     (f : A -> B) ->
>                     (x : F A) -> 
>                     t (map f x) = map f  (t x) 

> Monotone : {B, C : Type} -> {F : Type -> Type} -> (Functor F) => 
>            (LTE_B : B -> B -> Type) -> 
>            (LTE_C : C -> C -> Type) -> 
>            (measure : F B -> C) -> 
>            Type
> Monotone {B} {C} {F} LTE_B LTE_C measure =
>   {A : Type} ->
>   (f : A -> B) -> 
>   (g : A -> B) -> 
>   (p : (a : A) -> f a `LTE_B` g a) -> 
>   (x : F A) -> 
>   measure (map f x) `LTE_C` measure (map g x)  

> monotoneNaturalLemma: {B, C : Type} -> {F : Type -> Type} -> (Functor F) => 
>                       (LTE_B : B -> B -> Type) -> 
>                       (LTE_C : C -> C -> Type) -> 
>                       (measure : F B -> C) ->
>                       Monotone LTE_B LTE_C measure -> 
>                       (t : {A : Type} -> F A -> F A) -> 
>                       Natural t -> 
>                       Monotone LTE_B LTE_C (measure . t)
> monotoneNaturalLemma {B} {C} {F} LTE_B LTE_C m mm t nt = mmt where
>   mmt : {A : Type} -> 
>         (f : A -> B) -> 
>         (g : A -> B) -> 
>         (p : (a : A) -> f a `LTE_B` g a) ->
>         (x : F A) -> 
>         m (t {A = B} (map f x)) `LTE_C` m (t {A = B} (map g x))   
>   mmt = ?kika


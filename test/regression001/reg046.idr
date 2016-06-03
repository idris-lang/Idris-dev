module test

data MyList : (A : Type) -> Type where
    MyNil : (A : Type) -> MyList A
    MyCons : (A : Type) -> A -> MyList A -> MyList A

elimList : (A : Type) ->
           (m : MyList A -> Type) ->
           (f1 : m (MyNil A)) ->
           (f2 : (a : A) -> (as : MyList A) -> m as -> m (MyCons A a as)) ->
           (e : MyList A) ->
           m e
elimList A m f1 f2 (MyNil A) = f1
elimList A m f1 f2 (MyCons A a as) = f2 a as (elimList A m f1 f2 as)

append : (A : Type) ->  (b : MyList A) ->  (c : MyList A) ->  MyList A
append A b c = (elimList A (\ d =>  MyList A) c
                (\ d =>  \ e =>  \ f =>  MyCons A d f)
                b)

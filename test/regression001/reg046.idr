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
elimList aA m f1 f2 (MyNil aA) = f1
elimList aA m f1 f2 (MyCons aA a as) = f2 a as (elimList aA m f1 f2 as)

append : (A : Type) ->  (b : MyList A) ->  (c : MyList A) ->  MyList A
append aA b c = (elimList aA (\ d =>  MyList aA) c
                (\ d =>  \ e =>  \ f =>  MyCons aA d f)
                b)

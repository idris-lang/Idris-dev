data Exp : Type -> Type where
     Const : {t : Type} -> t -> Exp t
     Pair : {t1,t2:Type} -> Exp t1 -> Exp t2 -> Exp (t1, t2)
     Eq : {t:Type} -> Exp t -> Exp t -> Exp Bool

foo : Exp (Exp Integer)
foo = Const (Const 0)


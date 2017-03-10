data Point : Num t => Nat -> t -> Type where
     Nil : Point Z t

data Mono : (Monoid m) => () -> Type where
     Monono : (Monoid m) => Mono {m} ()

data Mono1 : (Monoid m) => Type where
    Monono1 : (Monoid m) => Mono1 {m}

data Mono2 : (m : Type) -> Monoid m => () -> Type where
    Monono2 : (Monoid m) => Mono2 m ()

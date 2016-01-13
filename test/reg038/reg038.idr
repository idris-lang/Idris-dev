interface C t (f : t -> t) (r : t -> t -> Type) where
    g : (a : t) -> r (f a) (f a) -> r (f a) (f a)

data Foo : {t : Type} -> t -> t -> Type where
  MkFoo : {t : Type} -> {x : t} -> {y : t} -> Foo x y

implementation C t f (Foo {t = t}) where
  g x = id

data Bar : {t1 : Type} -> {t2 : Type} -> t1 -> t2 -> Type where
  MkBar : {x : t1} -> Bar x x

implementation C s f (Bar {t1 = s} {t2 = s}) where
    g x = id

implementation C s f ((=) {A = s} {B = s}) where
    g x = id

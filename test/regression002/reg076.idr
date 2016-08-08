
data Qux : a -> Type where
  Tux : String -> Qux a

data Bar : a -> Type where
  Nil : Bar a
  (:>) : Qux a -> Bar a -> Bar a

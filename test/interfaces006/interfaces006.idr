module Categories

infixr 9 .
interface Category (c: k -> k -> Type) where
  id: c x x
  (.): c y z -> c x y -> c x z

interface Category c => Functor (c: k -> k -> Type) (f: k -> k) where
  map: c x y -> c (f x) (f y)

infixr 1 =<<
interface Functor c m => Monad (c: k -> k -> Type) (m: k -> k) where
  pure: c x (m x)
  join: c (m (m x)) (m x)
  (=<<) : c x (m y) -> c (m x) (m y)

  join = (=<<) id
  (=<<) f = join . map f


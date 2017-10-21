||| Combinators from Control.Arrow

first : (a -> b) -> (a, c) -> (b, c)
first f (a, c) = (f a, c)

second : (a -> b) -> ((c, a) -> (c, b))
second f (c, a) = (c, f a)

infixr 3 ***
(***) : (a -> b) -> (a' -> b') -> ((a, a') -> (b, b'))
(***) f g (a, a') = (f a, g a')

infixr 3 &&&
(&&&) : (a -> b) -> (a -> b') -> (a -> (b, b'))
(&&&) f g x = (f x, g x)

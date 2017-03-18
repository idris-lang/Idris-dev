total
map' : (a -> b) -> List a -> List b
map' _ [] = []
map' f (x :: xs) = f x :: map' f xs

f : a
f = f


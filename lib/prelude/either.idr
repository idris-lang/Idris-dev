module prelude.either

import builtins

data Either a b = Left a | Right b

choose : (b : Bool) -> Either (so b) (so (not b))
choose True = Left oh
choose False = Right oh

either : Either a b -> (a -> c) -> (b -> c) -> c
either (Left x)  l r = l x
either (Right x) l r = r x

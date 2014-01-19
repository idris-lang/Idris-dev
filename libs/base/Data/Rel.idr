module Data.Rel

import Data.VectFun

Rel : Vect n Type -> Type
Rel ts = VectFun ts Type

liftRel : (ts : Vect k Type) -> (p : Rel ts) -> (Type -> Type) -> Type
liftRel [] p f = f p
liftRel (t :: ts) p f = (x : t) -> liftRel ts (p x) f

module Data.Rel

import Data.FunN

--------------------------------------------------------------------------------
-- Build an n-ary relation type from a Vect of Types
--------------------------------------------------------------------------------
Rel : Vect n Type -> Type
Rel ts = FunN ts Type

liftRel : (ts : Vect n Type) -> (p : Rel ts) -> (Type -> Type) -> Type
liftRel [] p f = f p
liftRel (t :: ts) p f = (x : t) -> liftRel ts (p x) f

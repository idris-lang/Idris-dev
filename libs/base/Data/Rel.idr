module Data.Rel

import Data.VectFun

Rel : Vect n Type -> Type
Rel ts = VectFun ts Type

--  ATM it seems that using this at least for Decidable results in
--  inconvenience in the form of necessity of explicit instance declarations.
--liftRel : (ts : Vect k Type) -> (p : VectFun ts Type) -> (Type -> Type) -> Type
--liftRel [] p f = f p
--liftRel (t :: ts) p f = (x : t) -> liftRel ts (p x) f
liftRel : (ts : Vect k Type) -> (p : Rel ts) -> (Type -> Type) -> Type
liftRel [] p f = f p
liftRel (t :: ts) p f = (x : t) -> liftRel ts (p x) f

module Decidable.Decidable

import Data.VectFun -- FIXME let's see if this is needed
import Data.Rel

%access public

--------------------------------------------------------------------------------
-- Typeclass for decidable n-ary Relations
--------------------------------------------------------------------------------

--DecProc : (ts : Vect k Type) -> (p : Rel ts) -> Type
--DecProc [] p = Dec p
--DecProc (t::ts) p = (x : t) -> DecProc ts (p x)
--DecProc : (ts : Vect k Type) -> (p : VectFun ts Type) -> Type
--DecProc [] p = Dec p
--DecProc (t::ts) p = (x : t) -> DecProc ts (p x)

--class Decidable (ts : Vect k Type) (p : VectFun ts Type) where
--  total decide : DecProc ts p
--class Decidable (ts : Vect k Type) (p : Rel ts) where
--  total decide : DecProc ts p
--class Decidable (ts : Vect k Type) (p : VectFun ts Type) where
--  total decide : liftRel ts p Dec
class Decidable (ts : Vect k Type) (p : Rel ts) where
  total decide : liftRel ts p Dec

{-
using (t : Type)
  class Rel (p : t) where
    total liftRel : (Type -> Type) -> Type

  class (Rel p) => Decidable (p : t) where
    total decide : liftRel {p} Dec
-}

using (P : Type, p : P)
  data Given : Dec P -> Type where
    always : Given (Yes p)

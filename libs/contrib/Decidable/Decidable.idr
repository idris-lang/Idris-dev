module Decidable.Decidable

import Data.Rel
import Data.Fun

%access public export

--------------------------------------------------------------------------------
-- Interface for decidable n-ary Relations
--------------------------------------------------------------------------------

--  Note: Implementation resolution for Decidable is likely to not work in the REPL
--        at the moment.
interface Decidable (ts : Vect k Type) (p : Rel ts) where
  total decide : liftRel ts p Dec

-- 'No such variable {k506}'
--decision : Decidable ts p => (ts : Vect k Type) -> (p : Rel ts) -> liftRel ts p Dec
--decision ts p = decide {ts} {p}

using (a : Type, x : a)
  data Given : Dec a -> Type where
    Always : Given (Yes x)

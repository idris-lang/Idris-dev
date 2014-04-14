module Idris.ASTUtils where

-- This implements just a few basic lens-like concepts to ease state updates.
-- Similar to fclabels in approach, just without the extra dependency.
--
-- We don't include an explicit export list
-- because everything here is meant to be exported.

import Control.Category
import Control.Applicative
import Control.Monad.State.Class
import Data.Maybe
import Prelude hiding (id, (.))

import Idris.Core.TT
import Idris.AbsSyntaxTree

data Field rec fld = Field
    { fget :: rec -> fld
    , fset :: fld -> rec -> rec
    }

fmodify :: Field rec fld -> (fld -> fld) -> rec -> rec
fmodify field f x = fset field (f $ fget field x) x

instance Category Field where
    id = Field id const
    Field g2 s2 . Field g1 s1 = Field (g2 . g1) (\v2 x1 -> s1 (s2 v2 $ g1 x1) x1)

fgetState :: MonadState s m => Field s a -> m a
fgetState field = gets $ fget field

fputState :: MonadState s m => Field s a -> a -> m ()
fputState field x = fmodifyState field (const x)

fmodifyState :: MonadState s m => Field s a -> (a -> a) -> m ()
fmodifyState field f = modify $ fmodify field f

-- Until now, we'd have just ad-hoc empty lists and Falses thrown around
-- whenever a new instance of a record was to be created.
--
-- This class formalises the notion of an initial value for a record.
class InitialValue a where
    initialValue :: a

-- Exact-name context lookup; uses the initial value if needed.
ctxt_lookupExact :: InitialValue a => Name -> Field (Ctxt a) a
ctxt_lookupExact n = Field
    { fget = fromMaybe initialValue . lookupCtxtExact n
    , fset = addDef n
    }


-----------------------------------
-- Individual records and fields --
-----------------------------------


-- OptInfo
----------

instance InitialValue OptInfo where
    initialValue = Optimise [] False

-- the optimisation record for the given (exact) name
ist_optimisation :: Name -> Field IState OptInfo
ist_optimisation n = ctxt_lookupExact n
    . Field idris_optimisation (\v ist -> ist{ idris_optimisation = v })

-- two fields of the optimisation record
opt_inaccessible :: Field OptInfo [(Int, Name)]
opt_inaccessible = Field inaccessible (\v opt -> opt{ inaccessible = v })

opt_detaggable :: Field OptInfo Bool
opt_detaggable = Field detaggable (\v opt -> opt{ detaggable = v })


-- CGInfo
---------

instance InitialValue CGInfo where
    initialValue = CGInfo [] [] [] [] []

-- callgraph record for the given (exact) name
ist_callgraph :: Name -> Field IState CGInfo
ist_callgraph n = ctxt_lookupExact n
    . Field idris_callgraph (\v ist -> ist{ idris_callgraph = v })

-- some fields of the CGInfo record
cg_usedpos :: Field CGInfo [(Int, [UsageReason])]
cg_usedpos = Field usedpos (\v cg -> cg{ usedpos = v })

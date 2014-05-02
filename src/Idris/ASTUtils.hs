module Idris.ASTUtils where

-- This implements just a few basic lens-like concepts to ease state updates.
-- Similar to fclabels in approach, just without the extra dependency.
--
-- We don't include an explicit export list
-- because everything here is meant to be exported.
--
-- Short synopsis:
-- ---------------
--
-- f :: Idris ()
-- f = do
--      -- these two steps:
--      detaggable <- fgetState (opt_detaggable . ist_optimisation typeName)
--      fputState (opt_detaggable . ist_optimisation typeName) (not detaggable)
--
--      -- are equivalent to:
--      fmodifyState (opt_detaggable . ist_optimisation typeName) not
--
--      -- of course, the long accessor can be put in a variable;
--      -- everything is first-class
--      let detag n = opt_detaggable . ist_optimisation n
--      fputState (detag n1) True
--      fputState (detag n2) False
--
--      -- Note that all these operations handle missing items consistently
--      -- and transparently, as prescribed by the default values included
--      -- in the definitions of the ist_* functions.
--      --
--      -- Especially, it's no longer necessary to have initial values of
--      -- data structures copied (possibly inconsistently) all over the compiler.

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

-- Exact-name context lookup; uses Nothing for deleted values (read+write!).
-- 
-- Reading a non-existing value yields Nothing,
-- writing Nothing deletes the value (if it existed).
ctxt_lookup :: Name -> Field (Ctxt a) (Maybe a)
ctxt_lookup n = Field
    { fget = lookupCtxtExact n
    , fset = \newVal -> case newVal of
        Just x  -> addDef n x
        Nothing -> deleteDefExact n
    }

-- Maybe-lens with a default value.
maybe_default :: a -> Field (Maybe a) a
maybe_default dflt = Field (fromMaybe dflt) (const . Just)


-----------------------------------
-- Individual records and fields --
-----------------------------------
--
-- These could probably be generated; let's use lazy addition for now.
--


-- OptInfo
----------

-- the optimisation record for the given (exact) name
ist_optimisation :: Name -> Field IState OptInfo
ist_optimisation n =
      maybe_default Optimise
        { inaccessible = []
        , detaggable = False
        }
    . ctxt_lookup n
    . Field idris_optimisation (\v ist -> ist{ idris_optimisation = v })

-- two fields of the optimisation record
opt_inaccessible :: Field OptInfo [(Int, Name)]
opt_inaccessible = Field inaccessible (\v opt -> opt{ inaccessible = v })

opt_detaggable :: Field OptInfo Bool
opt_detaggable = Field detaggable (\v opt -> opt{ detaggable = v })


-- CGInfo
---------

-- callgraph record for the given (exact) name
ist_callgraph :: Name -> Field IState CGInfo
ist_callgraph n =
      maybe_default CGInfo
        { argsdef = [], calls = [], scg = []
        , argsused = [], usedpos = []
        }
    . ctxt_lookup n
    . Field idris_callgraph (\v ist -> ist{ idris_callgraph = v })

-- some fields of the CGInfo record
cg_usedpos :: Field CGInfo [(Int, [UsageReason])]
cg_usedpos = Field usedpos (\v cg -> cg{ usedpos = v })

{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Module      : Idris.ASTUtils
Description : This implements just a few basic lens-like concepts to ease state updates. Similar to fclabels in approach, just without the extra dependency.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.

This implements just a few basic lens-like concepts to ease state updates.
Similar to fclabels in approach, just without the extra dependency.

We don't include an explicit export list
because everything here is meant to be exported.

Short synopsis:
---------------
@
f :: Idris ()
f = do
     -- these two steps:
     detaggable <- fgetState (opt_detaggable . ist_optimisation typeName)
     fputState (opt_detaggable . ist_optimisation typeName) (not detaggable)

     -- are equivalent to:
     fmodifyState (opt_detaggable . ist_optimisation typeName) not

     -- of course, the long accessor can be put in a variable;
     -- everything is first-class
     let detag n = opt_detaggable . ist_optimisation n
     fputState (detag n1) True
     fputState (detag n2) False

     -- Note that all these operations handle missing items consistently
     -- and transparently, as prescribed by the default values included
     -- in the definitions of the ist_* functions.
     --
     -- Especially, it's no longer necessary to have initial values of
     -- data structures copied (possibly inconsistently) all over the compiler.
@
-}
module Idris.ASTUtils(
    Field(), cg_usedpos, ctxt_lookup, fgetState, fmodifyState
  , fputState, idris_fixities, ist_callgraph, ist_optimisation
  , known_interfaces, known_terms, opt_detaggable, opt_inaccessible
  , opt_forceable, opts_idrisCmdline, repl_definitions
  ) where

import Idris.AbsSyntaxTree
import Idris.Core.Evaluate
import Idris.Core.TT

import Prelude hiding (id, (.))

import Control.Applicative
import Control.Category
import Control.Monad.State.Class
import Data.Maybe

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

-- | Exact-name context lookup; uses Nothing for deleted values
-- (read+write!).
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

-- | the optimisation record for the given (exact) name
ist_optimisation :: Name -> Field IState OptInfo
ist_optimisation n =
      maybe_default Optimise
        { inaccessible = []
        , detaggable = False
        , forceable = []
        }
    . ctxt_lookup n
    . Field idris_optimisation (\v ist -> ist{ idris_optimisation = v })

-- | two fields of the optimisation record
opt_inaccessible :: Field OptInfo [(Int, Name)]
opt_inaccessible = Field inaccessible (\v opt -> opt{ inaccessible = v })

opt_detaggable :: Field OptInfo Bool
opt_detaggable = Field detaggable (\v opt -> opt{ detaggable = v })

opt_forceable :: Field OptInfo [Int]
opt_forceable = Field forceable (\v opt -> opt{ forceable = v })

-- | callgraph record for the given (exact) name
ist_callgraph :: Name -> Field IState CGInfo
ist_callgraph n =
      maybe_default CGInfo
        { calls = [], allCalls = Nothing, scg = [], usedpos = []
        }
    . ctxt_lookup n
    . Field idris_callgraph (\v ist -> ist{ idris_callgraph = v })

cg_usedpos :: Field CGInfo [(Int, [UsageReason])]
cg_usedpos = Field usedpos (\v cg -> cg{ usedpos = v })

-- | Commandline flags
opts_idrisCmdline :: Field IState [Opt]
opts_idrisCmdline =
      Field opt_cmdline (\v opts -> opts{ opt_cmdline = v })
    . Field idris_options (\v ist -> ist{ idris_options = v })

-- | TT Context
--
-- This has a terrible name, but I'm not sure of a better one that
-- isn't confusingly close to tt_ctxt
known_terms :: Field IState (Ctxt (Def, RigCount, Injectivity, Accessibility, Totality, MetaInformation))
known_terms = Field (definitions . tt_ctxt)
                    (\v state -> state {tt_ctxt = (tt_ctxt state) {definitions = v}})

known_interfaces :: Field IState (Ctxt InterfaceInfo)
known_interfaces = Field idris_interfaces (\v state -> state {idris_interfaces = idris_interfaces state})


-- | Names defined at the repl
repl_definitions :: Field IState [Name]
repl_definitions = Field idris_repl_defs (\v state -> state {idris_repl_defs = v})

-- | Fixity declarations in an IState
idris_fixities :: Field IState [FixDecl]
idris_fixities = Field idris_infixes (\v state -> state {idris_infixes = v})

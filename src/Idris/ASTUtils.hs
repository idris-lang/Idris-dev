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
--      detaggable <- fget $ opt_detaggable . ist_optimisation typeName
--      fput (opt_detaggable . ist_optimisation typeName) (not detaggable)
--
--      -- are equivalent to:
--      fmodify (opt_detaggable . ist_optimisation typeName) not
--
--      -- Of course, the long accessor can be put in a variable;
--      -- everything is first-class
--      let detag n = opt_detaggable . ist_optimisation n
--      fput (detag n1) True
--      fput (detag n2) False
--
--      -- expressed more succintly as
--      fsetFlag   $ detag n1
--      fclearFlag $ detag n2
--
--      -- or:
--      detag n1 .= True
--      detag n2 .= False
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
import Idris.Core.Evaluate
import Idris.AbsSyntaxTree

data Field rec fld = Field
    { fgetField :: rec -> fld
    , fsetField :: fld -> rec -> rec
    }

fmodifyField :: Field rec fld -> (fld -> fld) -> rec -> rec
fmodifyField field f x = fsetField field (f $ fgetField field x) x

instance Category Field where
    id = Field id const
    Field g2 s2 . Field g1 s1 = Field (g2 . g1) (\v2 x1 -> s1 (s2 v2 $ g1 x1) x1)

fget :: MonadState s m => Field s a -> m a
fget field = gets $ fgetField field

fput :: MonadState s m => Field s a -> a -> m ()
fput field x = fmodify field (const x)

fmodify :: MonadState s m => Field s a -> (a -> a) -> m ()
fmodify field f = modify $ fmodifyField field f

-- Control.Category.. is infixr 7
infix 4 .=
(.=) :: MonadState s m => Field s a -> a -> m ()
(.=) = fput

fsetFlag :: MonadState s m => Field s Bool -> m ()
fsetFlag field = field .= True

fclearFlag :: MonadState s m => Field s Bool -> m ()
fclearFlag field = field .= False

-- Exact-name context lookup; uses Nothing for deleted values (read+write!).
-- 
-- Reading a non-existing value yields Nothing,
-- writing Nothing deletes the value (if it existed).
ctxt_lookup :: Name -> Field (Ctxt a) (Maybe a)
ctxt_lookup n = Field
    { fgetField = lookupCtxtExact n
    , fsetField = \newVal -> case newVal of
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


-- Options
----------

ist_options :: Field IState IOption
ist_options = Field idris_options (\v ist -> ist{ idris_options = v })

ist_parserTrace :: Field IState [ParserTraceItem]
ist_parserTrace = Field idris_parserTrace (\v ist -> ist{ idris_parserTrace = v })


-- Commandline flags
--------------------

opts_idrisCmdline :: Field IOption [Opt]
opts_idrisCmdline = Field opt_cmdline (\v opts -> opts{ opt_cmdline = v })

opts_parserTrace :: Field IOption Bool
opts_parserTrace = Field opt_parserTrace (\v opts -> opts{ opt_parserTrace = v })

opts_warnReach :: Field IOption Bool
opts_warnReach = Field opt_warnReach (\v opts -> opts{ opt_warnReach = v })

-- TT Context
-------------
-- This has a terrible name, but I'm not sure of a better one that isn't
-- confusingly close to tt_ctxt
known_terms :: Field IState (Ctxt (Def, Accessibility, Totality, MetaInformation))
known_terms = Field (definitions . tt_ctxt)
                    (\v state -> state {tt_ctxt = (tt_ctxt state) {definitions = v}})

known_classes :: Field IState (Ctxt ClassInfo)
known_classes = Field idris_classes (\v state -> state {idris_classes = idris_classes state})


-- Names defined at the repl
----------------------------
repl_definitions :: Field IState [Name]
repl_definitions = Field idris_repl_defs (\v state -> state {idris_repl_defs = v})

-- Fixity declarations in an IState
idris_fixities :: Field IState [FixDecl]
idris_fixities = Field idris_infixes (\v state -> state {idris_infixes = v})

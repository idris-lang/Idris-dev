{-|
Module      : Idris.AbsSyntaxTree
Description : Core data definitions used in Idris.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, DeriveGeneric, PatternGuards #-}

module Idris.AbsSyntaxTree where

import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Docstrings
import IRTS.CodegenCommon
import IRTS.Lang
import Util.DynamicLinker
import Util.Pretty

import Idris.Colours

import System.IO

import Prelude hiding (Foldable, Traversable, (<$>))

import Control.Applicative ((<|>))
import qualified Control.Monad.Trans.Class as Trans (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Char
import Data.Data (Data)

import Data.Foldable (Foldable)
import Data.Function (on)
import Data.Generics.Uniplate.Data (children, universe)
import Data.List hiding (group)
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Traversable (Traversable)
import Data.Typeable
import GHC.Generics (Generic)
import Network.Socket (PortNumber)


data ElabWhat = ETypes | EDefns | EAll
  deriving (Show, Eq)

-- | Data to pass to recursively called elaborators; e.g. for where blocks,
-- paramaterised declarations, etc.
--
-- rec_elabDecl is used to pass the top level elaborator into other elaborators,
-- so that we can have mutually recursive elaborators in separate modules without
-- having to muck about with cyclic modules.
data ElabInfo = EInfo {
    params    :: [(Name, PTerm)]
  , inblock   :: Ctxt [Name]      -- ^ names in the block, and their params
  , liftname  :: Name -> Name
  , namespace :: [String]
  , elabFC    :: Maybe FC
  , constraintNS :: String        -- ^ filename for adding to constraint variables
  , pe_depth  :: Int
  , noCaseLift :: [Name]         -- ^ types which shouldn't be made arguments to case
  -- | We may, recursively, collect transformations to do on the rhs,
  -- e.g. rewriting recursive calls to functions defined by 'with'
  , rhs_trans :: PTerm -> PTerm
  , rec_elabDecl :: ElabWhat -> ElabInfo -> PDecl -> Idris ()
  }

toplevel :: ElabInfo
toplevel = EInfo [] emptyContext id [] Nothing "(toplevel)" 0 [] id (\_ _ _ -> fail "Not implemented")

toplevelWith :: String -> ElabInfo
toplevelWith ns = EInfo [] emptyContext id [] Nothing ns 0 [] id (\_ _ _ -> fail "Not implemented")

eInfoNames :: ElabInfo -> [Name]
eInfoNames info = map fst (params info) ++ M.keys (inblock info)

data IOption = IOption {
    opt_logLevel     :: Int
  , opt_logcats      :: [LogCat]      -- ^ List of logging categories.
  , opt_typecase     :: Bool
  , opt_typeintype   :: Bool
  , opt_coverage     :: Bool
  , opt_showimp      :: Bool          -- ^ show implicits
  , opt_errContext   :: Bool
  , opt_repl         :: Bool
  , opt_verbose      :: Int
  , opt_nobanner     :: Bool
  , opt_quiet        :: Bool
  , opt_codegen      :: Codegen
  , opt_outputTy     :: OutputType
  , opt_ibcsubdir    :: FilePath
  , opt_importdirs   :: [FilePath]
  , opt_sourcedirs   :: [FilePath]
  , opt_triple       :: String
  , opt_cpu          :: String
  , opt_cmdline      :: [Opt]          -- ^ remember whole command line
  , opt_origerr      :: Bool
  , opt_autoSolve    :: Bool           -- ^ automatically apply "solve" tactic in prover
  , opt_autoImport   :: [FilePath]     -- ^ List of modules to auto import i.e. `Builtins+Prelude`
  , opt_optimise     :: [Optimisation]
  , opt_printdepth   :: Maybe Int
  , opt_evaltypes    :: Bool           -- ^ normalise types in `:t`
  , opt_desugarnats  :: Bool
  , opt_autoimpls    :: Bool
  } deriving (Show, Eq, Generic)

defaultOpts :: IOption
defaultOpts = IOption { opt_logLevel   = 0
                      , opt_logcats    = []
                      , opt_typecase   = False
                      , opt_typeintype = False
                      , opt_coverage   = True
                      , opt_showimp    = False
                      , opt_errContext = False
                      , opt_repl       = True
                      , opt_verbose    = 0
                      , opt_nobanner   = False
                      , opt_quiet      = False
                      , opt_codegen    = Via IBCFormat "c"
                      , opt_outputTy   = Executable
                      , opt_ibcsubdir  = ""
                      , opt_importdirs = []
                      , opt_sourcedirs = []
                      , opt_triple     = ""
                      , opt_cpu        = ""
                      , opt_cmdline    = []
                      , opt_origerr    = False
                      , opt_autoSolve  = True
                      , opt_autoImport = []
                      , opt_optimise   = defaultOptimise
                      , opt_printdepth = Just 5000
                      , opt_evaltypes  = True
                      , opt_desugarnats = False
                      , opt_autoimpls  = True
                      }

data PPOption = PPOption {
    ppopt_impl        :: Bool -- ^ whether to show implicits
  , ppopt_desugarnats :: Bool
  , ppopt_pinames     :: Bool -- ^ whether to show names in pi bindings
  , ppopt_depth       :: Maybe Int
  } deriving (Show)

data Optimisation = PETransform -- ^ partial eval and associated transforms
  deriving (Show, Eq, Generic)

defaultOptimise :: [Optimisation]
defaultOptimise = []

-- | Pretty printing options with default verbosity.
defaultPPOption :: PPOption
defaultPPOption = PPOption {
    ppopt_impl = False
  , ppopt_desugarnats = False
  , ppopt_pinames = False
  , ppopt_depth = Nothing
  }

-- | Pretty printing options with the most verbosity.
verbosePPOption :: PPOption
verbosePPOption = PPOption {
    ppopt_impl = True
  , ppopt_desugarnats = True
  , ppopt_pinames = True
  , ppopt_depth = Nothing
  }

-- | Get pretty printing options from the big options record.
ppOption :: IOption -> PPOption
ppOption opt = PPOption {
    ppopt_impl = opt_showimp opt
  , ppopt_pinames = False
  , ppopt_depth = opt_printdepth opt
  , ppopt_desugarnats = opt_desugarnats opt
  }

-- | Get pretty printing options from an idris state record.
ppOptionIst :: IState -> PPOption
ppOptionIst = ppOption . idris_options

data LanguageExt = TypeProviders | ErrorReflection | UniquenessTypes
                 | DSLNotation   | ElabReflection  | FCReflection
                 | LinearTypes
  deriving (Show, Eq, Read, Ord, Generic)

-- | The output mode in use
data OutputMode = RawOutput Handle       -- ^ Print user output directly to the handle
                | IdeMode Integer Handle -- ^ Send IDE output for some request ID to the handle
                deriving Show

-- | How wide is the console?
data ConsoleWidth = InfinitelyWide -- ^ Have pretty-printer assume that lines should not be broken
                  | ColsWide Int   -- ^ Manually specified - must be positive
                  | AutomaticWidth -- ^ Attempt to determine width, or 80 otherwise
   deriving (Show, Eq, Generic)

-- | If a function has no totality annotation, what do we assume?
data DefaultTotality = DefaultCheckingTotal    -- ^ Total
                     | DefaultCheckingPartial  -- ^ Partial
                     | DefaultCheckingCovering -- ^Total coverage, but may diverge
  deriving (Show, Eq, Generic)

-- | Configuration options for interactive editing.
data InteractiveOpts = InteractiveOpts {
    interactiveOpts_indentWith :: Int
  , interactiveOpts_indentClause :: Int
} deriving (Show, Generic)

-- | The global state used in the Idris monad
data IState = IState {
    tt_ctxt            :: Context            -- ^ All the currently defined names and their terms
  , idris_constraints  :: S.Set ConstraintFC -- ^ A list of universe constraints and their corresponding source locations
  , idris_infixes      :: [FixDecl]          -- ^ Currently defined infix operators
  , idris_implicits    :: Ctxt [PArg]
  , idris_statics      :: Ctxt [Bool]
  , idris_interfaces   :: Ctxt InterfaceInfo
  , idris_openimpls    :: [Name]             -- ^ Privileged implementations, will resolve immediately
  , idris_records      :: Ctxt RecordInfo
  , idris_dsls         :: Ctxt DSL
  , idris_optimisation :: Ctxt OptInfo
  , idris_datatypes    :: Ctxt TypeInfo
  , idris_namehints    :: Ctxt [Name]

  -- | list of lhs/rhs, and a list of missing clauses. These are not
  -- exported.
  , idris_patdefs       :: Ctxt ([([(Name, Term)], Term, Term)], [PTerm])
  , idris_flags         :: Ctxt [FnOpt]
  , idris_callgraph     :: Ctxt CGInfo  -- ^ name, args used in each pos
  , idris_docstrings    :: Ctxt (Docstring DocTerm, [(Name, Docstring DocTerm)])

  -- | module documentation is saved in a special MN so the context
  -- mechanism can be used for disambiguation.
  , idris_moduledocs    :: Ctxt (Docstring DocTerm)
  , idris_tyinfodata    :: Ctxt TIData
  , idris_fninfo        :: Ctxt FnInfo
  , idris_transforms    :: Ctxt [(Term, Term)]
  , idris_autohints     :: Ctxt [Name]
  , idris_totcheck      :: [(FC, Name)] -- ^ names to check totality on
  , idris_defertotcheck :: [(FC, Name)] -- ^ names to check at the end
  , idris_totcheckfail  :: [(FC, String)]
  , idris_options       :: IOption
  , idris_name          :: Int
  , idris_lineapps      :: [((FilePath, Int), PTerm)] -- ^ Full application LHS on source line

  -- | The currently defined but not proven metavariables. The Int is
  -- the number of vars to display as a context, the Maybe Name is its
  -- top-level function, the [Name] is the list of local variables
  -- available for proof search and the Bools are whether :p is
  -- allowed, and whether the variable is definable at all
  -- (Metavariables are not definable if they are applied in a term
  -- which still has hole bindings)
  , idris_metavars      :: [(Name, (Maybe Name, Int, [Name], Bool, Bool))]
  , idris_coercions              :: [Name]
  , idris_errRev                 :: [(Term, Term)]
  , idris_errReduce              :: [Name]
  , syntax_rules                 :: SyntaxRules
  , syntax_keywords              :: [String]
  , imported                     :: [FilePath]                    -- ^ The imported modules
  , idris_scprims                :: [(Name, (Int, PrimFn))]
  , idris_objs                   :: [(Codegen, FilePath)]
  , idris_libs                   :: [(Codegen, String)]
  , idris_cgflags                :: [(Codegen, String)]
  , idris_hdrs                   :: [(Codegen, String)]
  , idris_imported               :: [(FilePath, Bool)]            -- ^ Imported ibc file names, whether public
  , proof_list                   :: [(Name, (Bool, [String]))]
  , errSpan                      :: Maybe FC
  , parserWarnings               :: [(FC, Err)]
  , lastParse                    :: Maybe Name
  , indent_stack                 :: [Int]
  , brace_stack                  :: [Maybe Int]
  , lastTokenSpan                :: Maybe FC                      -- ^ What was the span of the latest token parsed?
  , idris_parsedSpan             :: Maybe FC
  , hide_list                    :: Ctxt Accessibility
  , default_access               :: Accessibility
  , default_total                :: DefaultTotality
  , ibc_write                    :: [IBCWrite]
  , compiled_so                  :: Maybe String
  , idris_dynamic_libs           :: [DynamicLib]
  , idris_language_extensions    :: [LanguageExt]
  , idris_outputmode             :: OutputMode
  , idris_colourRepl             :: Bool
  , idris_colourTheme            :: ColourTheme
  , idris_errorhandlers          :: [Name]                         -- ^ Global error handlers
  , idris_nameIdx                :: (Int, Ctxt (Int, Name))
  , idris_function_errorhandlers :: Ctxt (M.Map Name (S.Set Name)) -- ^ Specific error handlers
  , module_aliases               :: M.Map [T.Text] [T.Text]
  , idris_consolewidth           :: ConsoleWidth                   -- ^ How many chars wide is the console?
  , idris_postulates             :: S.Set Name
  , idris_externs                :: S.Set (Name, Int)
  , idris_erasureUsed            :: [(Name, Int)]                  -- ^ Function/constructor name, argument position is used

  -- | List of names that were defined in the repl, and can be re-/un-defined
  , idris_repl_defs              :: [Name]

  -- | Stack of names currently being elaborated, Bool set if it's an
  -- implementation (implementations appear twice; also as a function name)
  , elab_stack                   :: [(Name, Bool)]


  , idris_symbols                :: M.Map Name Name           -- ^ Symbol table (preserves sharing of names)
  , idris_exports                :: [Name]                    -- ^ Functions with ExportList
  , idris_highlightedRegions     :: [(FC, OutputAnnotation)]  -- ^ Highlighting information to output
  , idris_parserHighlights       :: [(FC, OutputAnnotation)]  -- ^ Highlighting information from the parser
  , idris_deprecated             :: Ctxt String               -- ^ Deprecated names and explanation
  , idris_inmodule               :: S.Set Name                -- ^ Names defined in current module
  , idris_ttstats                :: M.Map Term (Int, Term)
  , idris_fragile                :: Ctxt String               -- ^ Fragile names and explanation.
  , idris_interactiveOpts        :: InteractiveOpts
  } deriving Generic

-- Required for parsers library, and therefore trifecta
instance Show IState where
  show = const "{internal state}"

data SizeChange = Smaller | Same | Bigger | Unknown
    deriving (Show, Eq, Generic)
{-!
deriving instance Binary SizeChange
!-}

type SCGEntry = (Name, [Maybe (Int, SizeChange)])
type UsageReason = (Name, Int)  -- fn_name, its_arg_number

data CGInfo = CGInfo {
    calls    :: [Name] -- Immediate calls
  , allCalls :: Maybe [Name] -- Calls and descendents (built as required, for PE)
  , scg      :: [SCGEntry]
  , usedpos  :: [(Int, [UsageReason])]
  } deriving (Show, Generic)
{-!
deriving instance Binary CGInfo
!-}

primDefs :: [Name]
primDefs = [ sUN "unsafePerformPrimIO"
           , sUN "mkLazyForeignPrim"
           , sUN "mkForeignPrim"
           , sUN "void"
           , sUN "assert_unreachable"
           , sUN "idris_crash"
           ]

-- information that needs writing for the current module's .ibc file
data IBCWrite = IBCFix FixDecl
              | IBCImp Name
              | IBCStatic Name
              | IBCInterface Name
              | IBCRecord Name
              | IBCImplementation Bool Bool Name Name
              | IBCDSL Name
              | IBCData Name
              | IBCOpt Name
              | IBCMetavar Name
              | IBCSyntax Syntax
              | IBCKeyword String
              | IBCImport (Bool, FilePath) -- ^ True = import public
              | IBCImportDir FilePath
              | IBCSourceDir FilePath
              | IBCObj Codegen FilePath
              | IBCLib Codegen String
              | IBCCGFlag Codegen String
              | IBCDyLib String
              | IBCHeader Codegen String
              | IBCAccess Name Accessibility
              | IBCMetaInformation Name MetaInformation
              | IBCTotal Name Totality
              | IBCInjective Name Injectivity
              | IBCFlags Name
              | IBCFnInfo Name FnInfo
              | IBCTrans Name (Term, Term)
              | IBCErrRev (Term, Term)
              | IBCErrReduce Name
              | IBCCG Name
              | IBCDoc Name
              | IBCCoercion Name
              | IBCDef Name -- ^ The main context.
              | IBCNameHint (Name, Name)
              | IBCLineApp FilePath Int PTerm
              | IBCErrorHandler Name
              | IBCFunctionErrorHandler Name Name Name
              | IBCPostulate Name
              | IBCExtern (Name, Int)
              | IBCTotCheckErr FC String
              | IBCParsedRegion FC
              | IBCModDocs Name -- ^ The name is the special name used to track module docs
              | IBCUsage (Name, Int)
              | IBCExport Name
              | IBCAutoHint Name Name
              | IBCDeprecate Name String
              | IBCFragile Name String
              | IBCConstraint FC UConstraint
  deriving (Show, Generic)

initialInteractiveOpts :: InteractiveOpts
initialInteractiveOpts = InteractiveOpts {
    interactiveOpts_indentWith = 2
  , interactiveOpts_indentClause = 2
}

-- | The initial state for the compiler
idrisInit :: IState
idrisInit = IState initContext S.empty []
                   emptyContext emptyContext emptyContext [] emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext
                   [] [] [] defaultOpts 6 [] [] [] [] [] emptySyntaxRules [] [] [] [] [] [] []
                   [] [] Nothing [] Nothing [] [] Nothing Nothing emptyContext Private DefaultCheckingPartial [] Nothing [] []
                   (RawOutput stdout) True defaultTheme [] (0, emptyContext) emptyContext M.empty
                   AutomaticWidth S.empty S.empty [] [] [] M.empty [] [] []
                   emptyContext S.empty M.empty emptyContext initialInteractiveOpts


-- | The monad for the main REPL - reading and processing files and
-- updating global state (hence the IO inner monad).
--
-- @
--     type Idris = WriterT [Either String (IO ())] (State IState a))
-- @
--
type Idris = StateT IState (ExceptT Err IO)

catchError :: Idris a -> (Err -> Idris a) -> Idris a
catchError = liftCatch catchE

throwError :: Err -> Idris a
throwError = Trans.lift . throwE

-- Commands in the REPL

data Codegen = Via IRFormat String
             | Bytecode
    deriving (Show, Eq, Generic)

data IRFormat = IBCFormat | JSONFormat deriving (Show, Eq, Generic)

data HowMuchDocs = FullDocs | OverviewDocs

data OutputFmt = HTMLOutput | LaTeXOutput

-- | Recognised logging categories for the Idris compiler.
--
-- @TODO add in sub categories.
data LogCat = IParse
            | IElab
            | ICodeGen
            | IErasure
            | ICoverage
            | IIBC
            deriving (Show, Eq, Ord, Generic)

strLogCat :: LogCat -> String
strLogCat IParse    = "parser"
strLogCat IElab     = "elab"
strLogCat ICodeGen  = "codegen"
strLogCat IErasure  = "erasure"
strLogCat ICoverage = "coverage"
strLogCat IIBC      = "ibc"

codegenCats :: [LogCat]
codegenCats =  [ICodeGen]

parserCats :: [LogCat]
parserCats = [IParse]

elabCats :: [LogCat]
elabCats = [IElab]

loggingCatsStr :: String
loggingCatsStr = unlines
    [ (strLogCat IParse)
    , (strLogCat IElab)
    , (strLogCat ICodeGen)
    , (strLogCat IErasure)
    , (strLogCat ICoverage)
    , (strLogCat IIBC)
    ]


data ElabShellCmd = EQED
                  | EAbandon
                  | EUndo
                  | EProofState
                  | EProofTerm
                  | EEval PTerm
                  | ECheck PTerm
                  | ESearch PTerm
                  | EDocStr (Either Name Const)
  deriving (Show, Eq)

data Opt = Filename String
         | Quiet
         | NoBanner
         | ColourREPL Bool
         | Idemode
         | IdemodeSocket
         | IndentWith Int
         | IndentClause Int
         | ShowAll
         | ShowLibs
         | ShowLibDir
         | ShowDocDir
         | ShowIncs
         | ShowPkgs
         | ShowLoggingCats
         | NoBasePkgs
         | NoPrelude
         | NoBuiltins -- only for the really primitive stuff!
         | NoREPL
         | OLogging Int
         | OLogCats [LogCat]
         | Output String
         | Interface
         | TypeCase
         | TypeInType
         | DefaultTotal
         | DefaultPartial
         | WarnPartial
         | WarnReach
         | AuditIPkg
         | EvalTypes
         | NoCoverage
         | ErrContext
         | ShowImpl
         | Verbose Int
         | Port REPLPort -- ^ REPL TCP port
         | IBCSubDir String
         | ImportDir String
         | SourceDir String
         | PkgBuild String
         | PkgInstall String
         | PkgClean String
         | PkgCheck String
         | PkgREPL String
         | PkgDocBuild String -- IdrisDoc
         | PkgDocInstall String
         | PkgTest String
         | PkgIndex FilePath
         | WarnOnly
         | Pkg String
         | BCAsm String
         | DumpDefun String
         | DumpCases String
         | UseCodegen Codegen
         | CodegenArgs String
         | OutputTy OutputType
         | Extension LanguageExt
         | InterpretScript String
         | EvalExpr String
         | TargetTriple String
         | TargetCPU String
         | OptLevel Int
         | AddOpt Optimisation
         | RemoveOpt Optimisation
         | Client String
         | ShowOrigErr
         | AutoWidth -- ^ Automatically adjust terminal width
         | AutoSolve -- ^ Automatically issue "solve" tactic in old-style interactive prover
         | UseConsoleWidth ConsoleWidth
         | DumpHighlights
         | DesugarNats
         | NoElimDeprecationWarnings      -- ^ Don't show deprecation warnings for %elim
         | NoOldTacticDeprecationWarnings -- ^ Don't show deprecation warnings for old-style tactics
    deriving (Show, Eq, Generic)

data REPLPort = DontListen | ListenPort PortNumber
  deriving (Eq, Generic, Show)

-- Parsed declarations

data Fixity = Infixl  { prec :: Int }
            | Infixr  { prec :: Int }
            | InfixN  { prec :: Int }
            | PrefixN { prec :: Int }
    deriving (Eq, Generic)
{-!
deriving instance Binary Fixity
!-}

instance Show Fixity where
    show (Infixl i)  = "infixl " ++ show i
    show (Infixr i)  = "infixr " ++ show i
    show (InfixN i)  = "infix "  ++ show i
    show (PrefixN i) = "prefix " ++ show i

data FixDecl = Fix Fixity String
    deriving (Eq, Generic)

instance Show FixDecl where
  show (Fix f s) = show f ++ " " ++ s

{-!
deriving instance Binary FixDecl
!-}

instance Ord FixDecl where
    compare (Fix x _) (Fix y _) = compare (prec x) (prec y)


data Static = Static | Dynamic
  deriving (Show, Eq, Ord, Data, Generic, Typeable)
{-!
deriving instance Binary Static
!-}

-- ^ Mark bindings with their explicitness, and laziness
data Plicity = Imp { pargopts  :: [ArgOpt]
                   , pstatic   :: Static
                   , pparam    :: Bool
                   , pscoped   :: Maybe ImplicitInfo -- ^ Nothing, if top level
                   , pinsource :: Bool               -- ^ Explicitly written in source
                   , pcount    :: RigCount
                   }
             | Exp { pargopts :: [ArgOpt]
                   , pstatic  :: Static
                   , pparam   :: Bool -- ^ this is a param (rather than index)
                   , pcount    :: RigCount
                   }
             | Constraint { pargopts :: [ArgOpt]
                          , pstatic :: Static
                          , pcount    :: RigCount
                         }
             | TacImp { pargopts :: [ArgOpt]
                      , pstatic  :: Static
                      , pscript  :: PTerm
                      , pcount    :: RigCount
                      }
             deriving (Show, Eq, Ord, Data, Generic, Typeable)

{-!
deriving instance Binary Plicity
!-}

is_scoped :: Plicity -> Maybe ImplicitInfo
is_scoped (Imp _ _ _ s _ _) = s
is_scoped _                 = Nothing

-- Top level implicit
impl              :: Plicity
impl              = Imp [] Dynamic False (Just (Impl False True False)) False RigW
-- Machine generated top level implicit
impl_gen          :: Plicity
impl_gen          = Imp [] Dynamic False (Just (Impl False True True)) False RigW

-- Scoped implicits
forall_imp        :: Plicity
forall_imp        = Imp [] Dynamic False (Just (Impl False False True)) False RigW
forall_constraint :: Plicity
forall_constraint = Imp [] Dynamic False (Just (Impl True False True)) False RigW

expl              :: Plicity
expl              = Exp [] Dynamic False RigW
expl_param        :: Plicity
expl_param        = Exp [] Dynamic True RigW

constraint        :: Plicity
constraint        = Constraint [] Static RigW

tacimpl           :: PTerm -> Plicity
tacimpl t         = TacImp [] Dynamic t RigW

data FnOpt = Inlinable -- ^ always evaluate when simplifying
           | TotalFn | PartialFn | CoveringFn
           | AllGuarded -- ^ all delayed arguments guaranteed guarded by constructors
           | AssertTotal

           -- | interface dictionary, eval only when a function
           -- argument, and further evaluation results.
           | Dictionary
           | OverlappingDictionary -- ^ Interface dictionary which may overlap
           | Implicit                       -- ^ implicit coercion
           | NoImplicit                     -- ^ do not apply implicit coercions
           | CExport String                 -- ^ export, with a C name
           | ErrorHandler                   -- ^ an error handler for use with the ErrorReflection extension
           | ErrorReverse                   -- ^ attempt to reverse normalise before showing in error
           | ErrorReduce                    -- ^ unfold definition before showing an error
           | Reflection                     -- ^ a reflecting function, compile-time only
           | Specialise [(Name, Maybe Int)] -- ^ specialise it, freeze these names
           | Constructor -- ^ Data constructor type
           | AutoHint    -- ^ use in auto implicit search
           | PEGenerated -- ^ generated by partial evaluator
           | StaticFn    -- ^ Marked static, to be evaluated by partial evaluator
    deriving (Show, Eq, Generic)
{-!
deriving instance Binary FnOpt
!-}

type FnOpts = [FnOpt]

inlinable :: FnOpts -> Bool
inlinable = elem Inlinable

dictionary :: FnOpts -> Bool
dictionary = elem Dictionary


-- | Type provider - what to provide
data ProvideWhat' t = ProvTerm t t     -- ^ the first is the goal type, the second is the term
                    | ProvPostulate t  -- ^ goal type must be Type, so only term
    deriving (Show, Eq, Functor, Generic)

type ProvideWhat = ProvideWhat' PTerm

-- | Top-level declarations such as compiler directives, definitions,
-- datatypes and interfaces.
data PDecl' t
   -- | Fixity declaration
   = PFix FC Fixity [String]
   -- | Type declaration (last FC is precise name location)
   | PTy (Docstring (Either Err t)) [(Name, Docstring (Either Err t))] SyntaxInfo FC FnOpts Name FC t
   -- | Postulate, second FC is precise name location
   | PPostulate Bool -- external def if true
          (Docstring (Either Err t)) SyntaxInfo FC FC FnOpts Name t
   -- | Pattern clause
   | PClauses FC FnOpts Name [PClause' t]
   -- | Top level constant
   | PCAF FC Name t
   -- | Data declaration.
   | PData (Docstring (Either Err t)) [(Name, Docstring (Either Err t))] SyntaxInfo FC DataOpts (PData' t)
   -- | Params block
   | PParams FC [(Name, t)] [PDecl' t]
   -- | Open block/declaration
   | POpenInterfaces FC [Name] [PDecl' t]
   -- | New namespace, where FC is accurate location of the namespace
   -- in the file
   | PNamespace String FC [PDecl' t]
   -- | Record name.
   | PRecord (Docstring (Either Err t)) SyntaxInfo FC DataOpts
             Name                 -- Record name
             FC                   -- Record name precise location
             [(Name, FC, Plicity, t)] -- Parameters, where FC is precise name span
             [(Name, Docstring (Either Err t))] -- Param Docs
             [(Maybe (Name, FC), Plicity, t, Maybe (Docstring (Either Err t)))] -- Fields
             (Maybe (Name, FC)) -- Optional constructor name and location
             (Docstring (Either Err t)) -- Constructor doc
             SyntaxInfo -- Constructor SyntaxInfo

   -- | Interface: arguments are documentation, syntax info, source
   -- location, constraints, interface name, interface name location,
   -- parameters, method declarations, optional constructor name
   | PInterface (Docstring (Either Err t)) SyntaxInfo FC
            [(Name, t)]                        -- constraints
            Name                               -- interface name
            FC                                 -- accurate location of interface name
            [(Name, FC, t)]                    -- parameters and precise locations
            [(Name, Docstring (Either Err t))] -- parameter docstrings
            [(Name, FC)]                       -- determining parameters and precise locations
            [PDecl' t]                         -- declarations
            (Maybe (Name, FC))                 -- implementation constructor name and location
            (Docstring (Either Err t))         -- implementation constructor docs

   -- | Implementation declaration: arguments are documentation, syntax
   -- info, source location, constraints, interface name, parameters, full
   -- Implementation type, optional explicit name, and definitions
   | PImplementation (Docstring (Either Err t))         -- Implementation docs
                     [(Name, Docstring (Either Err t))] -- Parameter docs
                     SyntaxInfo
                     FC [(Name, t)]                     -- constraints
                     [Name]                             -- parent dictionaries to search for constraints
                     Accessibility
                     FnOpts
                     Name                               -- interface
                     FC                                 -- precise location of interface
                     [t]                                -- parameters
                     [(Name, t)]                        -- Extra names in scope in the body
                     t                                  -- full Implementation type
                     (Maybe Name)                       -- explicit name
                     [PDecl' t]
   | PDSL     Name (DSL' t) -- ^ DSL declaration
   | PSyntax  FC Syntax     -- ^ Syntax definition
   | PMutual  FC [PDecl' t] -- ^ Mutual block
   | PDirective Directive   -- ^ Compiler directive.

   -- | Type provider. The first t is the type, the second is the
   -- term. The second FC is precise highlighting location.
   | PProvider (Docstring (Either Err t)) SyntaxInfo FC FC (ProvideWhat' t) Name

   -- | Source-to-source transformation rule. If bool is True, lhs and
   -- rhs must be convertible.
   | PTransform FC Bool t t

   -- | FC is decl-level, for errors, and Strings represent the
   -- namespace
   | PRunElabDecl FC t [String]
 deriving (Functor, Generic)
{-!
deriving instance Binary PDecl'
!-}

-- | The set of source directives
data Directive = DLib Codegen String
               | DLink Codegen String
               | DFlag Codegen String
               | DInclude Codegen String
               | DHide Name
               | DFreeze Name
               | DThaw Name
               | DInjective Name
               | DSetTotal Name -- assert totality after checking
               | DAccess Accessibility
               | DDefault DefaultTotality
               | DLogging Integer
               | DDynamicLibs [String]
               | DNameHint Name FC [(Name, FC)]
               | DErrorHandlers Name FC Name FC [(Name, FC)]
               | DLanguage LanguageExt
               | DDeprecate Name String
               | DFragile Name String
               | DAutoImplicits Bool
               | DUsed FC Name Name
  deriving Generic

-- | A set of instructions for things that need to happen in IState
-- after a term elaboration when there's been reflected elaboration.
data RDeclInstructions = RTyDeclInstrs Name FC [PArg] Type
                       | RClausesInstrs Name [([(Name, Term)], Term, Term)]
                       | RAddImplementation Name Name
                       | RDatatypeDeclInstrs Name [PArg]
                       -- | Datatype, constructors
                       | RDatatypeDefnInstrs Name Type [(Name, [PArg], Type)]


-- | For elaborator state
data EState = EState {
    case_decls        :: [(Name, PDecl)]
  , delayed_elab      :: [(Int, Elab' EState ())]
  , new_tyDecls       :: [RDeclInstructions]
  , highlighting      :: [(FC, OutputAnnotation)]
  , auto_binds        :: [Name]        -- ^  names bound as auto implicits
  , implicit_warnings :: [(FC, Name)] -- ^ Implicit warnings to report (location and global name)
  }

initEState :: EState
initEState = EState [] [] [] [] [] []

type ElabD a = Elab' EState a

highlightSource :: FC -> OutputAnnotation -> ElabD ()
highlightSource fc annot =
  updateAux (\aux -> aux { highlighting = (fc, annot) : highlighting aux })

-- | One clause of a top-level definition. Term arguments to constructors are:
--
-- 1. The whole application (missing for PClauseR and PWithR because they're within a "with" clause)
--
-- 2. The list of extra 'with' patterns
--
-- 3. The right-hand side
--
-- 4. The where block (PDecl' t)

data PClause' t = PClause  FC Name t [t] t                    [PDecl' t] -- ^ A normal top-level definition.
                | PWith    FC Name t [t] t (Maybe (Name, FC)) [PDecl' t]
                | PClauseR FC        [t] t                    [PDecl' t]
                | PWithR   FC        [t] t (Maybe (Name, FC)) [PDecl' t]
    deriving (Functor, Generic)
{-!
deriving instance Binary PClause'
!-}

-- | Data declaration
data PData' t  =
    -- | Data declaration
    PDatadecl { d_name    :: Name -- ^ The name of the datatype
              , d_name_fc :: FC   -- ^ The precise location of the type constructor name
              , d_tcon    :: t    -- ^ Type constructor
              , d_cons    :: [(Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, FC, t, FC, [Name])] -- ^ Constructors
              }
  -- | "Placeholder" for data whose constructors are defined later
  | PLaterdecl { d_name    :: Name
               , d_name_fc :: FC
               , d_tcon    :: t
  } deriving (Functor, Generic)

-- | Transform the FCs in a PData and its associated terms. The first
-- function transforms the general-purpose FCs, and the second
-- transforms those that are used for semantic source highlighting, so
-- they can be treated specially.
mapPDataFC :: (FC -> FC) -> (FC -> FC) -> PData -> PData
mapPDataFC f g (PDatadecl n nfc tycon ctors) =
  PDatadecl n (g nfc) (mapPTermFC f g tycon) (map ctorFC ctors)
    where ctorFC (doc, argDocs, n, nfc, ty, fc, ns) =
                 (doc, argDocs, n, g nfc, mapPTermFC f g ty, f fc, ns)
mapPDataFC f g (PLaterdecl n nfc tycon) =
  PLaterdecl n (g nfc) (mapPTermFC f g tycon)
{-!
deriving instance Binary PData'
!-}

-- Handy to get a free function for applying PTerm -> PTerm functions
-- across a program, by deriving Functor

type PDecl   = PDecl' PTerm
type PData   = PData' PTerm
type PClause = PClause' PTerm

-- | Transform the FCs in a PTerm. The first function transforms the
-- general-purpose FCs, and the second transforms those that are used
-- for semantic source highlighting, so they can be treated specially.
mapPDeclFC :: (FC -> FC) -> (FC -> FC) -> PDecl -> PDecl
mapPDeclFC f g (PFix fc fixity ops) =
    PFix (f fc) fixity ops
mapPDeclFC f g (PTy doc argdocs syn fc opts n nfc ty) =
    PTy doc argdocs syn (f fc) opts n (g nfc) (mapPTermFC f g ty)
mapPDeclFC f g (PPostulate ext doc syn fc nfc opts n ty) =
    PPostulate ext doc syn (f fc) (g nfc) opts n (mapPTermFC f g ty)

mapPDeclFC f g (PClauses fc opts n clauses) =
    PClauses (f fc) opts n (map (fmap (mapPTermFC f g)) clauses)
mapPDeclFC f g (PCAF fc n tm) = PCAF (f fc) n (mapPTermFC f g tm)
mapPDeclFC f g (PData doc argdocs syn fc opts dat) =
    PData doc argdocs syn (f fc) opts (mapPDataFC f g dat)
mapPDeclFC f g (PParams fc params decls) =
    PParams (f fc)
            (map (\(n, ty) -> (n, mapPTermFC f g ty)) params)
            (map (mapPDeclFC f g) decls)
mapPDeclFC f g (POpenInterfaces fc ifs decls) =
    POpenInterfaces (f fc) ifs (map (mapPDeclFC f g) decls)
mapPDeclFC f g (PNamespace ns fc decls) =
    PNamespace ns (f fc) (map (mapPDeclFC f g) decls)
mapPDeclFC f g (PRecord doc syn fc opts n nfc params paramdocs fields ctor ctorDoc syn') =
    PRecord doc syn (f fc) opts n (g nfc)
            (map (\(pn, pnfc, plic, ty) -> (pn, g pnfc, plic, mapPTermFC f g ty)) params)
            paramdocs
            (map (\(fn, plic, ty, fdoc) -> (fmap (\(fn', fnfc) -> (fn', g fnfc)) fn,
                                            plic, mapPTermFC f g ty, fdoc))
                 fields)
            (fmap (\(ctorN, ctorNFC) -> (ctorN, g ctorNFC)) ctor)
            ctorDoc
            syn'
mapPDeclFC f g (PInterface doc syn fc constrs n nfc params paramDocs det body ctor ctorDoc) =
    PInterface doc syn (f fc)
           (map (\(constrn, constr) -> (constrn, mapPTermFC f g constr)) constrs)
           n (g nfc) (map (\(n, nfc, pty) -> (n, g nfc, mapPTermFC f g pty)) params)
           paramDocs (map (\(dn, dnfc) -> (dn, g dnfc)) det)
           (map (mapPDeclFC f g) body)
           (fmap (\(n, nfc) -> (n, g nfc)) ctor)
           ctorDoc
mapPDeclFC f g (PImplementation doc paramDocs syn fc constrs pnames cn acc opts cnfc params pextra implTy implN body) =
    PImplementation doc paramDocs syn (f fc)
                    (map (\(constrN, constrT) -> (constrN, mapPTermFC f g constrT)) constrs)
                    pnames cn acc opts (g cnfc) (map (mapPTermFC f g) params)
                    (map (\(en, et) -> (en, mapPTermFC f g et)) pextra)
                    (mapPTermFC f g implTy)
                    implN
                    (map (mapPDeclFC f g) body)
mapPDeclFC f g (PDSL n dsl) = PDSL n (fmap (mapPTermFC f g) dsl)
mapPDeclFC f g (PSyntax fc syn) = PSyntax (f fc) $
                                    case syn of
                                      Rule syms tm ctxt -> Rule syms (mapPTermFC f g tm) ctxt
                                      DeclRule syms decls -> DeclRule syms (map (mapPDeclFC f g) decls)
mapPDeclFC f g (PMutual fc decls) =
    PMutual (f fc) (map (mapPDeclFC f g) decls)
mapPDeclFC f g (PDirective d) =
    PDirective $
      case d of
        DNameHint n nfc ns ->
            DNameHint n (g nfc) (map (\(hn, hnfc) -> (hn, g hnfc)) ns)
        DErrorHandlers n nfc n' nfc' ns ->
            DErrorHandlers n (g nfc) n' (g nfc') $
                map (\(an, anfc) -> (an, g anfc)) ns
mapPDeclFC f g (PProvider doc syn fc nfc what n) =
    PProvider doc syn (f fc) (g nfc) (fmap (mapPTermFC f g) what) n
mapPDeclFC f g (PTransform fc safe l r) =
    PTransform (f fc) safe (mapPTermFC f g l) (mapPTermFC f g r)
mapPDeclFC f g (PRunElabDecl fc script ns) =
    PRunElabDecl (f fc) (mapPTermFC f g script) ns

-- | Get all the names declared in a declaration
declared :: PDecl -> [Name]
declared (PFix _ _ _) = []
declared (PTy _ _ _ _ _ n fc t) = [n]
declared (PPostulate _ _ _ _ _ _ n t) = [n]
declared (PClauses _ _ n _) = [] -- not a declaration
declared (PCAF _ n _) = [n]
declared (PData _ _ _ _ _ (PDatadecl n _ _ ts)) = n : map fstt ts
   where fstt (_, _, a, _, _, _, _) = a
declared (PData _ _ _ _ _ (PLaterdecl n _ _)) = [n]
declared (PParams _ _ ds) = concatMap declared ds
declared (POpenInterfaces _ _ ds) = concatMap declared ds
declared (PNamespace _ _ ds) = concatMap declared ds
declared (PRecord _ _ _ _ n  _ _ _ _ cn _ _) = n : map fst (maybeToList cn)
declared (PInterface _ _ _ _ n _ _ _ _ ms cn cd) = n : (map fst (maybeToList cn) ++ concatMap declared ms)
declared (PImplementation _ _ _ _ _ _ _ _ _ _ _ _ _ mn _)
    = case mn of
           Nothing -> []
           Just n -> [n]
declared (PDSL n _) = [n]
declared (PSyntax _ _) = []
declared (PMutual _ ds) = concatMap declared ds
declared (PDirective _) = []
declared _ = []

-- get the names declared, not counting nested parameter blocks
tldeclared :: PDecl -> [Name]
tldeclared (PFix _ _ _)                           = []
tldeclared (PTy _ _ _ _ _ n _ t)                  = [n]
tldeclared (PPostulate _ _ _ _ _ _ n t)           = [n]
tldeclared (PClauses _ _ n _)                     = [] -- not a declaration
tldeclared (PRecord _ _ _ _ n _ _ _ _ cn _ _)     = n : map fst (maybeToList cn)
tldeclared (PData _ _ _ _ _ (PDatadecl n _ _ ts)) = n : map fstt ts
   where fstt (_, _, a, _, _, _, _) = a
tldeclared (PParams _ _ ds)                       = []
tldeclared (POpenInterfaces _ _ ds)               = concatMap tldeclared ds
tldeclared (PMutual _ ds)                         = concatMap tldeclared ds
tldeclared (PNamespace _ _ ds)                    = concatMap tldeclared ds
tldeclared (PInterface _ _ _ _ n _ _ _ _ ms cn _)     = n : (map fst (maybeToList cn) ++ concatMap tldeclared ms)
tldeclared (PImplementation _ _ _ _ _ _ _ _ _ _ _ _ _ mn _)
    = case mn of
           Nothing -> []
           Just n -> [n]
tldeclared _                                      = []

defined :: PDecl -> [Name]
defined (PFix _ _ _)                              = []
defined (PTy _ _ _ _ _ n _ t)                     = []
defined (PPostulate _ _ _ _ _ _ n t)              = []
defined (PClauses _ _ n _)                        = [n] -- not a declaration
defined (PCAF _ n _)                              = [n]
defined (PData _ _ _ _ _ (PDatadecl n _ _ ts))    = n : map fstt ts
   where fstt (_, _, a, _, _, _, _) = a
defined (PData _ _ _ _ _ (PLaterdecl n _ _))      = []
defined (PParams _ _ ds)                          = concatMap defined ds
defined (POpenInterfaces _ _ ds)                  = concatMap defined ds
defined (PNamespace _ _ ds)                       = concatMap defined ds
defined (PRecord _ _ _ _ n _ _ _ _ cn _ _)        = n : map fst (maybeToList cn)
defined (PInterface _ _ _ _ n _ _ _ _ ms cn _)        = n : (map fst (maybeToList cn) ++ concatMap defined ms)
defined (PImplementation _ _ _ _ _ _ _ _ _ _ _ _ _ mn _)
    = case mn of
           Nothing -> []
           Just n -> [n]
defined (PDSL n _)                                = [n]
defined (PSyntax _ _)                             = []
defined (PMutual _ ds)                            = concatMap defined ds
defined (PDirective _)                            = []
defined _                                         = []

updateN :: [(Name, Name)] -> Name -> Name
updateN ns n | Just n' <- lookup n ns = n'
updateN _  n = n

updateNs :: [(Name, Name)] -> PTerm -> PTerm
updateNs [] t = t
updateNs ns t = mapPT updateRef t
  where updateRef (PRef fc fcs f) = PRef fc fcs (updateN ns f)
        updateRef t = t

-- updateDNs :: [(Name, Name)] -> PDecl -> PDecl
-- updateDNs [] t = t
-- updateDNs ns (PTy s f n t)    | Just n' <- lookup n ns = PTy s f n' t
-- updateDNs ns (PClauses f n c) | Just n' <- lookup n ns = PClauses f n' (map updateCNs c)
--   where updateCNs ns (PClause n l ts r ds)
--             = PClause (updateN ns n) (fmap (updateNs ns) l)
--                                      (map (fmap (updateNs ns)) ts)
--                                      (fmap (updateNs ns) r)
--                                      (map (updateDNs ns) ds)
-- updateDNs ns c = c

data PunInfo = IsType
             | IsTerm
             | TypeOrTerm
             deriving (Eq, Show, Ord, Data, Typeable, Generic)

-- | High level language terms
data PTerm = PQuote Raw         -- ^ Inclusion of a core term into the
                                -- high-level language
           | PRef FC [FC] Name
             -- ^ A reference to a variable. The FC is its precise
             -- source location for highlighting. The list of FCs is a
             -- collection of additional highlighting locations.
           | PInferRef FC [FC] Name              -- ^ A name to be defined later
           | PPatvar FC Name                     -- ^ A pattern variable
           | PLam FC Name FC PTerm PTerm         -- ^ A lambda abstraction. Second FC is name span.
           | PPi  Plicity Name FC PTerm PTerm    -- ^ (n : t1) -> t2, where the FC is for the precise location of the variable
           | PLet FC Name FC PTerm PTerm PTerm   -- ^ A let binding (second FC is precise name location)
           | PTyped PTerm PTerm                  -- ^ Term with explicit type
           | PApp FC PTerm [PArg]                -- ^ e.g. IO (), List Char, length x
           | PWithApp FC PTerm PTerm             -- ^ Application plus a 'with' argument
           | PAppImpl PTerm [ImplicitInfo]       -- ^ Implicit argument application (introduced during elaboration only)
           | PAppBind FC PTerm [PArg]            -- ^ implicitly bound application
           | PMatchApp FC Name                   -- ^ Make an application by type matching
           | PIfThenElse FC PTerm PTerm PTerm    -- ^ Conditional expressions - elaborated to an overloading of ifThenElse
           | PCase FC PTerm [(PTerm, PTerm)]     -- ^ A case expression. Args are source location, scrutinee, and a list of pattern/RHS pairs
           | PTrue FC PunInfo                    -- ^ Unit type..?
           | PResolveTC FC                       -- ^ Solve this dictionary by interface resolution
           | PRewrite FC (Maybe Name) PTerm PTerm (Maybe PTerm)
             -- ^ "rewrite" syntax, with optional rewriting function and
             -- optional result type
           | PPair FC [FC] PunInfo PTerm PTerm
             -- ^ A pair (a, b) and whether it's a product type or a
             -- pair (solved by elaboration). The list of FCs is its
             -- punctuation.
           | PDPair FC [FC] PunInfo PTerm PTerm PTerm
             -- ^ A dependent pair (tm : a ** b) and whether it's a
             -- sigma type or a pair that inhabits one (solved by
             -- elaboration). The [FC] is its punctuation.
           | PAs FC Name PTerm                            -- ^ @-pattern, valid LHS only
           | PAlternative [(Name, Name)] PAltType [PTerm] -- ^ (| A, B, C|). Includes unapplied unique name mappings for mkUniqueNames.
           | PHidden PTerm                                -- ^ Irrelevant or hidden pattern
           | PType FC                                     -- ^ 'Type' type
           | PUniverse FC Universe                        -- ^ Some universe
           | PGoal FC PTerm Name PTerm                    -- ^ quoteGoal, used for %reflection functions
           | PConstant FC Const                           -- ^ Builtin types
           | Placeholder                                  -- ^ Underscore
           | PDoBlock [PDo]                               -- ^ Do notation
           | PIdiom FC PTerm                              -- ^ Idiom brackets
           | PMetavar FC Name                             -- ^ A metavariable, ?name, and its precise location
           | PProof [PTactic]                             -- ^ Proof script
           | PTactics [PTactic]                           -- ^ As PProof, but no auto solving
           | PElabError Err                               -- ^ Error to report on elaboration
           | PImpossible                                  -- ^ Special case for declaring when an LHS can't typecheck
           | PCoerced PTerm                               -- ^ To mark a coerced argument, so as not to coerce twice
           | PDisamb [[T.Text]] PTerm                     -- ^ Preferences for explicit namespaces
           | PUnifyLog PTerm                              -- ^ dump a trace of unifications when building term
           | PNoImplicits PTerm                           -- ^ never run implicit converions on the term
           | PQuasiquote PTerm (Maybe PTerm)              -- ^ `(Term [: Term])
           | PUnquote PTerm                               -- ^ ~Term
           | PQuoteName Name Bool FC
             -- ^ `{n} where the FC is the precise highlighting for
             -- the name in particular. If the Bool is False, then
             -- it's `{{n}} and the name won't be resolved.
           | PRunElab FC PTerm [String]
             -- ^ %runElab tm - New-style proof script. Args are
             -- location, script, enclosing namespace.
           | PConstSugar FC PTerm
             -- ^ A desugared constant. The FC is a precise source
             -- location that will be used to highlight it later.
       deriving (Eq, Ord, Data, Typeable, Generic)

data PAltType = ExactlyOne Bool -- ^ flag sets whether delay is allowed
              | FirstSuccess
              | TryImplicit
       deriving (Eq, Ord, Data, Generic, Typeable)

-- | Transform the FCs in a PTerm. The first function transforms the
-- general-purpose FCs, and the second transforms those that are used
-- for semantic source highlighting, so they can be treated specially.
mapPTermFC :: (FC -> FC) -> (FC -> FC) -> PTerm -> PTerm
mapPTermFC f g (PQuote q)                     = PQuote q
mapPTermFC f g (PRef fc fcs n)                = PRef (g fc) (map g fcs) n
mapPTermFC f g (PInferRef fc fcs n)           = PInferRef (g fc) (map g fcs) n
mapPTermFC f g (PPatvar fc n)                 = PPatvar (g fc) n
mapPTermFC f g (PLam fc n fc' t1 t2)          = PLam (f fc) n (g fc') (mapPTermFC f g t1) (mapPTermFC f g t2)
mapPTermFC f g (PPi plic n fc t1 t2)          = PPi plic n (g fc) (mapPTermFC f g t1) (mapPTermFC f g t2)
mapPTermFC f g (PLet fc n fc' t1 t2 t3)       = PLet (f fc) n (g fc') (mapPTermFC f g t1) (mapPTermFC f g t2) (mapPTermFC f g t3)
mapPTermFC f g (PTyped t1 t2)                 = PTyped (mapPTermFC f g t1) (mapPTermFC f g t2)
mapPTermFC f g (PApp fc t args)               = PApp (f fc) (mapPTermFC f g t) (map (fmap (mapPTermFC f g)) args)
mapPTermFC f g (PWithApp fc t arg)            = PWithApp (f fc) (mapPTermFC f g t) (mapPTermFC f g arg)
mapPTermFC f g (PAppImpl t1 impls)            = PAppImpl (mapPTermFC f g t1) impls
mapPTermFC f g (PAppBind fc t args)           = PAppBind (f fc) (mapPTermFC f g t) (map (fmap (mapPTermFC f g)) args)
mapPTermFC f g (PMatchApp fc n)               = PMatchApp (f fc) n
mapPTermFC f g (PIfThenElse fc t1 t2 t3)      = PIfThenElse (f fc) (mapPTermFC f g t1) (mapPTermFC f g t2) (mapPTermFC f g t3)
mapPTermFC f g (PCase fc t cases)             = PCase (f fc) (mapPTermFC f g t) (map (\(l,r) -> (mapPTermFC f g l, mapPTermFC f g r)) cases)
mapPTermFC f g (PTrue fc info)                = PTrue (f fc) info
mapPTermFC f g (PResolveTC fc)                = PResolveTC (f fc)
mapPTermFC f g (PRewrite fc by t1 t2 t3)      = PRewrite (f fc) by (mapPTermFC f g t1) (mapPTermFC f g t2) (fmap (mapPTermFC f g) t3)
mapPTermFC f g (PPair fc hls info t1 t2)      = PPair (f fc) (map g hls) info (mapPTermFC f g t1) (mapPTermFC f g t2)
mapPTermFC f g (PDPair fc hls info t1 t2 t3)  = PDPair (f fc) (map g hls) info (mapPTermFC f g t1) (mapPTermFC f g t2) (mapPTermFC f g t3)
mapPTermFC f g (PAs fc n t)                   = PAs (f fc) n (mapPTermFC f g t)
mapPTermFC f g (PAlternative ns ty ts)        = PAlternative ns ty (map (mapPTermFC f g) ts)
mapPTermFC f g (PHidden t)                    = PHidden (mapPTermFC f g t)
mapPTermFC f g (PType fc)                     = PType (f fc)
mapPTermFC f g (PUniverse fc u)               = PUniverse (f fc) u
mapPTermFC f g (PGoal fc t1 n t2)             = PGoal (f fc) (mapPTermFC f g t1) n (mapPTermFC f g t2)
mapPTermFC f g (PConstant fc c)               = PConstant (f fc) c
mapPTermFC f g Placeholder                    = Placeholder
mapPTermFC f g (PDoBlock dos) = PDoBlock (map mapPDoFC dos)
  where mapPDoFC (DoExp  fc t) = DoExp (f fc) (mapPTermFC f g t)
        mapPDoFC (DoBind fc n nfc t) = DoBind (f fc) n (g nfc) (mapPTermFC f g t)
        mapPDoFC (DoBindP fc t1 t2 alts) =
          DoBindP (f fc) (mapPTermFC f g t1) (mapPTermFC f g t2) (map (\(l,r)-> (mapPTermFC f g l, mapPTermFC f g r)) alts)
        mapPDoFC (DoLet fc n nfc t1 t2) = DoLet (f fc) n (g nfc) (mapPTermFC f g t1) (mapPTermFC f g t2)
        mapPDoFC (DoLetP fc t1 t2) = DoLetP (f fc) (mapPTermFC f g t1) (mapPTermFC f g t2)
mapPTermFC f g (PIdiom fc t)                  = PIdiom (f fc) (mapPTermFC f g t)
mapPTermFC f g (PMetavar fc n)                = PMetavar (g fc) n
mapPTermFC f g (PProof tacs)                  = PProof (map (fmap (mapPTermFC f g)) tacs)
mapPTermFC f g (PTactics tacs)                = PTactics (map (fmap (mapPTermFC f g)) tacs)
mapPTermFC f g (PElabError err)               = PElabError err
mapPTermFC f g PImpossible                    = PImpossible
mapPTermFC f g (PCoerced t)                   = PCoerced (mapPTermFC f g t)
mapPTermFC f g (PDisamb msg t)                = PDisamb msg (mapPTermFC f g t)
mapPTermFC f g (PUnifyLog t)                  = PUnifyLog (mapPTermFC f g t)
mapPTermFC f g (PNoImplicits t)               = PNoImplicits (mapPTermFC f g t)
mapPTermFC f g (PQuasiquote t1 t2)            = PQuasiquote (mapPTermFC f g t1) (fmap (mapPTermFC f g) t2)
mapPTermFC f g (PUnquote t)                   = PUnquote (mapPTermFC f g t)
mapPTermFC f g (PRunElab fc tm ns)            = PRunElab (f fc) (mapPTermFC f g tm) ns
mapPTermFC f g (PConstSugar fc tm)            = PConstSugar (g fc) (mapPTermFC f g tm)
mapPTermFC f g (PQuoteName n x fc)            = PQuoteName n x (g fc)

{-!
dg instance Binary PTerm
!-}

mapPT :: (PTerm -> PTerm) -> PTerm -> PTerm
mapPT f t = f (mpt t) where
  mpt (PLam fc n nfc t s)     = PLam fc n nfc (mapPT f t) (mapPT f s)
  mpt (PPi p n nfc t s)       = PPi p n nfc (mapPT f t) (mapPT f s)
  mpt (PLet fc n nfc ty v s)  = PLet fc n nfc (mapPT f ty) (mapPT f v) (mapPT f s)
  mpt (PRewrite fc by t s g)  = PRewrite fc by (mapPT f t) (mapPT f s) (fmap (mapPT f) g)
  mpt (PApp fc t as)          = PApp fc (mapPT f t) (map (fmap (mapPT f)) as)
  mpt (PWithApp fc t a)       = PWithApp fc (mapPT f t) (mapPT f a)
  mpt (PAppBind fc t as)      = PAppBind fc (mapPT f t) (map (fmap (mapPT f)) as)
  mpt (PCase fc c os)         = PCase fc (mapPT f c) (map (pmap (mapPT f)) os)
  mpt (PIfThenElse fc c t e)  = PIfThenElse fc (mapPT f c) (mapPT f t) (mapPT f e)
  mpt (PTyped l r)            = PTyped (mapPT f l) (mapPT f r)
  mpt (PPair fc hls p l r)    = PPair fc hls p (mapPT f l) (mapPT f r)
  mpt (PDPair fc hls p l t r) = PDPair fc hls p (mapPT f l) (mapPT f t) (mapPT f r)
  mpt (PAlternative ns a as)  = PAlternative ns a (map (mapPT f) as)
  mpt (PHidden t)             = PHidden (mapPT f t)
  mpt (PDoBlock ds)           = PDoBlock (map (fmap (mapPT f)) ds)
  mpt (PProof ts)             = PProof (map (fmap (mapPT f)) ts)
  mpt (PTactics ts)           = PTactics (map (fmap (mapPT f)) ts)
  mpt (PUnifyLog tm)          = PUnifyLog (mapPT f tm)
  mpt (PDisamb ns tm)         = PDisamb ns (mapPT f tm)
  mpt (PNoImplicits tm)       = PNoImplicits (mapPT f tm)
  mpt (PGoal fc r n sc)       = PGoal fc (mapPT f r) n (mapPT f sc)
  mpt x                       = x


data PTactic' t = Intro [Name] | Intros | Focus Name
                | Refine Name [Bool] | Rewrite t | DoUnify
                | Induction t
                | CaseTac t
                | Equiv t
                | Claim Name t
                | Unfocus
                | MatchRefine Name
                | LetTac Name t | LetTacTy Name t t
                | Exact t | Compute | Trivial | TCImplementation
                | ProofSearch Bool Bool Int (Maybe Name)
                              [Name] -- allowed local names
                              [Name] -- hints
                  -- ^ the bool is whether to search recursively
                | Solve
                | Attack
                | ProofState | ProofTerm | Undo
                | Try (PTactic' t) (PTactic' t)
                | TSeq (PTactic' t) (PTactic' t)
                | ApplyTactic t -- see Language.Reflection module
                | ByReflection t
                | Reflect t
                | Fill t
                | GoalType String (PTactic' t)
                | TCheck t
                | TEval t
                | TDocStr (Either Name Const)
                | TSearch t
                | Skip
                | TFail [ErrorReportPart]
                | Qed | Abandon
                | SourceFC
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Data, Generic, Typeable)
{-!
deriving instance Binary PTactic'
!-}
instance Sized a => Sized (PTactic' a) where
  size (Intro nms)      = 1 + size nms
  size Intros           = 1
  size (Focus nm)       = 1 + size nm
  size (Refine nm bs)   = 1 + size nm + length bs
  size (Rewrite t)      = 1 + size t
  size (Induction t)    = 1 + size t
  size (LetTac nm t)    = 1 + size nm + size t
  size (Exact t)        = 1 + size t
  size Compute          = 1
  size Trivial          = 1
  size Solve            = 1
  size Attack           = 1
  size ProofState       = 1
  size ProofTerm        = 1
  size Undo             = 1
  size (Try l r)        = 1 + size l + size r
  size (TSeq l r)       = 1 + size l + size r
  size (ApplyTactic t)  = 1 + size t
  size (Reflect t)      = 1 + size t
  size (Fill t)         = 1 + size t
  size Qed              = 1
  size Abandon          = 1
  size Skip             = 1
  size (TFail ts)       = 1 + size ts
  size SourceFC         = 1
  size DoUnify          = 1
  size (CaseTac x)      = 1 + size x
  size (Equiv t)        = 1 + size t
  size (Claim x y)      = 1 + size x + size y
  size Unfocus          = 1
  size (MatchRefine x)  = 1 + size x
  size (LetTacTy x y z) = 1 + size x + size y + size z
  size TCImplementation       = 1

type PTactic = PTactic' PTerm

data PDo' t = DoExp  FC t
            | DoBind FC Name FC t     -- ^ second FC is precise name location
            | DoBindP FC t t [(t,t)]
            | DoLet  FC Name FC t t   -- ^ second FC is precise name location
            | DoLetP FC t t
    deriving (Eq, Ord, Functor, Data, Generic, Typeable)
{-!
deriving instance Binary PDo'
!-}

instance Sized a => Sized (PDo' a) where
  size (DoExp fc t)           = 1 + size fc + size t
  size (DoBind fc nm nfc t)   = 1 + size fc + size nm + size nfc + size t
  size (DoBindP fc l r alts)  = 1 + size fc + size l  + size r   + size alts
  size (DoLet fc nm nfc l r)  = 1 + size fc + size nm + size l   + size r
  size (DoLetP fc l r)        = 1 + size fc + size l  + size r

type PDo = PDo' PTerm

-- The priority gives a hint as to elaboration order. Best to elaborate
-- things early which will help give a more concrete type to other
-- variables, e.g. a before (interpTy a).

data PArg' t = PImp { priority    :: Int
                    , machine_inf :: Bool -- ^ true if the machine inferred it
                    , argopts     :: [ArgOpt]
                    , pname       :: Name
                    , getTm       :: t
                    }
             | PExp { priority :: Int
                    , argopts  :: [ArgOpt]
                    , pname    :: Name
                    , getTm    :: t
                    }
             | PConstraint { priority :: Int
                           , argopts  :: [ArgOpt]
                           , pname    :: Name
                           , getTm    :: t
                           }
             | PTacImplicit { priority  :: Int
                            , argopts   :: [ArgOpt]
                            , pname     :: Name
                            , getScript :: t
                            , getTm     :: t
                            }
             deriving (Show, Eq, Ord, Functor, Data, Generic, Typeable)

data ArgOpt = AlwaysShow
            | HideDisplay
            | InaccessibleArg
            | UnknownImp
            deriving (Show, Eq, Ord, Data, Generic, Typeable)

instance Sized a => Sized (PArg' a) where
  size (PImp p _ l nm trm)            = 1 + size nm + size trm
  size (PExp p l nm trm)              = 1 + size nm + size trm
  size (PConstraint p l nm trm)       = 1 + size nm + size nm  +  size trm
  size (PTacImplicit p l nm scr trm)  = 1 + size nm + size scr + size trm

{-!
deriving instance Binary PArg'
!-}

pimp n t mach = PImp 1 mach [] n t
pexp t        = PExp 1 [] (sMN 0 "arg") t
pconst t      = PConstraint 1 [] (sMN 0 "carg") t
ptacimp n s t = PTacImplicit 2 [] n s t

type PArg = PArg' PTerm

-- | Get the highest FC in a term, if one exists
highestFC :: PTerm -> Maybe FC
highestFC (PQuote _)              = Nothing
highestFC (PRef fc _ _)           = Just fc
highestFC (PInferRef fc _ _)      = Just fc
highestFC (PPatvar fc _)          = Just fc
highestFC (PLam fc _ _ _ _)       = Just fc
highestFC (PPi _ _ _ _ _)         = Nothing
highestFC (PLet fc _ _ _ _ _)     = Just fc
highestFC (PTyped tm ty)          = highestFC tm <|> highestFC ty
highestFC (PApp fc _ _)           = Just fc
highestFC (PAppBind fc _ _)       = Just fc
highestFC (PMatchApp fc _)        = Just fc
highestFC (PCase fc _ _)          = Just fc
highestFC (PIfThenElse fc _ _ _)  = Just fc
highestFC (PTrue fc _)            = Just fc
highestFC (PResolveTC fc)         = Just fc
highestFC (PRewrite fc _ _ _ _)   = Just fc
highestFC (PPair fc _ _ _ _)      = Just fc
highestFC (PDPair fc _ _ _ _ _)   = Just fc
highestFC (PAs fc _ _)            = Just fc
highestFC (PAlternative _ _ args) =
  case mapMaybe highestFC args of
    [] -> Nothing
    (fc:_) -> Just fc
highestFC (PHidden _)             = Nothing
highestFC (PType fc)              = Just fc
highestFC (PUniverse _ _)         = Nothing
highestFC (PGoal fc _ _ _)        = Just fc
highestFC (PConstant fc _)        = Just fc
highestFC Placeholder             = Nothing
highestFC (PDoBlock lines) =
  case map getDoFC lines of
    [] -> Nothing
    (fc:_) -> Just fc
  where
    getDoFC (DoExp fc t)          = fc
    getDoFC (DoBind fc nm nfc t)  = fc
    getDoFC (DoBindP fc l r alts) = fc
    getDoFC (DoLet fc nm nfc l r) = fc
    getDoFC (DoLetP fc l r)       = fc

highestFC (PIdiom fc _)           = Just fc
highestFC (PMetavar fc _)         = Just fc
highestFC (PProof _)              = Nothing
highestFC (PTactics _)            = Nothing
highestFC (PElabError _)          = Nothing
highestFC PImpossible             = Nothing
highestFC (PCoerced tm)           = highestFC tm
highestFC (PDisamb _ opts)        = highestFC opts
highestFC (PUnifyLog tm)          = highestFC tm
highestFC (PNoImplicits tm)       = highestFC tm
highestFC (PQuasiquote _ _)       = Nothing
highestFC (PUnquote tm)           = highestFC tm
highestFC (PQuoteName _ _ fc)     = Just fc
highestFC (PRunElab fc _ _)       = Just fc
highestFC (PConstSugar fc _)      = Just fc
highestFC (PAppImpl t _)          = highestFC t

-- Interface data

data InterfaceInfo = CI {
    implementationCtorName             :: Name
  , interface_methods                  :: [(Name, (Bool, FnOpts, PTerm))] -- ^ flag whether it's a "data" method
  , interface_defaults                 :: [(Name, (Name, PDecl))]         -- ^ method name -> default impl
  , interface_default_super_interfaces :: [PDecl]
  , interface_impparams                :: [Name]
  , interface_params                   :: [Name]
  , interface_constraints              :: [PTerm]
  , interface_implementations          :: [(Name, Bool)] -- ^ the Bool is whether to include in implementation search, so named implementations are excluded
  , interface_determiners              :: [Int]
  } deriving (Show, Generic)
{-!
deriving instance Binary InterfaceInfo
!-}

-- Record data
data RecordInfo = RI {
    record_parameters  :: [(Name,PTerm)]
  , record_constructor :: Name
  , record_projections :: [Name]
  } deriving (Show, Generic)

-- Type inference data

data TIData = TIPartial         -- ^ a function with a partially defined type
            | TISolution [Term] -- ^ possible solutions to a metavariable in a type
    deriving (Show, Generic)

-- | Miscellaneous information about functions
data FnInfo = FnInfo { fn_params :: [Int] }
    deriving (Show, Generic)
{-!
deriving instance Binary FnInfo
!-}

data OptInfo = Optimise {
    inaccessible :: [(Int,Name)]  -- includes names for error reporting
  , detaggable :: Bool
  , forceable :: [Int] -- argument positions which are forced by other values
  } deriving (Show, Generic)
{-!
deriving instance Binary OptInfo
!-}

-- | Syntactic sugar info
data DSL' t = DSL {
    dsl_bind    :: t
  , dsl_apply   :: t
  , dsl_pure    :: t
  , dsl_var     :: Maybe t
  , index_first :: Maybe t
  , index_next  :: Maybe t
  , dsl_lambda  :: Maybe t
  , dsl_let     :: Maybe t
  , dsl_pi      :: Maybe t
  } deriving (Show, Functor, Generic)
{-!
deriving instance Binary DSL'
!-}

type DSL = DSL' PTerm

data SynContext = PatternSyntax
                | TermSyntax
                | AnySyntax
    deriving (Show, Generic)
{-!
deriving instance Binary SynContext
!-}

data Syntax = Rule [SSymbol] PTerm SynContext
            | DeclRule [SSymbol] [PDecl]
    deriving (Show, Generic)

syntaxNames :: Syntax -> [Name]
syntaxNames (Rule syms _ _) = mapMaybe ename syms
           where ename (Keyword n)  = Just n
                 ename _            = Nothing
syntaxNames (DeclRule syms _) = mapMaybe ename syms
           where ename (Keyword n)  = Just n
                 ename _            = Nothing

syntaxSymbols :: Syntax -> [SSymbol]
syntaxSymbols (Rule ss _ _) = ss
syntaxSymbols (DeclRule ss _) = ss
{-!
deriving instance Binary Syntax
!-}

data SSymbol = Keyword Name
             | Symbol String
             | Binding Name
             | Expr Name
             | SimpleExpr Name
    deriving (Show, Eq, Generic)


{-!
deriving instance Binary SSymbol
!-}

newtype SyntaxRules = SyntaxRules { syntaxRulesList :: [Syntax] }
  deriving Generic

emptySyntaxRules :: SyntaxRules
emptySyntaxRules = SyntaxRules []

updateSyntaxRules :: [Syntax] -> SyntaxRules -> SyntaxRules
updateSyntaxRules rules (SyntaxRules sr) = SyntaxRules newRules
  where
    newRules = sortBy (ruleSort `on` syntaxSymbols) (rules ++ sr)

    ruleSort [] []  = EQ
    ruleSort [] _   = LT
    ruleSort _ []   = GT
    ruleSort (s1:ss1) (s2:ss2) =
      case symCompare s1 s2 of
        EQ -> ruleSort ss1 ss2
        r -> r

    -- Better than creating Ord implementation for SSymbol since
    -- in general this ordering does not really make sense.
    symCompare (Keyword n1) (Keyword n2)        = compare n1 n2
    symCompare (Keyword _) _                    = LT
    symCompare (Symbol _) (Keyword _)           = GT
    symCompare (Symbol s1) (Symbol s2)          = compare s1 s2
    symCompare (Symbol _) _                     = LT
    symCompare (Binding _) (Keyword _)          = GT
    symCompare (Binding _) (Symbol _)           = GT
    symCompare (Binding b1) (Binding b2)        = compare b1 b2
    symCompare (Binding _) _                    = LT
    symCompare (Expr _) (Keyword _)             = GT
    symCompare (Expr _) (Symbol _)              = GT
    symCompare (Expr _) (Binding _)             = GT
    symCompare (Expr e1) (Expr e2)              = compare e1 e2
    symCompare (Expr _) _                       = LT
    symCompare (SimpleExpr _) (Keyword _)       = GT
    symCompare (SimpleExpr _) (Symbol _)        = GT
    symCompare (SimpleExpr _) (Binding _)       = GT
    symCompare (SimpleExpr _) (Expr _)          = GT
    symCompare (SimpleExpr e1) (SimpleExpr e2)  = compare e1 e2

initDSL = DSL (PRef f [] (sUN ">>="))
              (PRef f [] (sUN "<*>"))
              (PRef f [] (sUN "pure"))
              Nothing
              Nothing
              Nothing
              Nothing
              Nothing
              Nothing
  where f = fileFC "(builtin)"

data Using = UImplicit Name PTerm
           | UConstraint Name [Name]
    deriving (Show, Eq, Data, Generic, Typeable)
{-!
deriving instance Binary Using
!-}

data SyntaxInfo = Syn {
    using             :: [Using]
  , syn_params        :: [(Name, PTerm)]
  , syn_namespace     :: [String]
  , no_imp            :: [Name]
  , imp_methods       :: [Name]
  -- ^ interface methods. When expanding implicits, these should be
  -- expanded even under binders
  , decoration        :: Name -> Name
  , inPattern         :: Bool
  , implicitAllowed   :: Bool
  , constraintAllowed :: Bool
  , maxline           :: Maybe Int
  , mut_nesting       :: Int
  , dsl_info          :: DSL
  , syn_in_quasiquote :: Int
  , syn_toplevel      :: Bool
  , withAppAllowed    :: Bool
  } deriving (Show, Generic)
{-!
deriving instance Binary SyntaxInfo
!-}

defaultSyntax = Syn [] [] [] [] [] id False False False Nothing 0 initDSL 0 True True

expandNS :: SyntaxInfo -> Name -> Name
expandNS syn n@(NS _ _) = n
expandNS syn n = case syn_namespace syn of
                        [] -> n
                        xs -> sNS n xs


-- For inferring types of things

bi = fileFC "builtin"
primfc = fileFC "(primitive)"

inferTy   = sMN 0 "__Infer"
inferCon  = sMN 0 "__infer"
inferDecl = PDatadecl inferTy primfc
                      (PType bi)
                      [(emptyDocstring, [], inferCon, primfc, PPi impl (sMN 0 "iType") primfc (PType bi) (
                                                   PPi expl (sMN 0 "ival") primfc (PRef bi [] (sMN 0 "iType"))
                                                   (PRef bi [] inferTy)), bi, [])]
inferOpts = []

infTerm t = PApp bi (PRef bi [] inferCon) [pimp (sMN 0 "iType") Placeholder True, pexp t]
infP = P (TCon 6 0) inferTy (TType (UVal 0))

getInferTerm, getInferType :: Term -> Term
getInferTerm (Bind n b sc) = Bind n b $ getInferTerm sc
getInferTerm (App _ (App _ _ _) tm) = tm
getInferTerm tm = tm -- error ("getInferTerm " ++ show tm)

getInferType (Bind n b sc)  = Bind n (toTy b) $ getInferType sc
  where toTy (Lam r t)      = Pi r Nothing t (TType (UVar [] 0))
        toTy (PVar _ t)     = PVTy t
        toTy b              = b
getInferType (App _ (App _ _ ty) _) = ty



-- Handy primitives: Unit, False, Pair, MkPair, =, mkForeign

primNames = [inferTy, inferCon]

unitTy   = sUN "Unit"
unitCon  = sUN "MkUnit"

falseDoc = fmap (const $ Msg "") . parseDocstring . T.pack $
             "The empty type, also known as the trivially false proposition." ++
             "\n\n" ++
             "Use `void` or `absurd` to prove anything if you have a variable " ++
             "of type `Void` in scope."
falseTy   = sUN "Void"

pairTy    = sNS (sUN "Pair") ["Builtins"]
pairCon   = sNS (sUN "MkPair") ["Builtins"]

upairTy    = sNS (sUN "UPair") ["Builtins"]
upairCon   = sNS (sUN "MkUPair") ["Builtins"]

eqTy  = sUN "="
eqCon = sUN "Refl"
eqDoc = fmap (const (Left $ Msg "")) . parseDocstring . T.pack $
          "The propositional equality type. A proof that `x` = `y`." ++
          "\n\n" ++
          "To use such a proof, pattern-match on it, and the two equal things will " ++
          "then need to be the _same_ pattern." ++
          "\n\n" ++
          "**Note**: Idris's equality type is potentially _heterogeneous_, which means that it " ++
          "is possible to state equalities between values of potentially different " ++
          "types. However, Idris will attempt the homogeneous case unless it fails to typecheck." ++
          "\n\n" ++
          "You may need to use `(~=~)` to explicitly request heterogeneous equality."

eqDecl = PDatadecl eqTy primfc (piBindp impl [(n "A", PType bi), (n "B", PType bi)]
                                      (piBind [(n "x", PRef bi [] (n "A")), (n "y", PRef bi [] (n "B"))]
                                      (PType bi)))
                [(reflDoc, reflParamDoc,
                  eqCon, primfc, PPi impl (n "A") primfc (PType bi) (
                                        PPi impl (n "x") primfc (PRef bi [] (n "A"))
                                            (PApp bi (PRef bi [] eqTy) [pimp (n "A") Placeholder False,
                                                                     pimp (n "B") Placeholder False,
                                                                     pexp (PRef bi [] (n "x")),
                                                                     pexp (PRef bi [] (n "x"))])), bi, [])]
    where n a = sUN a
          reflDoc = annotCode (const (Left $ Msg "")) . parseDocstring . T.pack $
                      "A proof that `x` in fact equals `x`. To construct this, you must have already " ++
                      "shown that both sides are in fact equal."
          reflParamDoc = [(n "A",  annotCode (const (Left $ Msg "")) . parseDocstring . T.pack $ "the type at which the equality is proven"),
                          (n "x",  annotCode (const (Left $ Msg "")) . parseDocstring . T.pack $ "the element shown to be equal to itself.")]

eqParamDoc = [(n "A", annotCode (const (Left $ Msg "")) . parseDocstring . T.pack $ "the type of the left side of the equality"),
              (n "B", annotCode (const (Left $ Msg "")) . parseDocstring . T.pack $ "the type of the right side of the equality")
              ]
    where n a = sUN a

eqOpts = []

-- | The special name to be used in the module documentation context -
-- not for use in the main definition context. The namespace around it
-- will determine the module to which the docs adhere.
modDocName :: Name
modDocName = sMN 0 "ModuleDocs"

-- Defined in builtins.idr
sigmaTy   = sNS (sUN "DPair") ["Builtins"]
sigmaCon = sNS (sUN "MkDPair") ["Builtins"]

piBind :: [(Name, PTerm)] -> PTerm -> PTerm
piBind = piBindp expl

piBindp :: Plicity -> [(Name, PTerm)] -> PTerm -> PTerm
piBindp p [] t = t
piBindp p ((n, ty):ns) t = PPi p n NoFC ty (piBindp p ns t)


-- Pretty-printing declarations and terms

-- These "show" implementations render to an absurdly wide screen because inserted line breaks
-- could interfere with interactive editing, which calls "show".

instance Show PTerm where
  showsPrec _ tm = (displayS . renderPretty 1.0 10000000 . prettyImp defaultPPOption) tm

instance Show PDecl where
  showsPrec _ d = (displayS . renderPretty 1.0 10000000 . showDeclImp verbosePPOption) d

instance Show PClause where
  showsPrec _ c = (displayS . renderPretty 1.0 10000000 . showCImp verbosePPOption) c

instance Show PData where
  showsPrec _ d = (displayS . renderPretty 1.0 10000000 . showDImp defaultPPOption) d

instance Pretty PTerm OutputAnnotation where
  pretty = prettyImp defaultPPOption

-- | Colourise annotations according to an Idris state. It ignores the
-- names in the annotation, as there's no good way to show extended
-- information on a terminal.
annotationColour :: IState -> OutputAnnotation -> Maybe IdrisColour
annotationColour ist _ | not (idris_colourRepl ist) = Nothing
annotationColour ist (AnnConst c) =
    let theme = idris_colourTheme ist
    in Just $ if constIsType c
                then typeColour theme
                else dataColour theme
annotationColour ist (AnnData _ _)          = Just $ dataColour (idris_colourTheme ist)
annotationColour ist (AnnType _ _)          = Just $ typeColour (idris_colourTheme ist)
annotationColour ist (AnnBoundName _ True)  = Just $ implicitColour (idris_colourTheme ist)
annotationColour ist (AnnBoundName _ False) = Just $ boundVarColour (idris_colourTheme ist)
annotationColour ist AnnKeyword             = Just $ keywordColour (idris_colourTheme ist)
annotationColour ist (AnnName n _ _ _) =
  let ctxt = tt_ctxt ist
      theme = idris_colourTheme ist
  in case () of
       _ | isDConName n ctxt     -> Just $ dataColour theme
       _ | isFnName n ctxt       -> Just $ functionColour theme
       _ | isTConName n ctxt     -> Just $ typeColour theme
       _ | isPostulateName n ist -> Just $ postulateColour theme
       _ | otherwise             -> Nothing -- don't colourise unknown names
annotationColour ist (AnnTextFmt fmt) = Just (colour fmt)
  where colour BoldText      = IdrisColour Nothing True False True False
        colour UnderlineText = IdrisColour Nothing True True False False
        colour ItalicText    = IdrisColour Nothing True False False True
annotationColour ist _ = Nothing


-- | Colourise annotations according to an Idris state. It ignores the
-- names in the annotation, as there's no good way to show extended
-- information on a terminal. Note that strings produced this way will
-- not be coloured on Windows, so the use of the colour rendering
-- functions in Idris.Output is to be preferred.
consoleDecorate :: IState -> OutputAnnotation -> String -> String
consoleDecorate ist ann = maybe id colourise (annotationColour ist ann)

isPostulateName :: Name -> IState -> Bool
isPostulateName n ist = S.member n (idris_postulates ist)

-- | Pretty-print a high-level closed Idris term with no information
-- about precedence/associativity
prettyImp :: PPOption -- ^ pretty printing options
          -> PTerm    -- ^ the term to pretty-print
          -> Doc OutputAnnotation
prettyImp impl = pprintPTerm impl [] [] []

-- | Serialise something to base64 using its Binary implementation.

-- | Do the right thing for rendering a term in an IState
prettyIst ::  IState -> PTerm -> Doc OutputAnnotation
prettyIst ist = pprintPTerm (ppOptionIst ist) [] [] (idris_infixes ist)

-- | Pretty-print a high-level Idris term in some bindings context
-- with infix info.
pprintPTerm :: PPOption       -- ^ pretty printing options
            -> [(Name, Bool)] -- ^ the currently-bound names and whether they are implicit
            -> [Name]         -- ^ names to always show in pi, even if not used
            -> [FixDecl]      -- ^ Fixity declarations
            -> PTerm          -- ^ the term to pretty-print
            -> Doc OutputAnnotation
pprintPTerm ppo bnd docArgs infixes = prettySe (ppopt_depth ppo) startPrec bnd
  where
    startPrec = 0
    funcAppPrec = 10

    prettySe :: Maybe Int -> Int -> [(Name, Bool)] -> PTerm -> Doc OutputAnnotation
    prettySe d p bnd (PQuote r) =
        text "![" <> pretty r <> text "]"
    prettySe d p bnd (PPatvar fc n) = pretty n
    prettySe d p bnd e
      | Just str <- slist d p bnd e = depth d str
      | Just n <- snat ppo d p e = depth d $ annotate (AnnData "Nat" "") (text (show n))
    prettySe d p bnd (PRef fc _ n) = prettyName True (ppopt_impl ppo) bnd n
    prettySe d p bnd (PLam fc n nfc ty sc) =
      let (ns, sc') = getLamNames [n] sc in
          depth d . bracket p startPrec . group . align . hang 2 $
          text "\\" <> prettyBindingsOf ns False <+> text "=>" <$>
          prettySe (decD d) startPrec ((n, False):bnd) sc'
      where
        getLamNames acc (PLam fc n nfc ty sc) = getLamNames (n : acc) sc
        getLamNames acc sc = (reverse acc, sc)

        prettyBindingsOf [] t = text ""
        prettyBindingsOf [n] t = prettyBindingOf n t
        prettyBindingsOf (n : ns) t = prettyBindingOf n t <> text "," <+>
                                      prettyBindingsOf ns t
    prettySe d p bnd (PLet fc n nfc ty v sc) =
      depth d . bracket p startPrec . group . align $
      kwd "let" <+> (group . align . hang 2 $ prettyBindingOf n False <+> text "=" <$> prettySe (decD d) startPrec bnd v) </>
      kwd "in" <+> (group . align . hang 2 $ prettySe (decD d) startPrec ((n, False):bnd) sc)
    prettySe d p bnd (PPi (Exp l s _ rig) n _ ty sc)
      | Rig0 <- rig =
          depth d . bracket p startPrec . group $
          enclose lparen rparen (group . align $ text "0" <+> prettyBindingOf n False <+> colon <+> prettySe (decD d) startPrec bnd ty) <+>
          st <> text "->" <$> prettySe (decD d) startPrec ((n, False):bnd) sc
      | Rig1 <- rig =
          depth d . bracket p startPrec . group $
          enclose lparen rparen (group . align $ text "1" <+> prettyBindingOf n False <+> colon <+> prettySe (decD d) startPrec bnd ty) <+>
          st <> text "->" <$> prettySe (decD d) startPrec ((n, False):bnd) sc
      | n `elem` allNamesIn sc || ppopt_impl ppo && uname n || n `elem` docArgs
          || ppopt_pinames ppo && uname n =
          depth d . bracket p startPrec . group $
          enclose lparen rparen (group . align $ prettyBindingOf n False <+> colon <+> prettySe (decD d) startPrec bnd ty) <+>
          st <> text "->" <$> prettySe (decD d) startPrec ((n, False):bnd) sc
      | otherwise                      =
          depth d . bracket p startPrec . group $
          group (prettySe (decD d) (startPrec + 1) bnd ty <+> st) <> text "->" <$>
          group (prettySe (decD d) startPrec ((n, False):bnd) sc)
      where
        uname (UN n) = case str n of
                            ('_':_) -> False
                            _ -> True
        uname _ = False

        st =
          case s of
            Static -> text "%static" <> space
            _      -> empty
    prettySe d p bnd (PPi (Imp l s _ fa _ rig) n _ ty sc)
      | ppopt_impl ppo =
          depth d . bracket p startPrec $
          lbrace <> showRig rig n <+> colon <+> prettySe (decD d) startPrec bnd ty <> rbrace <+>
          st <> text "->" </> prettySe (decD d) startPrec ((n, True):bnd) sc
      | isPi sc = depth d . bracket p startPrec $ prettySe (decD d) startPrec ((n, True):bnd) sc
      | otherwise = depth d $ prettySe (decD d) startPrec ((n, True):bnd) sc
      where
        showRig Rig0 n = text "0" <+> prettyBindingOf n True
        showRig Rig1 n = text "1" <+> prettyBindingOf n True
        showRig _ n = prettyBindingOf n True

        isPi (PPi (Exp{}) _ _ _ _) = True
        isPi (PPi _ _ _ _ sc) = isPi sc
        isPi _ = False

        st =
          case s of
            Static -> text "%static" <> space
            _      -> empty
    prettySe d p bnd (PPi (Constraint _ _ rig) n _ ty sc) =
      depth d . bracket p startPrec $
      prettySe (decD d) (startPrec + 1) bnd ty <+> text "=>" </> prettySe (decD d) startPrec ((n, True):bnd) sc
    prettySe d p bnd (PPi (TacImp _ _ (PTactics [ProofSearch{}]) rig) n _ ty sc) =
      lbrace <> kwd "auto" <+> pretty n <+> colon <+> prettySe (decD d) startPrec bnd ty <>
      rbrace <+> text "->" </> prettySe (decD d) startPrec ((n, True):bnd) sc
    prettySe d p bnd (PPi (TacImp _ _ s rig) n _ ty sc) =
      depth d . bracket p startPrec $
      lbrace <> kwd "default" <+> prettySe (decD d) (funcAppPrec + 1) bnd s <+> pretty n <+> colon <+> prettySe (decD d) startPrec bnd ty <>
      rbrace <+> text "->" </> prettySe (decD d) startPrec ((n, True):bnd) sc
    prettySe d p bnd (PApp _ (PRef _ _ neg) [_, _, val])
      | basename neg == sUN "negate" =
         lparen <> text "-" <> prettySe d funcAppPrec bnd (getTm val) <> rparen
    -- This case preserves the behavior of the former constructor PEq.
    -- It should be removed if feasible when the pretty-printing of infix
    -- operators in general is improved.
    prettySe d p bnd (PApp _ (PRef _ _ n) [lt, rt, l, r])
      | n == eqTy, ppopt_impl ppo =
          depth d . bracket p eqPrec $
            enclose lparen rparen eq <+>
            align (group (vsep (map (prettyArgS (decD d) bnd)
                                    [lt, rt, l, r])))
      | n == eqTy =
          depth d . bracket p eqPrec . align . group $
            prettyTerm (getTm l) <+> eq <$> group (prettyTerm (getTm r))
      where eq = annName eqTy (text "=")
            eqPrec = startPrec
            prettyTerm = prettySe (decD d) (eqPrec + 1) bnd
    prettySe d p bnd (PApp _ (PRef _ _ f) args) -- normal names, no explicit args
      | UN nm <- basename f
      , not (ppopt_impl ppo) && null (getShowArgs args) =
          prettyName True (ppopt_impl ppo) bnd f
    prettySe d p bnd (PAppBind _ (PRef _ _ f) [])
      | not (ppopt_impl ppo) = text "!" <> prettyName True (ppopt_impl ppo) bnd f
    prettySe d p bnd (PApp _ (PRef _ _ op) args) -- infix operators
      | UN nm <- basename op
      , not (tnull nm) &&
        (not (ppopt_impl ppo)) && (not $ isAlpha (thead nm)) =
          case getShowArgs args of
            [] -> opName True
            [x] -> group (opName True <$> group (prettySe (decD d) startPrec bnd (getTm x)))
            [l,r] -> let precedence = maybe (startPrec - 1) prec f
                     in depth d . bracket p precedence $ inFix (getTm l) (getTm r)
            (l@(PExp{}) : r@(PExp{}) : rest) ->
                   depth d . bracket p funcAppPrec $
                          enclose lparen rparen (inFix (getTm l) (getTm r)) <+>
                          align (group (vsep (map (prettyArgS d bnd) rest)))
            as -> opName True <+> align (vsep (map (prettyArgS d bnd) as))
          where opName isPrefix = prettyName isPrefix (ppopt_impl ppo) bnd op
                f = getFixity (opStr op)
                left = case f of
                           Nothing -> funcAppPrec + 1
                           Just (Infixl p') -> p'
                           Just f' -> prec f' + 1
                right = case f of
                            Nothing -> funcAppPrec + 1
                            Just (Infixr p') -> p'
                            Just f' -> prec f' + 1
                inFix l r = align . group $
                  (prettySe (decD d) left bnd l <+> opName False) <$>
                    group (prettySe (decD d) right bnd r)
    prettySe d p bnd (PApp _ hd@(PRef fc _ f) [tm]) -- symbols, like 'foo
      | PConstant NoFC (Idris.Core.TT.Str str) <- getTm tm,
        f == sUN "Symbol_" = annotate (AnnType ("'" ++ str) ("The symbol " ++ str)) $
                               char '\'' <> prettySe (decD d) startPrec bnd (PRef fc [] (sUN str))
    prettySe d p bnd (PApp _ f as) = -- Normal prefix applications
      let args = getShowArgs as
          fp   = prettySe (decD d) (startPrec + 1) bnd f
          shownArgs = if ppopt_impl ppo then as else args
      in
        depth d . bracket p funcAppPrec . group $
            if null shownArgs
              then fp
              else fp <+> align (vsep (map (prettyArgS d bnd) shownArgs))
    prettySe d p bnd (PWithApp _ f a) = prettySe d p bnd f <+> text "|" <+> prettySe d p bnd a
    prettySe d p bnd (PCase _ scr cases) =
      bracket p funcAppPrec $
          align $ kwd "case" <+> prettySe (decD d) startPrec bnd scr <+> kwd "of" <$>
          depth d (indent 2 (vsep (map ppcase cases)))
      where
        ppcase (l, r) = let prettyCase = prettySe (decD d) startPrec
                                         ([(n, False) | n <- vars l] ++ bnd)
                        in nest nestingSize $
                             prettyCase l <+> text "=>" <+> prettyCase r
        -- Warning: this is a bit of a hack. At this stage, we don't have the
        -- global context, so we can't determine which names are constructors,
        -- which are types, and which are pattern variables on the LHS of the
        -- case pattern. We use the heuristic that names without a namespace
        -- are patvars, because right now case blocks in PTerms are always
        -- delaborated from TT before being sent to the pretty-printer. If they
        -- start getting printed directly, THIS WILL BREAK.
        -- Potential solution: add a list of known patvars to the cases in
        -- PCase, and have the delaborator fill it out, kind of like the pun
        -- disambiguation on PDPair.
        vars tm = filter noNS (allNamesIn tm)
        noNS (NS _ _) = False
        noNS _        = True

    prettySe d p bnd (PIfThenElse _ c t f) =
      depth d . bracket p funcAppPrec . group . align . hang 2 . vsep $
        [ kwd "if"   <+> prettySe (decD d) startPrec bnd c
        , kwd "then" <+> prettySe (decD d) startPrec bnd t
        , kwd "else" <+> prettySe (decD d) startPrec bnd f
        ]
    prettySe d p bnd (PHidden tm)         = text "." <> prettySe (decD d) funcAppPrec bnd tm
    prettySe d p bnd (PResolveTC _)       = kwd "%implementation"
    prettySe d p bnd (PTrue _ IsType)     = annName unitTy $ text "()"
    prettySe d p bnd (PTrue _ IsTerm)     = annName unitCon $ text "()"
    prettySe d p bnd (PTrue _ TypeOrTerm) = text "()"
    prettySe d p bnd (PRewrite _ by l r _)   =
      depth d . bracket p startPrec $
      text "rewrite" <+> prettySe (decD d) (startPrec + 1) bnd l
      <+> (case by of
               Nothing -> empty
               Just fn -> text "using" <+>
                              prettyName True (ppopt_impl ppo) bnd fn) <+>
          text "in" <+> prettySe (decD d) startPrec bnd r
    prettySe d p bnd (PTyped l r) =
      lparen <> prettySe (decD d) startPrec bnd l <+> colon <+> prettySe (decD d) startPrec bnd r <> rparen
    prettySe d p bnd pair@(PPair _ _ pun _ _) -- flatten tuples to the right, like parser
      | Just elts <- pairElts pair = depth d . enclose (ann lparen) (ann rparen) .
                                     align . group . vsep . punctuate (ann comma) $
                                     map (prettySe (decD d) startPrec bnd) elts
        where ann = case pun of
                      TypeOrTerm -> id
                      IsType -> annName pairTy
                      IsTerm -> annName pairCon
    prettySe d p bnd dpair@(PDPair _ _ pun l t r)
      | Just elts <- dPairElts dpair
      = depth d . enclose (annotated lparen) (annotated rparen) .
        align . group . vsep . punctuate (space <> annotated (text "**")) $
        ppElts elts bnd
      | otherwise
      = depth d $
        annotated lparen <>
        left <+>
        annotated (text "**") <+>
        prettySe (decD d) startPrec (addBinding bnd) r <>
        annotated rparen
      where annotated = case pun of
              IsType -> annName sigmaTy
              IsTerm -> annName sigmaCon
              TypeOrTerm -> id

            (left, addBinding) = case (l, pun) of
              (PRef _ _ n, IsType) -> (bindingOf n False <+> text ":" <+> prettySe (decD d) startPrec bnd t, ((n, False) :))
              _ ->                    (prettySe (decD d) startPrec bnd l, id)

            ppElts [] bs = []
            ppElts [(_, v)] bs = [prettySe (decD d) startPrec bs v]
            ppElts ((PRef _ _ n, t):rs) bs
              | IsType <- pun
              =  (bindingOf n False <+> colon <+>
                  prettySe (decD d) startPrec bs t) : ppElts rs ((n, False):bs)
            ppElts ((l, t):rs) bs
              = (prettySe (decD d) startPrec bs l) : ppElts rs bs
    prettySe d p bnd (PAlternative ns a as) =
      lparen <> text "|" <> prettyAs <> text "|" <> rparen
        where
          prettyAs =
            foldr ((\ l r -> l <+> text "," <+> r) .
                    depth d . prettySe (decD d) startPrec bnd)
                  empty as
    prettySe d p bnd (PType _)        = annotate (AnnType "Type" "The type of types") $ text "Type"
    prettySe d p bnd (PUniverse _ u)  = annotate (AnnType (show u) "The type of unique types") $ text (show u)
    prettySe d p bnd (PConstant _ c)  = annotate (AnnConst c) (text (show c))
    -- XXX: add pretty for tactics
    prettySe d p bnd (PProof ts)      =
      kwd "proof" <+> lbrace <> ellipsis <> rbrace
    prettySe d p bnd (PTactics ts)    =
      kwd "tactics" <+> lbrace <> ellipsis <> rbrace
    prettySe d p bnd (PMetavar _ n)   = annotate (AnnName n (Just MetavarOutput) Nothing Nothing) $  text "?" <> pretty n
    prettySe d p bnd PImpossible      = kwd "impossible"
    prettySe d p bnd Placeholder      = text "_"
    prettySe d p bnd (PDoBlock dos)   =
      bracket p startPrec $
      kwd "do" <+> align (vsep (map (group . align . hang 2) (ppdo bnd dos)))
       where ppdo bnd (DoExp _ tm:dos) = prettySe (decD d) startPrec bnd tm : ppdo bnd dos
             ppdo bnd (DoBind _ bn _ tm : dos) =
               (prettyBindingOf bn False <+> text "<-" <+>
                group (align (hang 2 (prettySe (decD d) startPrec bnd tm)))) :
               ppdo ((bn, False):bnd) dos
             ppdo bnd (DoBindP _ _ _ _ : dos) = -- ok because never made by delab
               text "no pretty printer for pattern-matching do binding" :
               ppdo bnd dos
             ppdo bnd (DoLet _ ln _ ty v : dos) =
               (kwd "let" <+> prettyBindingOf ln False <+>
                (if ty /= Placeholder
                   then colon <+> prettySe (decD d) startPrec bnd ty <+> text "="
                   else text "=") <+>
                group (align (hang 2 (prettySe (decD d) startPrec bnd v)))) :
               ppdo ((ln, False):bnd) dos
             ppdo bnd (DoLetP _ _ _ : dos) = -- ok because never made by delab
               text "no pretty printer for pattern-matching do binding" :
               ppdo bnd dos
             ppdo _ [] = []
    prettySe d p bnd (PCoerced t)             = prettySe d p bnd t
    prettySe d p bnd (PElabError s)           = pretty s
    -- Quasiquote pprinting ignores bound vars
    prettySe d p bnd (PQuasiquote t Nothing)  = text "`(" <> prettySe (decD d) p [] t <> text ")"
    prettySe d p bnd (PQuasiquote t (Just g)) = text "`(" <> prettySe (decD d) p [] t <+> colon <+> prettySe (decD d) p [] g <> text ")"
    prettySe d p bnd (PUnquote t)             = text "~" <> prettySe (decD d) p bnd t
    prettySe d p bnd (PQuoteName n res _)     = text start <> prettyName True (ppopt_impl ppo) bnd n <> text end
      where start = if res then "`{" else "`{{"
            end = if res then "}" else "}}"
    prettySe d p bnd (PRunElab _ tm _)        =
      bracket p funcAppPrec . group . align . hang 2 $
      text "%runElab" <$>
      prettySe (decD d) funcAppPrec bnd tm
    prettySe d p bnd (PConstSugar fc tm)      = prettySe d p bnd tm -- should never occur, but harmless
    prettySe d p bnd _                        = text "missing pretty-printer for term"

    prettyBindingOf :: Name -> Bool -> Doc OutputAnnotation
    prettyBindingOf n imp = annotate (AnnBoundName n imp) (text (display n))
      where display (UN n)    = T.unpack n
            display (MN _ n)  = T.unpack n
            -- If a namespace is specified on a binding form, we'd better show it regardless of the implicits settings
            display (NS n ns) = (intercalate "." . map T.unpack . reverse) ns ++ "." ++ display n
            display n         = show n

    prettyArgS d bnd (PImp _ _ _ n tm)          = prettyArgSi d bnd (n, tm)
    prettyArgS d bnd (PExp _ _ _ tm)            = prettyArgSe d bnd tm
    prettyArgS d bnd (PConstraint _ _ _ tm)     = prettyArgSc d bnd tm
    prettyArgS d bnd (PTacImplicit _ _ n _ tm)  = prettyArgSti d bnd (n, tm)

    prettyArgSe d bnd arg       = prettySe d (funcAppPrec + 1) bnd arg
    prettyArgSi d bnd (n, val)  = lbrace <> pretty n <+> text "=" <+> prettySe (decD d) startPrec bnd val <> rbrace
    prettyArgSc d bnd val       = lbrace <> lbrace <> prettySe (decD d) startPrec bnd val <> rbrace <> rbrace
    prettyArgSti d bnd (n, val) = lbrace <> kwd "auto" <+> pretty n <+> text "=" <+> prettySe (decD d) startPrec bnd val <> rbrace

    annName :: Name -> Doc OutputAnnotation -> Doc OutputAnnotation
    annName n = annotate (AnnName n Nothing Nothing Nothing)

    opStr :: Name -> String
    opStr (NS n _)  = opStr n
    opStr (UN n)    = T.unpack n

    slist' :: Maybe Int -> Int -> [(Name, Bool)] -> PTerm -> Maybe [Doc OutputAnnotation]
    slist' (Just d) _ _ _ | d <= 0 = Nothing
    slist' d _ _ e
      | containsHole e = Nothing
    slist' d p bnd (PApp _ (PRef _ _ nil) _)
      | not (ppopt_impl ppo) && nsroot nil == sUN "Nil" = Just []
    slist' d p bnd (PRef _ _ nil)
      | not (ppopt_impl ppo) && nsroot nil == sUN "Nil" = Just []
    slist' d p bnd (PApp _ (PRef _ _ cons) args)
      | nsroot cons == sUN "::",
        (PExp {getTm=tl}):(PExp {getTm=hd}):imps <- reverse args,
        all isImp imps,
        Just tl' <- slist' (decD d) p bnd tl
      = Just (prettySe d startPrec bnd hd : tl')
      where
        isImp (PImp {}) = True
        isImp _ = False
    slist' _ _ _ tm = Nothing

    slist d p bnd e | Just es <- slist' d p bnd e = Just $
      case es of
        [] -> annotate (AnnData "" "") $ text "[]"
        [x] -> enclose left right . group $ x
        xs -> enclose left right .
              align . group . vsep .
              punctuate comma $ xs
      where left  = (annotate (AnnData "" "") (text "["))
            right = (annotate (AnnData "" "") (text "]"))
            comma = (annotate (AnnData "" "") (text ","))
    slist _ _ _ _ = Nothing

    pairElts :: PTerm -> Maybe [PTerm]
    pairElts (PPair _ _ _ x y) | Just elts <- pairElts y = Just (x:elts)
                               | otherwise = Just [x, y]
    pairElts _ = Nothing

    dPairElts :: PTerm -> Maybe [(PTerm, PTerm)]
    dPairElts (PDPair _ _ _ l t r) | Just elts <- dPairElts r = Just ((l, t):elts)
                                   | otherwise = Just [(l, t), (Placeholder, r)]
    dPairElts _ = Nothing

    natns = "Prelude.Nat."

    snat :: PPOption -> Maybe Int -> Int -> PTerm -> Maybe Integer
    snat ppo d p e
         | ppopt_desugarnats ppo = Nothing
         | otherwise = snat' d p e
         where
             snat' :: Maybe Int -> Int -> PTerm -> Maybe Integer
             snat' (Just x) _ _ | x <= 0 = Nothing
             snat' d p (PRef _ _ z)
               | show z == (natns++"Z") || show z == "Z" = Just 0
             snat' d p (PApp _ s [PExp {getTm=n}])
               | show s == (natns++"S") || show s == "S",
                 Just n' <- snat' (decD d) p n
                 = Just $ 1 + n'
             snat' _ _ _ = Nothing

    bracket outer inner doc
      | outer > inner = lparen <> doc <> rparen
      | otherwise     = doc

    ellipsis = text "..."

    depth Nothing = id
    depth (Just d) = if d <= 0 then const ellipsis else id

    decD = fmap (\x -> x - 1)

    kwd = annotate AnnKeyword . text

    fixities :: M.Map String Fixity
    fixities = M.fromList [(s, f) | (Fix f s) <- infixes]

    getFixity :: String -> Maybe Fixity
    getFixity = flip M.lookup fixities

-- | Strip away namespace information
basename :: Name -> Name
basename (NS n _) = basename n
basename n        = n

-- | Determine whether a name was the one inserted for a hole or guess
-- by the delaborator
isHoleName :: Name -> Bool
isHoleName (UN n) = n == T.pack "[__]"
isHoleName _      = False

-- | Check whether a PTerm has been delaborated from a Term containing a Hole or Guess
containsHole :: PTerm -> Bool
containsHole pterm = or [isHoleName n | PRef _ _ n <- take 1000 $ universe pterm]

-- | Pretty-printer helper for names that attaches the correct annotations
prettyName :: Bool           -- ^ whether the name should be parenthesised if it is an infix operator
           -> Bool           -- ^ whether to show namespaces
           -> [(Name, Bool)] -- ^ the current bound variables and whether they are implicit
           -> Name           -- ^ the name to pprint
           -> Doc OutputAnnotation
prettyName infixParen showNS bnd n
    | (MN _ s)  <- n, isPrefixOf "_" $ T.unpack s = text "_"
    | (UN n')   <- n, isPrefixOf "__" $ T.unpack n' = text "_"
    | (UN n')   <- n, T.unpack n' == "_" = text "_"
    | Just imp  <- lookup n bnd = annotate (AnnBoundName n imp) fullName
    | otherwise                 = annotate (AnnName n Nothing Nothing Nothing) fullName
  where fullName = text nameSpace <> parenthesise (text (baseName n))
        baseName (UN n)     = T.unpack n
        baseName (NS n ns)  = baseName n
        baseName (MN i s)   = T.unpack s
        baseName other      = show other
        nameSpace = case n of
          (NS n' ns) -> if showNS then (concatMap (++ ".") . map T.unpack . reverse) ns else ""
          _ -> ""
        isInfix = case baseName n of
          ""      -> False
          (c : _) -> not (isAlpha c)
        parenthesise = if isInfix && infixParen then enclose lparen rparen else id


showCImp :: PPOption -> PClause -> Doc OutputAnnotation
showCImp ppo (PClause _ n l ws r w)
 = prettyImp ppo l <+> showWs ws <+> text "=" <+> prettyImp ppo r
             <+> text "where" <+> text (show w)
  where
    showWs []       = empty
    showWs (x : xs) = text "|" <+> prettyImp ppo x <+> showWs xs
showCImp ppo (PWith _ n l ws r pn w)
 = prettyImp ppo l <+> showWs ws <+> text "with" <+> prettyImp ppo r
                 <+> braces (text (show w))
  where
    showWs []       = empty
    showWs (x : xs) = text "|" <+> prettyImp ppo x <+> showWs xs


showDImp :: PPOption -> PData -> Doc OutputAnnotation
showDImp ppo (PDatadecl n nfc ty cons)
 = text "data" <+> text (show n) <+> colon <+> prettyImp ppo ty <+> text "where" <$>
    (indent 2 $ vsep (map (\ (_, _, n, _, t, _, _) -> pipe <+> prettyName True False [] n <+> colon <+> prettyImp ppo t) cons))

showDecls :: PPOption -> [PDecl] -> Doc OutputAnnotation
showDecls o ds = vsep (map (showDeclImp o) ds)

showDeclImp _ (PFix _ f ops)        = text (show f) <+> cat (punctuate (text ",") (map text ops))
showDeclImp o (PTy _ _ _ _ _ n _ t) = text "tydecl" <+> text (showCG n) <+> colon <+> prettyImp o t
showDeclImp o (PClauses _ _ n cs)   = text "pat" <+> text (showCG n) <+> text "\t" <+>
                                      indent 2 (vsep (map (showCImp o) cs))
showDeclImp o (PData _ _ _ _ _ d)   = showDImp o { ppopt_impl = True } d
showDeclImp o (PParams _ ns ps)     = text "params" <+> braces (text (show ns) <> line <> showDecls o ps <> line)
showDeclImp o (POpenInterfaces _ ns ps) = text "open" <+> braces (text (show ns) <> line <> showDecls o ps <> line)
showDeclImp o (PNamespace n fc ps)  = text "namespace" <+> text n <> braces (line <> showDecls o ps <> line)
showDeclImp _ (PSyntax _ syn) = text "syntax" <+> text (show syn)
showDeclImp o (PInterface _ _ _ cs n _ ps _ _ ds _ _)
   = text "interface" <+> text (show cs) <+> text (show n) <+> text (show ps) <> line <> showDecls o ds
showDeclImp o (PImplementation _ _ _ _ cs _ acc _ n _ _ _ t _ ds)
   = text "implementation" <+> text (show cs) <+> text (show n) <+> prettyImp o t <> line <> showDecls o ds
showDeclImp _ _ = text "..."
-- showDeclImp (PImport o) = "import " ++ o

getImps :: [PArg] -> [(Name, PTerm)]
getImps [] = []
getImps (PImp _ _ _ n tm : xs)  = (n, tm) : getImps xs
getImps (_ : xs)                = getImps xs

getExps :: [PArg] -> [PTerm]
getExps [] = []
getExps (PExp _ _ _ tm : xs)  = tm : getExps xs
getExps (_ : xs)              = getExps xs

getShowArgs :: [PArg] -> [PArg]
getShowArgs [] = []
getShowArgs (e@(PExp _ _ _ _) : xs) = e : getShowArgs xs
getShowArgs (e : xs) | AlwaysShow `elem` argopts e = e : getShowArgs xs
                     | PImp _ _ _ _ tm <- e
                     , containsHole tm = e : getShowArgs xs
getShowArgs (_ : xs) = getShowArgs xs

getConsts :: [PArg] -> [PTerm]
getConsts []                          = []
getConsts (PConstraint _ _ _ tm : xs) = tm : getConsts xs
getConsts (_ : xs)                    = getConsts xs

getAll :: [PArg] -> [PTerm]
getAll = map getTm


-- | Show Idris name
showName :: Maybe IState   -- ^ the Idris state, for information about names and colours
         -> [(Name, Bool)] -- ^ the bound variables and whether they're implicit
         -> PPOption       -- ^ pretty printing options
         -> Bool           -- ^ whether to colourise
         -> Name           -- ^ the term to show
         -> String
showName ist bnd ppo colour n = case ist of
                                   Just i   -> if colour then colourise n (idris_colourTheme i) else showbasic n
                                   Nothing  -> showbasic n
    where name = if ppopt_impl ppo then show n else showbasic n
          showbasic n@(UN _)  = showCG n
          showbasic (MN i s)  = str s
          showbasic (NS n s)  = showSep "." (map str (reverse s)) ++ "." ++ showbasic n
          showbasic (SN s)    = show s
          fst3 (x, _, _) = x
          colourise n t = let ctxt' = fmap tt_ctxt ist in
                          case ctxt' of
                            Nothing -> name
                            Just ctxt | Just impl <- lookup n bnd -> if impl then colouriseImplicit t name
                                                                             else colouriseBound t name
                                      | isDConName n ctxt -> colouriseData t name
                                      | isFnName n ctxt   -> colouriseFun t name
                                      | isTConName n ctxt -> colouriseType t name
                                      -- The assumption is that if a name is not bound and does not exist in the
                                      -- global context, then we're somewhere in which implicit info has been lost
                                      -- (like error messages). Thus, unknown vars are colourised as implicits.
                                      | otherwise         -> colouriseImplicit t name

showTm :: IState -- ^ the Idris state, for information about identifiers and colours
       -> PTerm  -- ^ the term to show
       -> String
showTm ist = displayDecorated (consoleDecorate ist) .
             renderPretty 0.8 100000 .
             prettyImp (ppOptionIst ist)

-- | Show a term with implicits, no colours
showTmImpls :: PTerm -> String
showTmImpls = flip (displayS . renderCompact . prettyImp verbosePPOption) ""

-- | Show a term with specific options
showTmOpts :: PPOption -> PTerm -> String
showTmOpts opt = flip (displayS . renderPretty 1.0 10000000 . prettyImp opt) ""


instance Sized PTerm where
  size (PQuote rawTerm)               = size rawTerm
  size (PRef fc _ name)               = size name
  size (PLam fc name _ ty bdy)        = 1 + size ty + size bdy
  size (PPi plicity name fc ty bdy)   = 1 + size ty + size fc + size bdy
  size (PLet fc name nfc ty def bdy)  = 1 + size ty + size def + size bdy
  size (PTyped trm ty)                = 1 + size trm + size ty
  size (PApp fc name args)            = 1 + size args
  size (PAppBind fc name args)        = 1 + size args
  size (PCase fc trm bdy)             = 1 + size trm + size bdy
  size (PIfThenElse fc c t f)         = 1 + sum (map size [c, t, f])
  size (PTrue fc _)                   = 1
  size (PResolveTC fc)                = 1
  size (PRewrite fc by left right _)  = 1 + size left + size right
  size (PPair fc _ _ left right)      = 1 + size left + size right
  size (PDPair fs _ _ left ty right)  = 1 + size left + size ty + size right
  size (PAlternative _ a alts)        = 1 + size alts
  size (PHidden hidden)               = size hidden
  size (PUnifyLog tm)                 = size tm
  size (PDisamb _ tm)                 = size tm
  size (PNoImplicits tm)              = size tm
  size (PType _)                      = 1
  size (PUniverse _ _)                = 1
  size (PConstant fc const)           = 1 + size fc + size const
  size Placeholder                    = 1
  size (PDoBlock dos)                 = 1 + size dos
  size (PIdiom fc term)               = 1 + size term
  size (PMetavar _ name)              = 1
  size (PProof tactics)               = size tactics
  size (PElabError err)               = size err
  size PImpossible                    = 1
  size _                              = 0

getPArity :: PTerm -> Int
getPArity (PPi _ _ _ _ sc)  = 1 + getPArity sc
getPArity _                 = 0

-- Return all names, free or globally bound, in the given term.

allNamesIn :: PTerm -> [Name]
allNamesIn tm = nub $ ni 0 [] tm
  where -- TODO THINK added niTacImp, but is it right?
    ni 0 env (PRef _ _ n)
        | not (n `elem` env)          = [n]
    ni 0 env (PPatvar _ n)            = [n]
    ni 0 env (PApp _ f as)            = ni 0 env f ++ concatMap (ni 0 env . getTm) as
    ni 0 env (PAppBind _ f as)        = ni 0 env f ++ concatMap (ni 0 env . getTm) as
    ni 0 env (PCase _ c os)           = ni 0 env c ++ concatMap (ni 0 env . snd) os
    ni 0 env (PIfThenElse _ c t f)    = ni 0 env c ++ ni 0 env t ++ ni 0 env f
    ni 0 env (PLam fc n _ ty sc)      = ni 0 env ty ++ ni 0 (n:env) sc
    ni 0 env (PPi p n _ ty sc)        = niTacImp 0 env p ++ ni 0 env ty ++ ni 0 (n:env) sc
    ni 0 env (PLet _ n _ ty val sc)   = ni 0 env ty ++ ni 0 env val ++ ni 0 (n:env) sc
    ni 0 env (PHidden tm)             = ni 0 env tm
    ni 0 env (PRewrite _ _ l r _)     = ni 0 env l ++ ni 0 env r
    ni 0 env (PTyped l r)             = ni 0 env l ++ ni 0 env r
    ni 0 env (PPair _ _ _ l r)        = ni 0 env l ++ ni 0 env r
    ni 0 env (PDPair _ _ _ (PRef _ _ n) Placeholder r) = n : ni 0 env r
    ni 0 env (PDPair _ _ _ (PRef _ _ n) t r) = ni 0 env t ++ ni 0 (n:env) r
    ni 0 env (PDPair _ _ _ l t r)     = ni 0 env l ++ ni 0 env t ++ ni 0 env r
    ni 0 env (PAlternative ns a ls)   = map snd ns ++ concatMap (ni 0 env) ls
    ni 0 env (PUnifyLog tm)           = ni 0 env tm
    ni 0 env (PDisamb _ tm)           = ni 0 env tm
    ni 0 env (PNoImplicits tm)        = ni 0 env tm

    ni i env (PQuasiquote tm ty)  = ni (i+1) env tm ++ maybe [] (ni i env) ty
    ni i env (PUnquote tm)        = ni (i - 1) env tm
    ni i env tm                   = concatMap (ni i env) (children tm)

    niTacImp i env (TacImp _ _ scr _) = ni i env scr
    niTacImp _ _ _                  = []


-- Return all names defined in binders in the given term
boundNamesIn :: PTerm -> [Name]
boundNamesIn tm = S.toList (ni 0 S.empty tm)
  where -- TODO THINK Added niTacImp, but is it right?
    ni :: Int -> S.Set Name -> PTerm -> S.Set Name
    ni 0 set (PApp _ f as)              = niTms 0 (ni 0 set f) (map getTm as)
    ni 0 set (PAppBind _ f as)          = niTms 0 (ni 0 set f) (map getTm as)
    ni 0 set (PCase _ c os)             = niTms 0 (ni 0 set c) (map snd os)
    ni 0 set (PIfThenElse _ c t f)      = niTms 0 set [c, t, f]
    ni 0 set (PLam fc n _ ty sc)        = S.insert n $ ni 0 (ni 0 set ty) sc
    ni 0 set (PLet fc n nfc ty val sc)  = S.insert n $ ni 0 (ni 0 (ni 0 set ty) val) sc
    ni 0 set (PPi p n _ ty sc)          = niTacImp 0 (S.insert n $ ni 0 (ni 0 set ty) sc) p
    ni 0 set (PRewrite _ _ l r _)       = ni 0 (ni 0 set l) r
    ni 0 set (PTyped l r)               = ni 0 (ni 0 set l) r
    ni 0 set (PPair _ _ _ l r)          = ni 0 (ni 0 set l) r
    ni 0 set (PDPair _ _ _ (PRef _ _ n) t r) = ni 0 (ni 0 set t) r
    ni 0 set (PDPair _ _ _ l t r)       = ni 0 (ni 0 (ni 0 set l) t) r
    ni 0 set (PAlternative ns a as)     = niTms 0 set as
    ni 0 set (PHidden tm)               = ni 0 set tm
    ni 0 set (PUnifyLog tm)             = ni 0 set tm
    ni 0 set (PDisamb _ tm)             = ni 0 set tm
    ni 0 set (PNoImplicits tm)          = ni 0 set tm

    ni i set (PQuasiquote tm ty)        = ni (i + 1) set tm `S.union` maybe S.empty (ni i set) ty
    ni i set (PUnquote tm)              = ni (i - 1) set tm

    ni i set tm                         = foldr (S.union . ni i set) set (children tm)

    niTms :: Int -> S.Set Name -> [PTerm] -> S.Set Name
    niTms i set []        = set
    niTms i set (x : xs)  = niTms i (ni i set x) xs

    niTacImp i set (TacImp _ _ scr _) = ni i set scr
    niTacImp i set _                = set

-- Return names which are valid implicits in the given term (type).
implicitNamesIn :: [Name] -> IState -> PTerm -> [Name]
implicitNamesIn uvars ist tm
      = let (imps, fns) = execState (ni 0 [] tm) ([], []) in
            nub imps \\ nub fns
  where
    addImp n = do (imps, fns) <- get
                  put (n : imps, fns)
    addFn n = do (imps, fns) <- get
                 put (imps, n: fns)

    notCAF []                 = False
    notCAF (PExp _ _ _ _ : _) = True
    notCAF (_ : xs)           = notCAF xs

    notHidden (n, _) = case getAccessibility n of
                            Hidden  -> False
                            Private -> False
                            _       -> True

    getAccessibility n
             = case lookupDefAccExact n False (tt_ctxt ist) of
                    Just (n,t)  -> t
                    _           -> Public

    ni 0 env (PRef _ _ n@(NS _ _))
        | not (n `elem` env)
          -- Never implicitly bind if there's a namespace
            = addFn n
    ni 0 env (PRef _ _ n)
        | not (n `elem` env) && implicitable n || n `elem` uvars = addImp n
    ni 0 env (PApp _ f@(PRef _ _ n) as)
        | n `elem` uvars = do ni 0 env f
                              mapM_ (ni 0 env . getTm) as
        | otherwise = do case lookupTy n (tt_ctxt ist) of
                              []  -> return ()
                              _   -> addFn n
                         mapM_ (ni 0 env . getTm) as
    ni 0 env (PApp _ f as) = do ni 0 env f
                                mapM_ (ni 0 env . getTm) as
    ni 0 env (PAppBind _ f as) = do ni 0 env f
                                    mapM_ (ni 0 env . getTm) as
    ni 0 env (PCase _ c os)  = do ni 0 env c
    -- names in 'os', not counting the names bound in the cases
                                  mapM_ (ni 0 env . snd) os
                                  (imps, fns) <- get
                                  put ([] ,[])
                                  mapM_ (ni 0 env . fst) os
                                  (impsfst, _) <- get
                                  put (nub imps \\ nub impsfst, fns)
    ni 0 env (PIfThenElse _ c t f)            = mapM_ (ni 0 env) [c, t, f]
    ni 0 env (PLam fc n _ ty sc)              = do ni 0 env ty; ni 0 (n:env) sc
    ni 0 env (PPi p n _ ty sc)                = do ni 0 env ty; ni 0 (n:env) sc
    ni 0 env (PLet fc n _ ty val sc)          = do ni 0 env ty;
                                                   ni 0 env val; ni 0 (n:env) sc
    ni 0 env (PRewrite _ _ l r _)             = do ni 0 env l; ni 0 env r
    ni 0 env (PTyped l r)                     = do ni 0 env l; ni 0 env r
    ni 0 env (PPair _ _ _ l r)                = do ni 0 env l; ni 0 env r
    ni 0 env (PDPair _ _ _ (PRef _ _ n) t r)  = do ni 0 env t; ni 0 (n:env) r
    ni 0 env (PDPair _ _ _ l t r)             = do ni 0 env l
                                                   ni 0 env t
                                                   ni 0 env r
    ni 0 env (PAlternative ns a as)           = mapM_ (ni 0 env) as
    ni 0 env (PHidden tm)                     = ni 0 env tm
    ni 0 env (PUnifyLog tm)                   = ni 0 env tm
    ni 0 env (PDisamb _ tm)                   = ni 0 env tm
    ni 0 env (PNoImplicits tm)                = ni 0 env tm

    ni i env (PQuasiquote tm ty) = do ni (i + 1) env tm
                                      maybe (return ()) (ni i env) ty
    ni i env (PUnquote tm) = ni (i - 1) env tm

    ni i env tm = mapM_ (ni i env) (children tm)

-- Return names which are free in the given term.
namesIn :: [(Name, PTerm)] -> IState -> PTerm -> [Name]
namesIn uvars ist tm = nub $ ni 0 [] tm
  where
    ni 0 env (PRef _ _ n)
        | not (n `elem` env)
            = case lookupTy n (tt_ctxt ist) of
                []  -> [n]
                _   -> [n | n `elem` (map fst uvars)]
    ni 0 env (PApp _ f as)      = ni 0 env f ++ concatMap (ni 0 env . getTm) as
    ni 0 env (PAppBind _ f as)  = ni 0 env f ++ concatMap (ni 0 env . getTm) as
    ni 0 env (PCase _ c os)     = ni 0 env c ++
    -- names in 'os', not counting the names bound in the cases
                                (nub (concatMap (ni 0 env . snd) os)
                                     \\ nub (concatMap (ni 0 env . fst) os))
    ni 0 env (PIfThenElse _ c t f)  = concatMap (ni 0 env) [c, t, f]
    ni 0 env (PLam fc n nfc ty sc)  = ni 0 env ty ++ ni 0 (n:env) sc
    ni 0 env (PPi p n _ ty sc)      = niTacImp 0 env p ++ ni 0 env ty ++ ni 0 (n:env) sc
    ni 0 env (PRewrite _ _ l r _)   = ni 0 env l ++ ni 0 env r
    ni 0 env (PTyped l r)           = ni 0 env l ++ ni 0 env r
    ni 0 env (PPair _ _ _ l r)      = ni 0 env l ++ ni 0 env r
    ni 0 env (PDPair _ _ _ (PRef _ _ n) t r) = ni 0 env t ++ ni 0 (n:env) r
    ni 0 env (PDPair _ _ _ l t r)   = ni 0 env l ++ ni 0 env t ++ ni 0 env r
    ni 0 env (PAlternative ns a as) = concatMap (ni 0 env) as
    ni 0 env (PHidden tm)           = ni 0 env tm
    ni 0 env (PUnifyLog tm)         = ni 0 env tm
    ni 0 env (PDisamb _ tm)         = ni 0 env tm
    ni 0 env (PNoImplicits tm)      = ni 0 env tm

    ni i env (PQuasiquote tm ty)    = ni (i + 1) env tm ++ maybe [] (ni i env) ty
    ni i env (PUnquote tm)          = ni (i - 1) env tm

    ni i env tm                     = concatMap (ni i env) (children tm)

    niTacImp i env (TacImp _ _ scr _) = ni i env scr
    niTacImp _ _ _                  = []

-- Return which of the given names are used in the given term.

usedNamesIn :: [Name] -> IState -> PTerm -> [Name]
usedNamesIn vars ist tm = nub $ ni 0 [] tm
  where -- TODO THINK added niTacImp, but is it right?
    ni 0 env (PRef _ _ n)
        | n `elem` vars && not (n `elem` env)
            = case lookupDefExact n (tt_ctxt ist) of
                Nothing -> [n]
                _ -> []
    ni 0 env (PApp _ f as)          = ni 0 env f ++ concatMap (ni 0 env . getTm) as
    ni 0 env (PAppBind _ f as)      = ni 0 env f ++ concatMap (ni 0 env . getTm) as
    ni 0 env (PCase _ c os)         = ni 0 env c ++ concatMap (ni 0 env . snd) os
    ni 0 env (PIfThenElse _ c t f)  = concatMap (ni 0 env) [c, t, f]
    ni 0 env (PLam fc n _ ty sc)    = ni 0 env ty ++ ni 0 (n:env) sc
    ni 0 env (PPi p n _ ty sc)      = niTacImp 0 env p ++ ni 0 env ty ++ ni 0 (n:env) sc
    ni 0 env (PRewrite _ _ l r _)   = ni 0 env l ++ ni 0 env r
    ni 0 env (PTyped l r)           = ni 0 env l ++ ni 0 env r
    ni 0 env (PPair _ _ _ l r)      = ni 0 env l ++ ni 0 env r
    ni 0 env (PDPair _ _ _ (PRef _ _ n) t r) = ni 0 env t ++ ni 0 (n:env) r
    ni 0 env (PDPair _ _ _ l t r)   = ni 0 env l ++ ni 0 env t ++ ni 0 env r
    ni 0 env (PAlternative ns a as) = concatMap (ni 0 env) as
    ni 0 env (PHidden tm)           = ni 0 env tm
    ni 0 env (PUnifyLog tm)         = ni 0 env tm
    ni 0 env (PDisamb _ tm)         = ni 0 env tm
    ni 0 env (PNoImplicits tm)      = ni 0 env tm

    ni i env (PQuasiquote tm ty)    = ni (i + 1) env tm ++ maybe [] (ni i env) ty
    ni i env (PUnquote tm)          = ni (i - 1) env tm

    ni i env tm                     = concatMap (ni i env) (children tm)

    niTacImp i env (TacImp _ _ scr _) = ni i env scr
    niTacImp _ _ _                = []

-- Return the list of inaccessible (= dotted) positions for a name.
getErasureInfo :: IState -> Name -> [Int]
getErasureInfo ist n =
    case lookupCtxtExact n (idris_optimisation ist) of
        Just (Optimise inacc _ _) -> map fst inacc
        Nothing -> []

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             DeriveDataTypeable, TypeSynonymInstances, PatternGuards #-}

module Idris.AbsSyntaxTree where

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Typecheck
import Idris.Docstrings
import IRTS.Lang
import IRTS.CodegenCommon
import Util.Pretty
import Util.DynamicLinker

import Idris.Colours

import System.Console.Haskeline
import System.IO

import Control.Applicative ((<|>))

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Except
import qualified Control.Monad.Trans.Class as Trans (lift)

import Data.Data (Data)
import Data.Function (on)
import Data.Generics.Uniplate.Data (universe)
import Data.List hiding (group)
import Data.Char
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Data.Either
import qualified Data.Set as S
import Data.Word (Word)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Traversable (Traversable)
import Data.Typeable
import Data.Foldable (Foldable)

import Debug.Trace

import Text.PrettyPrint.Annotated.Leijen

data ElabWhat = ETypes | EDefns | EAll
  deriving (Show, Eq)

-- Data to pass to recursively called elaborators; e.g. for where blocks,
-- paramaterised declarations, etc.

-- rec_elabDecl is used to pass the top level elaborator into other elaborators,
-- so that we can have mutually recursive elaborators in separate modules without
-- having to muck about with cyclic modules.
data ElabInfo = EInfo { params :: [(Name, PTerm)],
                        inblock :: Ctxt [Name], -- names in the block, and their params
                        liftname :: Name -> Name,
                        namespace :: Maybe [String],
                        elabFC :: Maybe FC,
                        rec_elabDecl :: ElabWhat -> ElabInfo -> PDecl -> 
                                        Idris () }

toplevel :: ElabInfo
toplevel = EInfo [] emptyContext id Nothing Nothing (\_ _ _ -> fail "Not implemented")

eInfoNames :: ElabInfo -> [Name]
eInfoNames info = map fst (params info) ++ M.keys (inblock info)

data IOption = IOption { opt_logLevel   :: Int,
                         opt_typecase   :: Bool,
                         opt_typeintype :: Bool,
                         opt_coverage   :: Bool,
                         opt_showimp    :: Bool, -- ^^ show implicits
                         opt_errContext :: Bool,
                         opt_repl       :: Bool,
                         opt_verbose    :: Bool,
                         opt_nobanner   :: Bool,
                         opt_quiet      :: Bool,
                         opt_codegen    :: Codegen,
                         opt_outputTy   :: OutputType,
                         opt_ibcsubdir  :: FilePath,
                         opt_importdirs :: [FilePath],
                         opt_triple     :: String,
                         opt_cpu        :: String,
                         opt_cmdline    :: [Opt], -- remember whole command line
                         opt_origerr    :: Bool,
                         opt_autoSolve  :: Bool, -- ^ automatically apply "solve" tactic in prover
                         opt_autoImport :: [FilePath], -- ^ e.g. Builtins+Prelude
                         opt_optimise   :: [Optimisation]
                       }
    deriving (Show, Eq)

defaultOpts = IOption { opt_logLevel   = 0
                      , opt_typecase   = False
                      , opt_typeintype = False
                      , opt_coverage   = True
                      , opt_showimp    = False
                      , opt_errContext = False
                      , opt_repl       = True
                      , opt_verbose    = True
                      , opt_nobanner   = False
                      , opt_quiet      = False
                      , opt_codegen    = Via "c"
                      , opt_outputTy   = Executable
                      , opt_ibcsubdir  = ""
                      , opt_importdirs = []
                      , opt_triple     = ""
                      , opt_cpu        = ""
                      , opt_cmdline    = []
                      , opt_origerr    = False
                      , opt_autoSolve  = True
                      , opt_autoImport = []
                      , opt_optimise   = defaultOptimise
                      }

data PPOption = PPOption {
    ppopt_impl :: Bool -- ^^ whether to show implicits
} deriving (Show)

data Optimisation = PETransform -- partial eval and associated transforms
  deriving (Show, Eq)

defaultOptimise = [PETransform]

-- | Pretty printing options with default verbosity.
defaultPPOption :: PPOption
defaultPPOption = PPOption { ppopt_impl = False }

-- | Pretty printing options with the most verbosity.
verbosePPOption :: PPOption
verbosePPOption = PPOption { ppopt_impl = True }

-- | Get pretty printing options from the big options record.
ppOption :: IOption -> PPOption
ppOption opt = PPOption {
    ppopt_impl = opt_showimp opt
}

-- | Get pretty printing options from an idris state record.
ppOptionIst :: IState -> PPOption
ppOptionIst = ppOption . idris_options

data LanguageExt = TypeProviders | ErrorReflection deriving (Show, Eq, Read, Ord)

-- | The output mode in use
data OutputMode = RawOutput Handle -- ^ Print user output directly to the handle
                | IdeMode Integer Handle -- ^ Send IDE output for some request ID to the handle
                deriving Show

-- | How wide is the console?
data ConsoleWidth = InfinitelyWide -- ^ Have pretty-printer assume that lines should not be broken
                  | ColsWide Int -- ^ Manually specified - must be positive
                  | AutomaticWidth -- ^ Attempt to determine width, or 80 otherwise

-- | The global state used in the Idris monad
data IState = IState {
    tt_ctxt :: Context, -- ^ All the currently defined names and their terms
    idris_constraints :: [(UConstraint, FC)],
      -- ^ A list of universe constraints and their corresponding source locations
    idris_infixes :: [FixDecl], -- ^ Currently defined infix operators
    idris_implicits :: Ctxt [PArg],
    idris_statics :: Ctxt [Bool],
    idris_classes :: Ctxt ClassInfo,
    idris_dsls :: Ctxt DSL,
    idris_optimisation :: Ctxt OptInfo,
    idris_datatypes :: Ctxt TypeInfo,
    idris_namehints :: Ctxt [Name],
    idris_patdefs :: Ctxt ([([Name], Term, Term)], [PTerm]), -- not exported
      -- ^ list of lhs/rhs, and a list of missing clauses
    idris_flags :: Ctxt [FnOpt],
    idris_callgraph :: Ctxt CGInfo, -- name, args used in each pos
    idris_calledgraph :: Ctxt [Name],
    idris_docstrings :: Ctxt (Docstring DocTerm, [(Name, Docstring DocTerm)]),
    idris_moduledocs :: Ctxt (Docstring DocTerm),
    -- ^ module documentation is saved in a special MN so the context
    -- mechanism can be used for disambiguation
    idris_tyinfodata :: Ctxt TIData,
    idris_fninfo :: Ctxt FnInfo,
    idris_transforms :: Ctxt [(Term, Term)],
    idris_totcheck :: [(FC, Name)], -- names to check totality on
    idris_defertotcheck :: [(FC, Name)], -- names to check at the end
    idris_totcheckfail :: [(FC, String)],
    idris_options :: IOption,
    idris_name :: Int,
    idris_lineapps :: [((FilePath, Int), PTerm)],
          -- ^ Full application LHS on source line
    idris_metavars :: [(Name, (Maybe Name, Int, Bool))], -- ^ The currently defined but not proven metavariables
    idris_coercions :: [Name],
    idris_errRev :: [(Term, Term)],
    syntax_rules :: SyntaxRules,
    syntax_keywords :: [String],
    imported :: [FilePath], -- ^ The imported modules
    idris_scprims :: [(Name, (Int, PrimFn))],
    idris_objs :: [(Codegen, FilePath)],
    idris_libs :: [(Codegen, String)],
    idris_cgflags :: [(Codegen, String)],
    idris_hdrs :: [(Codegen, String)],
    idris_imported :: [(FilePath, Bool)], -- ^ Imported ibc file names, whether public
    proof_list :: [(Name, [String])],
    errSpan :: Maybe FC,
    parserWarnings :: [(FC, Err)],
    lastParse :: Maybe Name,
    indent_stack :: [Int],
    brace_stack :: [Maybe Int],
    lastTokenSpan :: Maybe FC, -- ^ What was the span of the latest token parsed?
    idris_parsedSpan :: Maybe FC,
    hide_list :: [(Name, Maybe Accessibility)],
    default_access :: Accessibility,
    default_total :: Bool,
    ibc_write :: [IBCWrite],
    compiled_so :: Maybe String,
    idris_dynamic_libs :: [DynamicLib],
    idris_language_extensions :: [LanguageExt],
    idris_outputmode :: OutputMode,
    idris_colourRepl :: Bool,
    idris_colourTheme :: ColourTheme,
    idris_errorhandlers :: [Name], -- ^ Global error handlers
    idris_nameIdx :: (Int, Ctxt (Int, Name)),
    idris_function_errorhandlers :: Ctxt (M.Map Name (S.Set Name)), -- ^ Specific error handlers
    module_aliases :: M.Map [T.Text] [T.Text],
    idris_consolewidth :: ConsoleWidth, -- ^ How many chars wide is the console?
    idris_postulates :: S.Set Name,
    idris_erasureUsed :: [(Name, Int)], -- ^ Function/constructor name, argument position is used
    idris_whocalls :: Maybe (M.Map Name [Name]),
    idris_callswho :: Maybe (M.Map Name [Name]),
    idris_repl_defs :: [Name], -- ^ List of names that were defined in the repl, and can be re-/un-defined
    elab_stack :: [Name], -- ^ Stack of names currently being elaborated
    idris_symbols :: M.Map Name Name -- ^ Symbol table (preserves sharing of names)
   }

-- Required for parsers library, and therefore trifecta
instance Show IState where
  show = const "{internal state}"

data SizeChange = Smaller | Same | Bigger | Unknown
    deriving (Show, Eq)
{-!
deriving instance Binary SizeChange
deriving instance NFData SizeChange
!-}

type SCGEntry = (Name, [Maybe (Int, SizeChange)])
type UsageReason = (Name, Int)  -- fn_name, its_arg_number

data CGInfo = CGInfo { argsdef :: [Name],
                       calls :: [(Name, [[Name]])],
                       scg :: [SCGEntry],
                       argsused :: [Name],
                       usedpos :: [(Int, [UsageReason])] }
    deriving Show
{-!
deriving instance Binary CGInfo
deriving instance NFData CGInfo
!-}

primDefs = [sUN "unsafePerformPrimIO",
            sUN "mkLazyForeignPrim",
            sUN "mkForeignPrim",
            sUN "void"]

-- information that needs writing for the current module's .ibc file
data IBCWrite = IBCFix FixDecl
              | IBCImp Name
              | IBCStatic Name
              | IBCClass Name
              | IBCInstance Bool Name Name
              | IBCDSL Name
              | IBCData Name
              | IBCOpt Name
              | IBCMetavar Name
              | IBCSyntax Syntax
              | IBCKeyword String
              | IBCImport (Bool, FilePath) -- True = import public
              | IBCImportDir FilePath
              | IBCObj Codegen FilePath
              | IBCLib Codegen String
              | IBCCGFlag Codegen String
              | IBCDyLib String
              | IBCHeader Codegen String
              | IBCAccess Name Accessibility
              | IBCMetaInformation Name MetaInformation
              | IBCTotal Name Totality
              | IBCFlags Name [FnOpt]
              | IBCFnInfo Name FnInfo
              | IBCTrans Name (Term, Term)
              | IBCErrRev (Term, Term)
              | IBCCG Name
              | IBCDoc Name
              | IBCCoercion Name
              | IBCDef Name -- i.e. main context
              | IBCNameHint (Name, Name)
              | IBCLineApp FilePath Int PTerm
              | IBCErrorHandler Name
              | IBCFunctionErrorHandler Name Name Name
              | IBCPostulate Name
              | IBCTotCheckErr FC String
              | IBCParsedRegion FC
              | IBCModDocs Name -- ^ The name is the special name used to track module docs
              | IBCUsage (Name, Int)
  deriving Show

-- | The initial state for the compiler
idrisInit :: IState
idrisInit = IState initContext [] []
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   [] [] [] defaultOpts 6 [] [] [] [] emptySyntaxRules [] [] [] [] [] [] []
                   [] [] Nothing [] Nothing [] [] Nothing Nothing [] Hidden False [] Nothing [] []
                   (RawOutput stdout) True defaultTheme [] (0, emptyContext) emptyContext M.empty
                   AutomaticWidth S.empty [] Nothing Nothing [] [] M.empty

-- | The monad for the main REPL - reading and processing files and updating
-- global state (hence the IO inner monad).
--type Idris = WriterT [Either String (IO ())] (State IState a))
type Idris = StateT IState (ExceptT Err IO)

catchError :: Idris a -> (Err -> Idris a) -> Idris a
catchError = liftCatch catchE

throwError :: Err -> Idris a
throwError = Trans.lift . throwE

-- Commands in the REPL

data Codegen = Via String
--              | ViaC
--              | ViaJava
--              | ViaNode
--              | ViaJavaScript
--              | ViaLLVM
             | Bytecode
    deriving (Show, Eq)
{-!
deriving instance NFData Codegen
!-}

-- | REPL commands
data Command = Quit
             | Help
             | Eval PTerm
             | NewDefn [PDecl] -- ^ Each 'PDecl' should be either a type declaration (at most one) or a clause defining the same name.
             | Undefine [Name]
             | Check PTerm
             | DocStr (Either Name Const)
             | TotCheck Name
             | Reload
             | Load FilePath (Maybe Int) -- up to maximum line number
             | ChangeDirectory FilePath
             | ModImport String
             | Edit
             | Compile Codegen String
             | Execute
             | ExecVal PTerm
             | Metavars
             | Prove Name
             | AddProof (Maybe Name)
             | RmProof Name
             | ShowProof Name
             | Proofs
             | Universes
             | LogLvl Int
             | Spec PTerm
             | HNF PTerm
             | TestInline PTerm
             | Defn Name
             | Missing Name
             | DynamicLink FilePath
             | ListDynamic
             | Pattelab PTerm
             | Search [String] PTerm
             | CaseSplitAt Bool Int Name
             | AddClauseFrom Bool Int Name
             | AddProofClauseFrom Bool Int Name
             | AddMissing Bool Int Name
             | MakeWith Bool Int Name
             | MakeLemma Bool Int Name
             | DoProofSearch Bool Bool Int Name [Name]
               -- ^ the first bool is whether to update,
               -- the second is whether to search recursively (i.e. for the arguments)
             | SetOpt Opt
             | UnsetOpt Opt
             | NOP
             | SetColour ColourType IdrisColour
             | ColourOn
             | ColourOff
             | ListErrorHandlers
             | SetConsoleWidth ConsoleWidth
             | Apropos [String] String
             | WhoCalls Name
             | CallsWho Name
             | MakeDoc String                      -- IdrisDoc
             | Warranty
             | PrintDef Name
             | PPrint OutputFmt Int PTerm
             | TransformInfo Name
             -- Debugging commands
             | DebugInfo Name
             | DebugUnify PTerm PTerm

data OutputFmt = HTMLOutput | LaTeXOutput

data Opt = Filename String
         | Quiet
         | NoBanner
         | ColourREPL Bool
         | Idemode
         | IdemodeSocket
         | ShowLibs
         | ShowLibdir
         | ShowIncs
         | ShowPkgs
         | NoBasePkgs
         | NoPrelude
         | NoBuiltins -- only for the really primitive stuff!
         | NoREPL
         | OLogging Int
         | Output String
         | TypeCase
         | TypeInType
         | DefaultTotal
         | DefaultPartial
         | WarnPartial
         | WarnReach
         | NoCoverage
         | ErrContext
         | ShowImpl
         | Verbose
         | Port String         -- REPL TCP port
         | IBCSubDir String
         | ImportDir String
         | PkgBuild String
         | PkgInstall String
         | PkgClean String
         | PkgCheck String
         | PkgREPL String
         | PkgMkDoc String     -- IdrisDoc
         | PkgTest String
         | PkgIndex FilePath
         | WarnOnly
         | Pkg String
         | BCAsm String
         | DumpDefun String
         | DumpCases String
         | UseCodegen Codegen
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
         | AutoSolve -- ^ Automatically issue "solve" tactic in interactive prover
    deriving (Show, Eq)

-- Parsed declarations

data Fixity = Infixl { prec :: Int }
            | Infixr { prec :: Int }
            | InfixN { prec :: Int }
            | PrefixN { prec :: Int }
    deriving Eq
{-!
deriving instance Binary Fixity
deriving instance NFData Fixity
!-}

instance Show Fixity where
    show (Infixl i) = "infixl " ++ show i
    show (Infixr i) = "infixr " ++ show i
    show (InfixN i) = "infix " ++ show i
    show (PrefixN i) = "prefix " ++ show i

data FixDecl = Fix Fixity String
    deriving Eq

instance Show FixDecl where
  show (Fix f s) = show f ++ " " ++ s

{-!
deriving instance Binary FixDecl
deriving instance NFData FixDecl
!-}

instance Ord FixDecl where
    compare (Fix x _) (Fix y _) = compare (prec x) (prec y)


data Static = Static | Dynamic
  deriving (Show, Eq, Data, Typeable)
{-!
deriving instance Binary Static
deriving instance NFData Static
!-}

-- Mark bindings with their explicitness, and laziness
data Plicity = Imp { pargopts :: [ArgOpt],
                     pstatic :: Static,
                     pparam :: Bool,
                     pscoped :: Maybe ImplicitInfo -- Nothing, if top level
                   }
             | Exp { pargopts :: [ArgOpt],
                     pstatic :: Static,
                     pparam :: Bool }   -- this is a param (rather than index)
             | Constraint { pargopts :: [ArgOpt],
                            pstatic :: Static }
             | TacImp { pargopts :: [ArgOpt],
                        pstatic :: Static,
                        pscript :: PTerm }
  deriving (Show, Eq, Data, Typeable)

{-!
deriving instance Binary Plicity
deriving instance NFData Plicity
!-}

is_scoped :: Plicity -> Maybe ImplicitInfo
is_scoped (Imp _ _ _ s) = s
is_scoped _ = Nothing

impl = Imp [] Dynamic False Nothing
forall_imp = Imp [] Dynamic False (Just (Impl False))
forall_constraint = Imp [] Dynamic False (Just (Impl True))
expl = Exp [] Dynamic False
expl_param = Exp [] Dynamic True
constraint = Constraint [] Static
tacimpl t = TacImp [] Dynamic t

data FnOpt = Inlinable -- always evaluate when simplifying
           | TotalFn | PartialFn | CoveringFn
           | Coinductive | AssertTotal
           | Dictionary -- type class dictionary, eval only when
                        -- a function argument, and further evaluation resutls
           | Implicit -- implicit coercion
           | NoImplicit -- do not apply implicit coercions
           | CExport String    -- export, with a C name
           | ErrorHandler     -- ^^ an error handler for use with the ErrorReflection extension
           | ErrorReverse     -- ^^ attempt to reverse normalise before showing in error
           | Reflection -- a reflecting function, compile-time only
           | Specialise [(Name, Maybe Int)] -- specialise it, freeze these names
           | Constructor -- Data constructor type
    deriving (Show, Eq)
{-!
deriving instance Binary FnOpt
deriving instance NFData FnOpt
!-}

type FnOpts = [FnOpt]

inlinable :: FnOpts -> Bool
inlinable = elem Inlinable

dictionary :: FnOpts -> Bool
dictionary = elem Dictionary


-- | Data declaration options
data DataOpt = Codata -- ^ Set if the the data-type is coinductive
             | DefaultEliminator -- ^ Set if an eliminator should be generated for data type
             | DefaultCaseFun -- ^ Set if a case function should be generated for data type
             | DataErrRev
    deriving (Show, Eq)

type DataOpts = [DataOpt]

-- | Type provider - what to provide
data ProvideWhat' t = ProvTerm t t     -- ^ the first is the goal type, the second is the term
                    | ProvPostulate t  -- ^ goal type must be Type, so only term
    deriving (Show, Eq, Functor)

type ProvideWhat = ProvideWhat' PTerm

-- | Top-level declarations such as compiler directives, definitions,
-- datatypes and typeclasses.
data PDecl' t
   = PFix     FC Fixity [String] -- ^ Fixity declaration
   | PTy      (Docstring (Either Err PTerm)) [(Name, Docstring (Either Err PTerm))] SyntaxInfo FC FnOpts Name t   -- ^ Type declaration
   | PPostulate (Docstring (Either Err PTerm)) SyntaxInfo FC FnOpts Name t -- ^ Postulate
   | PClauses FC FnOpts Name [PClause' t]   -- ^ Pattern clause
   | PCAF     FC Name t -- ^ Top level constant
   | PData    (Docstring (Either Err PTerm)) [(Name, Docstring (Either Err PTerm))] SyntaxInfo FC DataOpts (PData' t)  -- ^ Data declaration.
   | PParams  FC [(Name, t)] [PDecl' t] -- ^ Params block
   | PNamespace String [PDecl' t] -- ^ New namespace
   | PRecord  (Docstring (Either Err PTerm)) SyntaxInfo FC Name t DataOpts (Docstring (Either Err PTerm)) Name t  -- ^ Record declaration
   | PClass   (Docstring (Either Err PTerm)) SyntaxInfo FC
              [(Name, t)] -- constraints
              Name
              [(Name, t)] -- parameters
              [(Name, Docstring (Either Err PTerm))] -- parameter docstrings
              [PDecl' t] -- declarations
              -- ^ Type class: arguments are documentation, syntax info, source location, constraints,
              -- class name, parameters, method declarations
   | PInstance SyntaxInfo FC [(Name, t)] -- constraints
                             Name -- class
                             [t] -- parameters
                             t -- full instance type
                             (Maybe Name) -- explicit name
                             [PDecl' t]
               -- ^ Instance declaration: arguments are syntax info, source location, constraints,
               -- class name, parameters, full instance type, optional explicit name, and definitions
   | PDSL     Name (DSL' t) -- ^ DSL declaration
   | PSyntax  FC Syntax -- ^ Syntax definition
   | PMutual  FC [PDecl' t] -- ^ Mutual block
   | PDirective (Idris ()) -- ^ Compiler directive. The parser inserts the corresponding action in the Idris monad.
   | PProvider SyntaxInfo FC (ProvideWhat' t) Name -- ^ Type provider. The first t is the type, the second is the term
   | PTransform FC Bool t t -- ^ Source-to-source transformation rule. If
                            -- bool is True, lhs and rhs must be convertible
 deriving Functor
{-!
deriving instance Binary PDecl'
deriving instance NFData PDecl'
!-}

-- For elaborator state
data EState = EState {
                  case_decls :: [PDecl],
                  delayed_elab :: [Elab' EState ()]
              }

initEState = EState [] []

type ElabD a = Elab' EState a

-- | One clause of a top-level definition. Term arguments to constructors are:
--
-- 1. The whole application (missing for PClauseR and PWithR because they're within a "with" clause)
--
-- 2. The list of extra 'with' patterns
--
-- 3. The right-hand side
--
-- 4. The where block (PDecl' t)

data PClause' t = PClause  FC Name t [t] t              [PDecl' t] -- ^ A normal top-level definition.
                | PWith    FC Name t [t] t (Maybe Name) [PDecl' t]
                | PClauseR FC        [t] t              [PDecl' t]
                | PWithR   FC        [t] t (Maybe Name) [PDecl' t]
    deriving Functor
{-!
deriving instance Binary PClause'
deriving instance NFData PClause'
!-}

-- | Data declaration
data PData' t  = PDatadecl { d_name :: Name, -- ^ The name of the datatype
                             d_tcon :: t, -- ^ Type constructor
                             d_cons :: [(Docstring (Either Err PTerm), [(Name, Docstring (Either Err PTerm))], Name, t, FC, [Name])] -- ^ Constructors
                           }
                 -- ^ Data declaration
               | PLaterdecl { d_name :: Name, d_tcon :: t }
                 -- ^ "Placeholder" for data whose constructors are defined later
    deriving Functor
{-!
deriving instance Binary PData'
deriving instance NFData PData'
!-}

-- Handy to get a free function for applying PTerm -> PTerm functions
-- across a program, by deriving Functor

type PDecl   = PDecl' PTerm
type PData   = PData' PTerm
type PClause = PClause' PTerm

-- get all the names declared in a decl

declared :: PDecl -> [Name]
declared (PFix _ _ _) = []
declared (PTy _ _ _ _ _ n t) = [n]
declared (PPostulate _ _ _ _ n t) = [n]
declared (PClauses _ _ n _) = [] -- not a declaration
declared (PCAF _ n _) = [n]
declared (PData _ _ _ _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (_, _, a, _, _, _) = a
declared (PData _ _ _ _ _ (PLaterdecl n _)) = [n]
declared (PParams _ _ ds) = concatMap declared ds
declared (PNamespace _ ds) = concatMap declared ds
declared (PRecord _ _ _ n _ _ _ c _) = [n, c]
declared (PClass _ _ _ _ n _ _ ms) = n : concatMap declared ms
declared (PInstance _ _ _ _ _ _ _ _) = []
declared (PDSL n _) = [n]
declared (PSyntax _ _) = []
declared (PMutual _ ds) = concatMap declared ds
declared (PDirective _) = []

-- get the names declared, not counting nested parameter blocks
tldeclared :: PDecl -> [Name]
tldeclared (PFix _ _ _) = []
tldeclared (PTy _ _ _ _ _ n t) = [n]
tldeclared (PPostulate _ _ _ _ n t) = [n]
tldeclared (PClauses _ _ n _) = [] -- not a declaration
tldeclared (PRecord _ _ _ n _ _ _ c _) = [n, c]
tldeclared (PData _ _ _ _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (_, _, a, _, _, _) = a
tldeclared (PParams _ _ ds) = []
tldeclared (PMutual _ ds) = concatMap tldeclared ds
tldeclared (PNamespace _ ds) = concatMap tldeclared ds
tldeclared (PClass _ _ _ _ n _ _ ms) = concatMap tldeclared ms
tldeclared (PInstance _ _ _ _ _ _ _ _) = []
tldeclared _ = []

defined :: PDecl -> [Name]
defined (PFix _ _ _) = []
defined (PTy _ _ _ _ _ n t) = []
defined (PPostulate _ _ _ _ n t) = []
defined (PClauses _ _ n _) = [n] -- not a declaration
defined (PCAF _ n _) = [n]
defined (PData _ _ _ _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (_, _, a, _, _, _) = a
defined (PData _ _ _ _ _ (PLaterdecl n _)) = []
defined (PParams _ _ ds) = concatMap defined ds
defined (PNamespace _ ds) = concatMap defined ds
defined (PRecord _ _ _ n _ _ _ c _) = [n, c]
defined (PClass _ _ _ _ n _ _ ms) = n : concatMap defined ms
defined (PInstance _ _ _ _ _ _ _ _) = []
defined (PDSL n _) = [n]
defined (PSyntax _ _) = []
defined (PMutual _ ds) = concatMap defined ds
defined (PDirective _) = []
--defined _ = []

updateN :: [(Name, Name)] -> Name -> Name
updateN ns n | Just n' <- lookup n ns = n'
updateN _  n = n

updateNs :: [(Name, Name)] -> PTerm -> PTerm
updateNs [] t = t
updateNs ns t = mapPT updateRef t
  where updateRef (PRef fc f) = PRef fc (updateN ns f)
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

data PunInfo = IsType | IsTerm | TypeOrTerm deriving (Eq, Show, Data, Typeable)

-- | High level language terms
data PTerm = PQuote Raw -- ^ Inclusion of a core term into the high-level language
           | PRef FC Name -- ^ A reference to a variable
           | PInferRef FC Name -- ^ A name to be defined later
           | PPatvar FC Name -- ^ A pattern variable
           | PLam FC Name PTerm PTerm -- ^ A lambda abstraction
           | PPi  Plicity Name PTerm PTerm -- ^ (n : t1) -> t2
           | PLet FC Name PTerm PTerm PTerm -- ^ A let binding
           | PTyped PTerm PTerm -- ^ Term with explicit type
           | PApp FC PTerm [PArg] -- ^ e.g. IO (), List Char, length x
           | PAppImpl PTerm [ImplicitInfo] -- ^ Implicit argument application (introduced during elaboration only)
           | PAppBind FC PTerm [PArg] -- ^ implicitly bound application
           | PMatchApp FC Name -- ^ Make an application by type matching
           | PCase FC PTerm [(PTerm, PTerm)] -- ^ A case expression. Args are source location, scrutinee, and a list of pattern/RHS pairs
           | PTrue FC PunInfo -- ^ Unit type..?
           | PRefl FC PTerm -- ^ The canonical proof of the equality type
           | PResolveTC FC -- ^ Solve this dictionary by type class resolution
           | PEq FC PTerm PTerm PTerm PTerm -- ^ Heterogeneous equality type: A = B
           | PRewrite FC PTerm PTerm (Maybe PTerm) -- ^ "rewrite" syntax, with optional result type
           | PPair FC PunInfo PTerm PTerm -- ^ A pair (a, b) and whether it's a product type or a pair (solved by elaboration)
           | PDPair FC PunInfo PTerm PTerm PTerm -- ^ A dependent pair (tm : a ** b) and whether it's a sigma type or a pair that inhabits one (solved by elaboration)
           | PAs FC Name PTerm -- ^ @-pattern, valid LHS only
           | PAlternative Bool [PTerm] -- ^ True if only one may work. (| A, B, C|)
           | PHidden PTerm -- ^ Irrelevant or hidden pattern
           | PType -- ^ 'Type' type
           | PUniverse Universe -- ^ Some universe 
           | PGoal FC PTerm Name PTerm -- ^ quoteGoal, used for %reflection functions
           | PConstant Const -- ^ Builtin types
           | Placeholder -- ^ Underscore
           | PDoBlock [PDo] -- ^ Do notation
           | PIdiom FC PTerm -- ^ Idiom brackets
           | PReturn FC
           | PMetavar Name -- ^ A metavariable, ?name
           | PProof [PTactic] -- ^ Proof script
           | PTactics [PTactic] -- ^ As PProof, but no auto solving
           | PElabError Err -- ^ Error to report on elaboration
           | PImpossible -- ^ Special case for declaring when an LHS can't typecheck
           | PCoerced PTerm -- ^ To mark a coerced argument, so as not to coerce twice
           | PDisamb [[T.Text]] PTerm -- ^ Preferences for explicit namespaces
           | PUnifyLog PTerm -- ^ dump a trace of unifications when building term
           | PNoImplicits PTerm -- ^ never run implicit converions on the term
           | PQuasiquote PTerm (Maybe PTerm) -- ^ `(Term [: Term])
           | PUnquote PTerm -- ^ ~Term
           | PRunTactics PTerm -- ^ %run_tactics tm - New-style proof script
       deriving (Eq, Data, Typeable)


{-!
deriving instance Binary PTerm
deriving instance NFData PTerm
!-}

mapPT :: (PTerm -> PTerm) -> PTerm -> PTerm
mapPT f t = f (mpt t) where
  mpt (PLam fc n t s) = PLam fc n (mapPT f t) (mapPT f s)
  mpt (PPi p n t s) = PPi p n (mapPT f t) (mapPT f s)
  mpt (PLet fc n ty v s) = PLet fc n (mapPT f ty) (mapPT f v) (mapPT f s)
  mpt (PRewrite fc t s g) = PRewrite fc (mapPT f t) (mapPT f s)
                                 (fmap (mapPT f) g)
  mpt (PApp fc t as) = PApp fc (mapPT f t) (map (fmap (mapPT f)) as)
  mpt (PAppBind fc t as) = PAppBind fc (mapPT f t) (map (fmap (mapPT f)) as)
  mpt (PCase fc c os) = PCase fc (mapPT f c) (map (pmap (mapPT f)) os)
  mpt (PEq fc lt rt l r) = PEq fc (mapPT f lt) (mapPT f rt) (mapPT f l) (mapPT f r)
  mpt (PTyped l r) = PTyped (mapPT f l) (mapPT f r)
  mpt (PPair fc p l r) = PPair fc p (mapPT f l) (mapPT f r)
  mpt (PDPair fc p l t r) = PDPair fc p (mapPT f l) (mapPT f t) (mapPT f r)
  mpt (PAlternative a as) = PAlternative a (map (mapPT f) as)
  mpt (PHidden t) = PHidden (mapPT f t)
  mpt (PDoBlock ds) = PDoBlock (map (fmap (mapPT f)) ds)
  mpt (PProof ts) = PProof (map (fmap (mapPT f)) ts)
  mpt (PTactics ts) = PTactics (map (fmap (mapPT f)) ts)
  mpt (PUnifyLog tm) = PUnifyLog (mapPT f tm)
  mpt (PDisamb ns tm) = PDisamb ns (mapPT f tm)
  mpt (PNoImplicits tm) = PNoImplicits (mapPT f tm)
  mpt (PGoal fc r n sc) = PGoal fc (mapPT f r) n (mapPT f sc)
  mpt x = x


data PTactic' t = Intro [Name] | Intros | Focus Name
                | Refine Name [Bool] | Rewrite t | DoUnify
                | Induction t
                | CaseTac t
                | Equiv t
                | Claim Name t
                | Unfocus
                | MatchRefine Name
                | LetTac Name t | LetTacTy Name t t
                | Exact t | Compute | Trivial | TCInstance
                | ProofSearch Bool Bool Int (Maybe Name) [Name]
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
    deriving (Show, Eq, Functor, Foldable, Traversable, Data, Typeable)
{-!
deriving instance Binary PTactic'
deriving instance NFData PTactic'
!-}
instance Sized a => Sized (PTactic' a) where
  size (Intro nms) = 1 + size nms
  size Intros = 1
  size (Focus nm) = 1 + size nm
  size (Refine nm bs) = 1 + size nm + length bs
  size (Rewrite t) = 1 + size t
  size (Induction t) = 1 + size t
  size (LetTac nm t) = 1 + size nm + size t
  size (Exact t) = 1 + size t
  size Compute = 1
  size Trivial = 1
  size Solve = 1
  size Attack = 1
  size ProofState = 1
  size ProofTerm = 1
  size Undo = 1
  size (Try l r) = 1 + size l + size r
  size (TSeq l r) = 1 + size l + size r
  size (ApplyTactic t) = 1 + size t
  size (Reflect t) = 1 + size t
  size (Fill t) = 1 + size t
  size Qed = 1
  size Abandon = 1
  size Skip = 1
  size (TFail ts) = 1 + size ts
  size SourceFC = 1

type PTactic = PTactic' PTerm

data PDo' t = DoExp  FC t
            | DoBind FC Name t
            | DoBindP FC t t [(t,t)]
            | DoLet  FC Name t t
            | DoLetP FC t t
    deriving (Eq, Functor, Data, Typeable)
{-!
deriving instance Binary PDo'
deriving instance NFData PDo'
!-}

instance Sized a => Sized (PDo' a) where
  size (DoExp fc t) = 1 + size fc + size t
  size (DoBind fc nm t) = 1 + size fc + size nm + size t
  size (DoBindP fc l r alts) = 1 + size fc + size l + size r + size alts
  size (DoLet fc nm l r) = 1 + size fc + size nm + size l + size r
  size (DoLetP fc l r) = 1 + size fc + size l + size r

type PDo = PDo' PTerm

-- The priority gives a hint as to elaboration order. Best to elaborate
-- things early which will help give a more concrete type to other
-- variables, e.g. a before (interpTy a).

data PArg' t = PImp { priority :: Int,
                      machine_inf :: Bool, -- true if the machine inferred it
                      argopts :: [ArgOpt],
                      pname :: Name, getTm :: t }
             | PExp { priority :: Int,
                      argopts :: [ArgOpt],
                      pname :: Name,
                      getTm :: t }
             | PConstraint { priority :: Int,
                             argopts :: [ArgOpt],
                             pname :: Name,
                             getTm :: t }
             | PTacImplicit { priority :: Int,
                              argopts :: [ArgOpt],
                              pname :: Name,
                              getScript :: t,
                              getTm :: t }
    deriving (Show, Eq, Functor, Data, Typeable)

data ArgOpt = AlwaysShow | HideDisplay | InaccessibleArg
    deriving (Show, Eq, Data, Typeable)

instance Sized a => Sized (PArg' a) where
  size (PImp p _ l nm trm) = 1 + size nm + size trm
  size (PExp p l nm trm) = 1 + size nm + size trm
  size (PConstraint p l nm trm) = 1 + size nm +size nm +  size trm
  size (PTacImplicit p l nm scr trm) = 1 + size nm + size scr + size trm

{-!
deriving instance Binary PArg'
deriving instance NFData PArg'
!-}

pimp n t mach = PImp 1 mach [] n t
pexp t = PExp 1 [] (sMN 0 "arg") t
pconst t = PConstraint 1 [] (sMN 0 "carg") t
ptacimp n s t = PTacImplicit 2 [] n s t

type PArg = PArg' PTerm

-- | Get the highest FC in a term, if one exists
highestFC :: PTerm -> Maybe FC
highestFC (PQuote _) = Nothing
highestFC (PRef fc _) = Just fc
highestFC (PInferRef fc _) = Just fc
highestFC (PPatvar fc _) = Just fc
highestFC (PLam fc _ _ _) = Just fc
highestFC (PPi  _ _ _ _) = Nothing
highestFC (PLet fc _ _ _ _) = Just fc
highestFC (PTyped tm ty) = highestFC tm <|> highestFC ty
highestFC (PApp fc _ _) = Just fc
highestFC (PAppBind fc _ _) = Just fc
highestFC (PMatchApp fc _) = Just fc
highestFC (PCase fc _ _) = Just fc
highestFC (PTrue fc _) = Just fc
highestFC (PRefl fc _) = Just fc
highestFC (PResolveTC fc) = Just fc
highestFC (PEq fc _ _ _ _) = Just fc
highestFC (PRewrite fc _ _ _) = Just fc
highestFC (PPair fc _ _ _) = Just fc
highestFC (PDPair fc _ _ _ _) = Just fc
highestFC (PAs fc _ _) = Just fc
highestFC (PAlternative _ args) =
  case mapMaybe highestFC args of
    [] -> Nothing
    (fc:_) -> Just fc
highestFC (PHidden _) = Nothing
highestFC PType = Nothing
highestFC (PUniverse _) = Nothing
highestFC (PGoal fc _ _ _) = Just fc
highestFC (PConstant _) = Nothing
highestFC Placeholder = Nothing
highestFC (PDoBlock lines) =
  case map getDoFC lines of
    [] -> Nothing
    (fc:_) -> Just fc
  where
    getDoFC (DoExp fc t)          = fc
    getDoFC (DoBind fc nm t)      = fc
    getDoFC (DoBindP fc l r alts) = fc
    getDoFC (DoLet fc nm l r)     = fc
    getDoFC (DoLetP fc l r)       = fc

highestFC (PIdiom fc _) = Just fc
highestFC (PReturn fc) = Just fc
highestFC (PMetavar _) = Nothing
highestFC (PProof _) = Nothing
highestFC (PTactics _) = Nothing
highestFC (PElabError _) = Nothing
highestFC PImpossible = Nothing
highestFC (PCoerced tm) = highestFC tm
highestFC (PDisamb _ opts) = highestFC opts
highestFC (PUnifyLog tm) = highestFC tm
highestFC (PNoImplicits tm) = highestFC tm
highestFC (PQuasiquote _ _) = Nothing
highestFC (PUnquote tm) = highestFC tm

-- Type class data

data ClassInfo = CI { instanceName :: Name,
                      class_methods :: [(Name, (FnOpts, PTerm))],
                      class_defaults :: [(Name, (Name, PDecl))], -- method name -> default impl
                      class_default_superclasses :: [PDecl],
                      class_params :: [Name],
                      class_instances :: [Name] }
    deriving Show
{-!
deriving instance Binary ClassInfo
deriving instance NFData ClassInfo
!-}

-- Type inference data

data TIData = TIPartial -- ^ a function with a partially defined type
            | TISolution [Term] -- ^ possible solutions to a metavariable in a type
    deriving Show

-- | Miscellaneous information about functions
data FnInfo = FnInfo { fn_params :: [Int] }
    deriving Show
{-!
deriving instance Binary FnInfo
deriving instance NFData FnInfo
!-}

data OptInfo = Optimise { inaccessible :: [(Int,Name)],  -- includes names for error reporting
                          detaggable :: Bool }
    deriving Show
{-!
deriving instance Binary OptInfo
deriving instance NFData OptInfo
!-}


data TypeInfo = TI { con_names :: [Name],
                     codata :: Bool,
                     data_opts :: DataOpts,
                     param_pos :: [Int],
                     mutual_types :: [Name] }
    deriving Show
{-!
deriving instance Binary TypeInfo
deriving instance NFData TypeInfo
!-}

-- Syntactic sugar info

data DSL' t = DSL { dsl_bind    :: t,
                    dsl_return  :: t,
                    dsl_apply   :: t,
                    dsl_pure    :: t,
                    dsl_var     :: Maybe t,
                    index_first :: Maybe t,
                    index_next  :: Maybe t,
                    dsl_lambda  :: Maybe t,
                    dsl_let     :: Maybe t,
                    dsl_pi      :: Maybe t
                  }
    deriving (Show, Functor)
{-!
deriving instance Binary DSL'
deriving instance NFData DSL'
!-}

type DSL = DSL' PTerm

data SynContext = PatternSyntax | TermSyntax | AnySyntax
    deriving Show
{-!
deriving instance Binary SynContext
deriving instance NFData SynContext
!-}

data Syntax = Rule [SSymbol] PTerm SynContext
    deriving Show

syntaxNames :: Syntax -> [Name]
syntaxNames (Rule syms _ _) = mapMaybe ename syms
           where ename (Keyword n) = Just n
                 ename _           = Nothing

syntaxSymbols :: Syntax -> [SSymbol]
syntaxSymbols (Rule ss _ _) = ss
{-!
deriving instance Binary Syntax
deriving instance NFData Syntax
!-}

data SSymbol = Keyword Name
             | Symbol String
             | Binding Name
             | Expr Name
             | SimpleExpr Name
    deriving (Show, Eq)
    

{-!
deriving instance Binary SSymbol
deriving instance NFData SSymbol
!-}

newtype SyntaxRules = SyntaxRules { syntaxRulesList :: [Syntax] }

emptySyntaxRules :: SyntaxRules
emptySyntaxRules = SyntaxRules []

updateSyntaxRules :: [Syntax] -> SyntaxRules -> SyntaxRules
updateSyntaxRules rules (SyntaxRules sr) = SyntaxRules newRules
  where
    newRules = sortBy (ruleSort `on` syntaxSymbols) (rules ++ sr)

    ruleSort [] [] = EQ
    ruleSort [] _ = LT
    ruleSort _ [] = GT
    ruleSort (s1:ss1) (s2:ss2) =
      case symCompare s1 s2 of
        EQ -> ruleSort ss1 ss2
        r -> r

    -- Better than creating Ord instance for SSymbol since
    -- in general this ordering does not really make sense.
    symCompare (Keyword n1) (Keyword n2) = compare n1 n2
    symCompare (Keyword _) _ = LT
    symCompare (Symbol _) (Keyword _) = GT
    symCompare (Symbol s1) (Symbol s2) = compare s1 s2
    symCompare (Symbol _) _ = LT
    symCompare (Binding _) (Keyword _) = GT
    symCompare (Binding _) (Symbol _) = GT
    symCompare (Binding b1) (Binding b2) = compare b1 b2
    symCompare (Binding _) _ = LT
    symCompare (Expr _) (Keyword _) = GT
    symCompare (Expr _) (Symbol _) = GT
    symCompare (Expr _) (Binding _) = GT
    symCompare (Expr e1) (Expr e2) = compare e1 e2
    symCompare (Expr _) _ = LT
    symCompare (SimpleExpr _) (Keyword _) = GT
    symCompare (SimpleExpr _) (Symbol _) = GT
    symCompare (SimpleExpr _) (Binding _) = GT
    symCompare (SimpleExpr _) (Expr _) = GT
    symCompare (SimpleExpr e1) (SimpleExpr e2) = compare e1 e2

initDSL = DSL (PRef f (sUN ">>="))
              (PRef f (sUN "return"))
              (PRef f (sUN "<$>"))
              (PRef f (sUN "pure"))
              Nothing
              Nothing
              Nothing
              Nothing
              Nothing
              Nothing
  where f = fileFC "(builtin)"

data Using = UImplicit Name PTerm
           | UConstraint Name [Name]
    deriving (Show, Eq)
{-!
deriving instance Binary Using
deriving instance NFData Using
!-}

data SyntaxInfo = Syn { using :: [Using],
                        syn_params :: [(Name, PTerm)],
                        syn_namespace :: [String],
                        no_imp :: [Name],
                        decoration :: Name -> Name,
                        inPattern :: Bool,
                        implicitAllowed :: Bool,
                        maxline :: Maybe Int,
                        mut_nesting :: Int,
                        dsl_info :: DSL,
                        syn_in_quasiquote :: Int }
    deriving Show
{-!
deriving instance NFData SyntaxInfo
deriving instance Binary SyntaxInfo
!-}

defaultSyntax = Syn [] [] [] [] id False False Nothing 0 initDSL 0

expandNS :: SyntaxInfo -> Name -> Name
expandNS syn n@(NS _ _) = n
expandNS syn n = case syn_namespace syn of
                        [] -> n
                        xs -> sNS n xs


-- For inferring types of things

bi = fileFC "builtin"

inferTy   = sMN 0 "__Infer"
inferCon  = sMN 0 "__infer"
inferDecl = PDatadecl inferTy
                      PType
                      [(emptyDocstring, [], inferCon, PPi impl (sMN 0 "iType") PType (
                                                   PPi expl (sMN 0 "ival") (PRef bi (sMN 0 "iType"))
                                                   (PRef bi inferTy)), bi, [])]
inferOpts = []

infTerm t = PApp bi (PRef bi inferCon) [pimp (sMN 0 "iType") Placeholder True, pexp t]
infP = P (TCon 6 0) inferTy (TType (UVal 0))

getInferTerm, getInferType :: Term -> Term
getInferTerm (Bind n b sc) = Bind n b $ getInferTerm sc
getInferTerm (App (App _ _) tm) = tm
getInferTerm tm = tm -- error ("getInferTerm " ++ show tm)

getInferType (Bind n b sc) = Bind n (toTy b) $ getInferType sc
  where toTy (Lam t) = Pi Nothing t (TType (UVar 0))
        toTy (PVar t) = PVTy t
        toTy b = b
getInferType (App (App _ ty) _) = ty



-- Handy primitives: Unit, False, Pair, MkPair, =, mkForeign

primNames = [eqTy, eqCon, inferTy, inferCon]

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

eqTy = sUN "="
eqCon = sUN "Refl"
eqDoc =  fmap (const (Left $ Msg "")) . parseDocstring . T.pack $
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

eqDecl = PDatadecl eqTy (piBindp impl [(n "A", PType), (n "B", PType)]
                                 (piBind [(n "x", PRef bi (n "A")), (n "y", PRef bi (n "B"))]
                                 PType))
                [(reflDoc, reflParamDoc,
                  eqCon, PPi impl (n "A") PType (
                                  PPi impl (n "x") (PRef bi (n "A"))
                                      (PApp bi (PRef bi eqTy) [pimp (n "A") Placeholder False,
                                                               pimp (n "B") Placeholder False,
                                                               pexp (PRef bi (n "x")),
                                                               pexp (PRef bi (n "x"))])), bi, [])]
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
sigmaTy   = sNS (sUN "Sigma") ["Builtins"]
existsCon = sNS (sUN "MkSigma") ["Builtins"]

piBind :: [(Name, PTerm)] -> PTerm -> PTerm
piBind = piBindp expl

piBindp :: Plicity -> [(Name, PTerm)] -> PTerm -> PTerm
piBindp p [] t = t
piBindp p ((n, ty):ns) t = PPi p n ty (piBindp p ns t)


-- Pretty-printing declarations and terms

-- These "show" instances render to an absurdly wide screen because inserted line breaks
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

-- | Colourise annotations according to an Idris state. It ignores the names
-- in the annotation, as there's no good way to show extended information on a
-- terminal.
consoleDecorate :: IState -> OutputAnnotation -> String -> String
consoleDecorate ist _ | not (idris_colourRepl ist) = id
consoleDecorate ist (AnnConst c) = let theme = idris_colourTheme ist
                                   in if constIsType c
                                        then colouriseType theme
                                        else colouriseData theme
consoleDecorate ist (AnnData _ _) = colouriseData (idris_colourTheme ist)
consoleDecorate ist (AnnType _ _) = colouriseType (idris_colourTheme ist)
consoleDecorate ist (AnnBoundName _ True) = colouriseImplicit (idris_colourTheme ist)
consoleDecorate ist (AnnBoundName _ False) = colouriseBound (idris_colourTheme ist)
consoleDecorate ist AnnKeyword = colouriseKeyword (idris_colourTheme ist)
consoleDecorate ist (AnnName n _ _ _) = let ctxt  = tt_ctxt ist
                                            theme = idris_colourTheme ist
                                        in case () of
                                             _ | isDConName n ctxt     -> colouriseData theme
                                             _ | isFnName n ctxt       -> colouriseFun theme
                                             _ | isTConName n ctxt     -> colouriseType theme
                                             _ | isPostulateName n ist -> colourisePostulate theme
                                             _ | otherwise             -> id -- don't colourise unknown names
consoleDecorate ist (AnnFC _) = id
consoleDecorate ist (AnnTextFmt fmt) = Idris.Colours.colourise (colour fmt)
  where colour BoldText      = IdrisColour Nothing True False True False
        colour UnderlineText = IdrisColour Nothing True True False False
        colour ItalicText    = IdrisColour Nothing True False False True
consoleDecorate ist (AnnTerm _ _) = id
consoleDecorate ist (AnnSearchResult _) = id
consoleDecorate ist (AnnErr _) = id

isPostulateName :: Name -> IState -> Bool
isPostulateName n ist = S.member n (idris_postulates ist)

-- | Pretty-print a high-level closed Idris term with no information about precedence/associativity
prettyImp :: PPOption -- ^^ pretty printing options
          -> PTerm -- ^^ the term to pretty-print
          -> Doc OutputAnnotation
prettyImp impl = pprintPTerm impl [] [] []

-- | Serialise something to base64 using its Binary instance.

-- | Do the right thing for rendering a term in an IState
prettyIst ::  IState -> PTerm -> Doc OutputAnnotation
prettyIst ist = pprintPTerm (ppOptionIst ist) [] [] (idris_infixes ist)

-- | Pretty-print a high-level Idris term in some bindings context with infix info
pprintPTerm :: PPOption -- ^^ pretty printing options
            -> [(Name, Bool)] -- ^^ the currently-bound names and whether they are implicit
            -> [Name] -- ^^ names to always show in pi, even if not used
            -> [FixDecl] -- ^^ Fixity declarations
            -> PTerm -- ^^ the term to pretty-print
            -> Doc OutputAnnotation
pprintPTerm ppo bnd docArgs infixes = prettySe startPrec bnd
  where
    startPrec = 0
    funcAppPrec = 10
    
    prettySe :: Int -> [(Name, Bool)] -> PTerm -> Doc OutputAnnotation
    prettySe p bnd (PQuote r) =
        text "![" <> pretty r <> text "]"
    prettySe p bnd (PPatvar fc n) = pretty n
    prettySe p bnd e
      | Just str <- slist p bnd e = str
      | Just n <- snat p e = annotate (AnnData "Nat" "") (text (show n))
    prettySe p bnd (PRef fc n) = prettyName True (ppopt_impl ppo) bnd n
    prettySe p bnd (PLam fc n ty sc) =
      bracket p startPrec . group . align . hang 2 $
      text "\\" <> bindingOf n False <+> text "=>" <$>
      prettySe startPrec ((n, False):bnd) sc
    prettySe p bnd (PLet fc n ty v sc) =
      bracket p startPrec . group . align $
      kwd "let" <+> (group . align . hang 2 $ bindingOf n False <+> text "=" <$> prettySe startPrec bnd v) </>
      kwd "in" <+> (group . align . hang 2 $ prettySe startPrec ((n, False):bnd) sc)
    prettySe p bnd (PPi (Exp l s _) n ty sc)
      | n `elem` allNamesIn sc || ppopt_impl ppo || n `elem` docArgs =
          bracket p startPrec . group $
          enclose lparen rparen (group . align $ bindingOf n False <+> colon <+> prettySe startPrec bnd ty) <+>
          st <> text "->" <$> prettySe startPrec ((n, False):bnd) sc
      | otherwise                      =
          bracket p startPrec . group $
          group (prettySe (startPrec + 1) bnd ty <+> st) <> text "->" <$> group (prettySe startPrec ((n, False):bnd) sc)
      where
        st =
          case s of
            Static -> text "[static]" <> space
            _      -> empty
    prettySe p bnd (PPi (Imp l s _ fa) n ty sc)
      | ppopt_impl ppo =
          bracket p startPrec $
          lbrace <> bindingOf n True <+> colon <+> prettySe startPrec bnd ty <> rbrace <+>
          st <> text "->" </> prettySe startPrec ((n, True):bnd) sc
      | otherwise = prettySe startPrec ((n, True):bnd) sc
      where
        st =
          case s of
            Static -> text "[static]" <> space
            _      -> empty
    prettySe p bnd (PPi (Constraint _ _) n ty sc) =
      bracket p startPrec $
      prettySe (startPrec + 1) bnd ty <+> text "=>" </> prettySe startPrec ((n, True):bnd) sc
    prettySe p bnd (PPi (TacImp _ _ s) n ty sc) =
      bracket p startPrec $
      lbrace <> kwd "tacimp" <+> pretty n <+> colon <+> prettySe startPrec bnd ty <>
      rbrace <+> text "->" </> prettySe startPrec ((n, True):bnd) sc
    prettySe p bnd (PApp _ (PRef _ f) args) -- normal names, no explicit args
      | UN nm <- basename f
      , not (ppopt_impl ppo) && null (getShowArgs args) =
          prettyName True (ppopt_impl ppo) bnd f
    prettySe p bnd (PAppBind _ (PRef _ f) [])
      | not (ppopt_impl ppo) = text "!" <> prettyName True (ppopt_impl ppo) bnd f
    prettySe p bnd (PApp _ (PRef _ op) args) -- infix operators
      | UN nm <- basename op
      , not (tnull nm) &&
        (not (ppopt_impl ppo)) && (not $ isAlpha (thead nm)) =
          case getShowArgs args of
            [] -> opName True
            [x] -> group (opName True <$> group (prettySe startPrec bnd (getTm x)))
            [l,r] -> let precedence = maybe (startPrec - 1) prec f
                     in bracket p precedence $ inFix (getTm l) (getTm r)
            (l@(PExp _ _ _ _) : r@(PExp _ _ _ _) : rest) -> 
                   bracket p funcAppPrec $
                          enclose lparen rparen (inFix (getTm l) (getTm r)) <+>
                          align (group (vsep (map (prettyArgS bnd) rest)))
            as -> opName True <+> align (vsep (map (prettyArgS bnd) as))
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
                  (prettySe left bnd l <+> opName False) <$> 
                    group (prettySe right bnd r)
    prettySe p bnd (PApp _ hd@(PRef fc f) [tm]) -- symbols, like 'foo
      | PConstant (Idris.Core.TT.Str str) <- getTm tm,
        f == sUN "Symbol_" = annotate (AnnType ("'" ++ str) ("The symbol " ++ str)) $
                               char '\'' <> prettySe startPrec bnd (PRef fc (sUN str))
    prettySe p bnd (PApp _ f as) = -- Normal prefix applications
      let args = getShowArgs as
          fp   = prettySe (startPrec + 1) bnd f
          shownArgs = if ppopt_impl ppo then as else args
      in
        bracket p funcAppPrec . group $
            if null shownArgs
              then fp
              else fp <+> align (vsep (map (prettyArgS bnd) shownArgs))
    prettySe p bnd (PCase _ scr cases) =
      align $ kwd "case" <+> prettySe startPrec bnd scr <+> kwd "of" <$>
      indent 2 (vsep (map ppcase cases))
      where
        ppcase (l, r) = let prettyCase = prettySe startPrec 
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
        noNS _ = True

    prettySe p bnd (PHidden tm) = text "." <> prettySe funcAppPrec bnd tm
    prettySe p bnd (PRefl _ _) = annName eqCon $ text "Refl"
    prettySe p bnd (PResolveTC _) = text "resolvetc"
    prettySe p bnd (PTrue _ IsType) = annName unitTy $ text "()"
    prettySe p bnd (PTrue _ IsTerm) = annName unitCon $ text "()"
    prettySe p bnd (PTrue _ TypeOrTerm) = text "()"
    prettySe p bnd (PEq _ lt rt l r)
      | ppopt_impl ppo =
          bracket p eqPrec $
            enclose lparen rparen eq <+>
            align (group (vsep (map (prettyArgS bnd)
                                    [PImp 0 False [] (sUN "A") lt,
                                     PImp 0 False [] (sUN "B") rt,
                                     PExp 0 [] (sUN "x") l,
                                     PExp 0 [] (sUN "y") r])))
      | otherwise =
          bracket p eqPrec . align . group $
            prettyTerm l <+> eq <$> group (prettyTerm r)
      where eq = annName eqTy (text "=")
            eqPrec = startPrec
            prettyTerm = prettySe (eqPrec + 1) bnd
    prettySe p bnd (PRewrite _ l r _) =
      bracket p startPrec $
      text "rewrite" <+> prettySe (startPrec + 1) bnd l <+> text "in" <+> prettySe startPrec bnd r
    prettySe p bnd (PTyped l r) =
      lparen <> prettySe startPrec bnd l <+> colon <+> prettySe startPrec bnd r <> rparen
    prettySe p bnd pair@(PPair _ pun _ _) -- flatten tuples to the right, like parser
      | Just elts <- pairElts pair = enclose (ann lparen) (ann rparen) .
                                     align . group . vsep . punctuate (ann comma) $
                                     map (prettySe startPrec bnd) elts
        where ann = case pun of
                      TypeOrTerm -> id
                      IsType -> annName pairTy
                      IsTerm -> annName pairCon
    prettySe p bnd (PDPair _ pun l t r) =
      annotated lparen <>
      left <+>
      annotated (text "**") <+>
      prettySe startPrec (addBinding bnd) r <>
      annotated rparen
      where annotated = case pun of
              IsType -> annName sigmaTy
              IsTerm -> annName existsCon
              TypeOrTerm -> id
            (left, addBinding) = case (l, pun) of
              (PRef _ n, IsType) -> (bindingOf n False,        ((n, False) :))
              _ ->                  (prettySe startPrec bnd l, id            )
    prettySe p bnd (PAlternative a as) =
      lparen <> text "|" <> prettyAs <> text "|" <> rparen
        where
          prettyAs =
            foldr (\l -> \r -> l <+> text "," <+> r) empty $ map (prettySe startPrec bnd) as
    prettySe p bnd PType = annotate (AnnType "Type" "The type of types") $ text "Type"
    prettySe p bnd (PUniverse u) = annotate (AnnType (show u) "The type of unique types") $ text (show u) 
    prettySe p bnd (PConstant c) = annotate (AnnConst c) (text (show c))
    -- XXX: add pretty for tactics
    prettySe p bnd (PProof ts) =
      text "proof" <+> lbrace <> nest nestingSize (text . show $ ts) <> rbrace
    prettySe p bnd (PTactics ts) =
      text "tactics" <+> lbrace <> nest nestingSize (text . show $ ts) <> rbrace
    prettySe p bnd (PMetavar n) = text "?" <> pretty n
    prettySe p bnd (PReturn f) = kwd "return"
    prettySe p bnd PImpossible = kwd "impossible"
    prettySe p bnd Placeholder = text "_"
    prettySe p bnd (PDoBlock _) = text "do block pretty not implemented"
    prettySe p bnd (PCoerced t) = prettySe p bnd t
    prettySe p bnd (PElabError s) = pretty s
    -- Quasiquote pprinting ignores bound vars
    prettySe p bnd (PQuasiquote t Nothing) = text "`(" <> prettySe p [] t <> text ")"
    prettySe p bnd (PQuasiquote t (Just g)) = text "`(" <> prettySe p [] t <+> colon <+> prettySe p [] g <> text ")"
    prettySe p bnd (PUnquote t) = text "~" <> prettySe p bnd t

    prettySe p bnd _ = text "missing pretty-printer for term"

    prettyArgS bnd (PImp _ _ _ n tm) = prettyArgSi bnd (n, tm)
    prettyArgS bnd (PExp _ _ _ tm)   = prettyArgSe bnd tm
    prettyArgS bnd (PConstraint _ _ _ tm) = prettyArgSc bnd tm
    prettyArgS bnd (PTacImplicit _ _ n _ tm) = prettyArgSti bnd (n, tm)

    prettyArgSe bnd arg = prettySe (funcAppPrec + 1) bnd arg
    prettyArgSi bnd (n, val) = lbrace <> pretty n <+> text "=" <+> prettySe startPrec bnd val <> rbrace
    prettyArgSc bnd val = lbrace <> lbrace <> prettySe startPrec bnd val <> rbrace <> rbrace
    prettyArgSti bnd (n, val) = lbrace <> kwd "auto" <+> pretty n <+> text "=" <+> prettySe startPrec bnd val <> rbrace

    annName :: Name -> Doc OutputAnnotation -> Doc OutputAnnotation
    annName n = annotate (AnnName n Nothing Nothing Nothing)

    opStr :: Name -> String
    opStr (NS n _) = opStr n
    opStr (UN n) = T.unpack n

    basename :: Name -> Name
    basename (NS n _) = basename n
    basename n = n

    slist' p bnd (PApp _ (PRef _ nil) _)
      | not (ppopt_impl ppo) && nsroot nil == sUN "Nil" = Just []
    slist' p bnd (PRef _ nil)
      | not (ppopt_impl ppo) && nsroot nil == sUN "Nil" = Just []
    slist' p bnd (PApp _ (PRef _ cons) args)
      | nsroot cons == sUN "::",
        (PExp {getTm=tl}):(PExp {getTm=hd}):imps <- reverse args,
        all isImp imps,
        Just tl' <- slist' p bnd tl
      = Just (hd:tl')
      where
        isImp (PImp {}) = True
        isImp _ = False
    slist' _ _ tm = Nothing

    slist p bnd e | Just es <- slist' p bnd e = Just $
      case es of [] -> annotate (AnnData "" "") $ text "[]"
                 [x] -> enclose left right . group $
                        prettySe p bnd x
                 xs -> (enclose left right .
                        align . group . vsep .
                        punctuate comma .
                        map (prettySe p bnd)) xs
      where left  = (annotate (AnnData "" "") (text "["))
            right = (annotate (AnnData "" "") (text "]"))
            comma = (annotate (AnnData "" "") (text ","))
    slist _ _ _ = Nothing

    pairElts :: PTerm -> Maybe [PTerm]
    pairElts (PPair _ _ x y) | Just elts <- pairElts y = Just (x:elts)
                             | otherwise = Just [x, y]
    pairElts _ = Nothing

    natns = "Prelude.Nat."

    snat p (PRef _ z)
      | show z == (natns++"Z") || show z == "Z" = Just 0
    snat p (PApp _ s [PExp {getTm=n}])
      | show s == (natns++"S") || show s == "S",
        Just n' <- snat p n
      = Just $ 1 + n'
    snat _ _ = Nothing

    bracket outer inner doc
      | outer > inner = lparen <> doc <> rparen
      | otherwise     = doc

    kwd = annotate AnnKeyword . text

    fixities :: M.Map String Fixity
    fixities = M.fromList [(s, f) | (Fix f s) <- infixes]

    getFixity :: String -> Maybe Fixity
    getFixity = flip M.lookup fixities

-- | Determine whether a name was the one inserted for a hole or
-- guess by the delaborator
isHoleName :: Name -> Bool
isHoleName (UN n) = n == T.pack "[__]"
isHoleName _      = False

-- | Check whether a PTerm has been delaborated from a Term containing a Hole or Guess
containsHole :: PTerm -> Bool
containsHole pterm = or [isHoleName n | PRef _ n <- take 1000 $ universe pterm]

-- | Pretty-printer helper for the binding site of a name
bindingOf :: Name -- ^^ the bound name
          -> Bool -- ^^ whether the name is implicit
          -> Doc OutputAnnotation
bindingOf n imp = annotate (AnnBoundName n imp) (text (show n))

-- | Pretty-printer helper for names that attaches the correct annotations
prettyName
  :: Bool -- ^^ whether the name should be parenthesised if it is an infix operator
  -> Bool -- ^^ whether to show namespaces
  -> [(Name, Bool)] -- ^^ the current bound variables and whether they are implicit
  -> Name -- ^^ the name to pprint
  -> Doc OutputAnnotation
prettyName infixParen showNS bnd n
    | (MN _ s) <- n, isPrefixOf "_" $ T.unpack s = text "_"
    | (UN n') <- n, T.unpack n' == "_" = text "_"
    | Just imp <- lookup n bnd = annotate (AnnBoundName n imp) fullName
    | otherwise                = annotate (AnnName n Nothing Nothing Nothing) fullName
  where fullName = text nameSpace <> parenthesise (text (baseName n))
        baseName (UN n) = T.unpack n
        baseName (NS n ns) = baseName n
        baseName (MN i s) = T.unpack s
        baseName other = show other
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
    showWs [] = empty
    showWs (x : xs) = text "|" <+> prettyImp ppo x <+> showWs xs
showCImp ppo (PWith _ n l ws r pn w)
 = prettyImp ppo l <+> showWs ws <+> text "with" <+> prettyImp ppo r
                 <+> braces (text (show w))
  where
    showWs [] = empty
    showWs (x : xs) = text "|" <+> prettyImp ppo x <+> showWs xs


showDImp :: PPOption -> PData -> Doc OutputAnnotation
showDImp ppo (PDatadecl n ty cons)
 = text "data" <+> text (show n) <+> colon <+> prettyImp ppo ty <+> text "where" <$>
    (indent 2 $ vsep (map (\ (_, _, n, t, _, _) -> pipe <+> prettyName True False [] n <+> colon <+> prettyImp ppo t) cons))

showDecls :: PPOption -> [PDecl] -> Doc OutputAnnotation
showDecls o ds = vsep (map (showDeclImp o) ds)

showDeclImp _ (PFix _ f ops) = text (show f) <+> cat (punctuate (text ",") (map text ops))
showDeclImp o (PTy _ _ _ _ _ n t) = text "tydecl" <+> text (showCG n) <+> colon <+> prettyImp o t
showDeclImp o (PClauses _ _ n cs) = text "pat" <+> text (showCG n) <+> text "\t" <+>
                                      indent 2 (vsep (map (showCImp o) cs))
showDeclImp o (PData _ _ _ _ _ d) = showDImp o { ppopt_impl = True } d
showDeclImp o (PParams _ ns ps) = text "params" <+> braces (text (show ns) <> line <> showDecls o ps <> line)
showDeclImp o (PNamespace n ps) = text "namespace" <+> text n <> braces (line <> showDecls o ps <> line)
showDeclImp _ (PSyntax _ syn) = text "syntax" <+> text (show syn)
showDeclImp o (PClass _ _ _ cs n ps _ ds)
   = text "class" <+> text (show cs) <+> text (show n) <+> text (show ps) <> line <> showDecls o ds
showDeclImp o (PInstance _ _ cs n _ t _ ds)
   = text "instance" <+> text (show cs) <+> text (show n) <+> prettyImp o t <> line <> showDecls o ds
showDeclImp _ _ = text "..."
-- showDeclImp (PImport o) = "import " ++ o

instance Show (Doc OutputAnnotation) where
  show = flip (displayS . renderCompact) ""

getImps :: [PArg] -> [(Name, PTerm)]
getImps [] = []
getImps (PImp _ _ _ n tm : xs) = (n, tm) : getImps xs
getImps (_ : xs) = getImps xs

getExps :: [PArg] -> [PTerm]
getExps [] = []
getExps (PExp _ _ _ tm : xs) = tm : getExps xs
getExps (_ : xs) = getExps xs

getShowArgs :: [PArg] -> [PArg]
getShowArgs [] = []
getShowArgs (e@(PExp _ _ _ tm) : xs) = e : getShowArgs xs
getShowArgs (e : xs) | AlwaysShow `elem` argopts e = e : getShowArgs xs
                     | PImp _ _ _ _ tm <- e
                     , containsHole tm       = e : getShowArgs xs
getShowArgs (_ : xs) = getShowArgs xs

getConsts :: [PArg] -> [PTerm]
getConsts [] = []
getConsts (PConstraint _ _ _ tm : xs) = tm : getConsts xs
getConsts (_ : xs) = getConsts xs

getAll :: [PArg] -> [PTerm]
getAll = map getTm


-- | Show Idris name
showName :: Maybe IState   -- ^^ the Idris state, for information about names and colours
         -> [(Name, Bool)] -- ^^ the bound variables and whether they're implicit
         -> PPOption         -- ^^ pretty printing options
         -> Bool           -- ^^ whether to colourise
         -> Name           -- ^^ the term to show
         -> String
showName ist bnd ppo colour n = case ist of
                                   Just i -> if colour then colourise n (idris_colourTheme i) else showbasic n
                                   Nothing -> showbasic n
    where name = if ppopt_impl ppo then show n else showbasic n
          showbasic n@(UN _) = showCG n
          showbasic (MN i s) = str s
          showbasic (NS n s) = showSep "." (map str (reverse s)) ++ "." ++ showbasic n
          showbasic (SN s) = show s
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

showTm :: IState -- ^^ the Idris state, for information about identifiers and colours
       -> PTerm  -- ^^ the term to show
       -> String
showTm ist = displayDecorated (consoleDecorate ist) .
             renderPretty 0.8 100000 .
             prettyImp (ppOptionIst ist)

-- | Show a term with implicits, no colours
showTmImpls :: PTerm -> String
showTmImpls = flip (displayS . renderCompact . prettyImp verbosePPOption) ""



instance Sized PTerm where
  size (PQuote rawTerm) = size rawTerm
  size (PRef fc name) = size name
  size (PLam fc name ty bdy) = 1 + size ty + size bdy
  size (PPi plicity name ty bdy) = 1 + size ty + size bdy
  size (PLet fc name ty def bdy) = 1 + size ty + size def + size bdy
  size (PTyped trm ty) = 1 + size trm + size ty
  size (PApp fc name args) = 1 + size args
  size (PAppBind fc name args) = 1 + size args
  size (PCase fc trm bdy) = 1 + size trm + size bdy
  size (PTrue fc _) = 1
  size (PRefl fc _) = 1
  size (PResolveTC fc) = 1
  size (PEq fc _ _ left right) = 1 + size left + size right
  size (PRewrite fc left right _) = 1 + size left + size right
  size (PPair fc _ left right) = 1 + size left + size right
  size (PDPair fs _ left ty right) = 1 + size left + size ty + size right
  size (PAlternative a alts) = 1 + size alts
  size (PHidden hidden) = size hidden
  size (PUnifyLog tm) = size tm
  size (PDisamb _ tm) = size tm
  size (PNoImplicits tm) = size tm
  size PType = 1
  size (PUniverse _) = 1
  size (PConstant const) = 1 + size const
  size Placeholder = 1
  size (PDoBlock dos) = 1 + size dos
  size (PIdiom fc term) = 1 + size term
  size (PReturn fc) = 1
  size (PMetavar name) = 1
  size (PProof tactics) = size tactics
  size (PElabError err) = size err
  size PImpossible = 1
  size _ = 0

getPArity :: PTerm -> Int
getPArity (PPi _ _ _ sc) = 1 + getPArity sc
getPArity _ = 0

-- Return all names, free or globally bound, in the given term.

allNamesIn :: PTerm -> [Name]
allNamesIn tm = nub $ ni [] tm
  where -- TODO THINK added niTacImp, but is it right?
    ni env (PRef _ n)
        | not (n `elem` env) = [n]
    ni env (PPatvar _ n) = [n]
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PAppBind _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PCase _ c os)  = ni env c ++ concatMap (ni env) (map snd os)
    ni env (PLam fc n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi p n ty sc) = niTacImp env p ++ ni env ty ++ ni (n:env) sc
    ni env (PHidden tm)    = ni env tm
    ni env (PEq _ _ _ l r)     = ni env l ++ ni env r
    ni env (PRewrite _ l r _) = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ _ (PRef _ n) t r)  = ni env t ++ ni (n:env) r
    ni env (PDPair _ _ l t r)  = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative a ls) = concatMap (ni env) ls
    ni env (PUnifyLog tm)    = ni env tm
    ni env (PDisamb _ tm)    = ni env tm
    ni env (PNoImplicits tm)    = ni env tm
    ni env _               = []

    niTacImp env (TacImp _ _ scr) = ni env scr
    niTacImp _ _                   = []

-- Return all names defined in binders in the given term
boundNamesIn :: PTerm -> [Name]
boundNamesIn tm = nub $ ni tm
  where -- TODO THINK Added niTacImp, but is it right?
    ni (PApp _ f as)   = ni f ++ concatMap (ni) (map getTm as)
    ni (PAppBind _ f as)   = ni f ++ concatMap (ni) (map getTm as)
    ni (PCase _ c os)  = ni c ++ concatMap (ni) (map snd os)
    ni (PLam fc n ty sc)  = n : (ni ty ++ ni sc)
    ni (PLet fc n ty val sc)  = n : (ni ty ++ ni val ++ ni sc)
    ni (PPi p n ty sc) = niTacImp p ++ (n : (ni ty ++ ni sc))
    ni (PEq _ _ _ l r)     = ni l ++ ni r
    ni (PRewrite _ l r _) = ni l ++ ni r
    ni (PTyped l r)    = ni l ++ ni r
    ni (PPair _ _ l r)   = ni l ++ ni r
    ni (PDPair _ _ (PRef _ n) t r) = ni t ++ ni r
    ni (PDPair _ _ l t r) = ni l ++ ni t ++ ni r
    ni (PAlternative a as) = concatMap (ni) as
    ni (PHidden tm)    = ni tm
    ni (PUnifyLog tm)    = ni tm
    ni (PDisamb _ tm)    = ni tm
    ni (PNoImplicits tm) = ni tm
    ni _               = []

    niTacImp (TacImp _ _ scr) = ni scr
    niTacImp _                = []

-- Return names which are valid implicits in the given term (type).
implicitNamesIn :: [Name] -> IState -> PTerm -> [Name]
implicitNamesIn uvars ist tm = nub $ ni [] tm
  where
    ni env (PRef _ n)
        | not (n `elem` env) 
            = case lookupTy n (tt_ctxt ist) of
                [] -> [n]
                _ -> if n `elem` uvars then [n] else []
    ni env (PApp _ f@(PRef _ n) as) 
        | n `elem` uvars = ni env f ++ concatMap (ni env) (map getTm as)
        | otherwise = concatMap (ni env) (map getTm as)
    ni env (PApp _ f as) = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PAppBind _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PCase _ c os)  = ni env c ++ 
    -- names in 'os', not counting the names bound in the cases
                                (nub (concatMap (ni env) (map snd os))
                                     \\ nub (concatMap (ni env) (map fst os)))
    ni env (PLam fc n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi p n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PEq _ _ _ l r)     = ni env l ++ ni env r
    ni env (PRewrite _ l r _) = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ _ (PRef _ n) t r) = ni env t ++ ni (n:env) r
    ni env (PDPair _ _ l t r) = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative a as) = concatMap (ni env) as
    ni env (PHidden tm)    = ni env tm
    ni env (PUnifyLog tm)    = ni env tm
    ni env (PDisamb _ tm)    = ni env tm
    ni env (PNoImplicits tm) = ni env tm
    ni env _               = []

-- Return names which are free in the given term.
namesIn :: [(Name, PTerm)] -> IState -> PTerm -> [Name]
namesIn uvars ist tm = nub $ ni [] tm
  where
    ni env (PRef _ n)
        | not (n `elem` env)
            = case lookupTy n (tt_ctxt ist) of
                [] -> [n]
                _ -> if n `elem` (map fst uvars) then [n] else []
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PAppBind _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PCase _ c os)  = ni env c ++ 
    -- names in 'os', not counting the names bound in the cases
                                (nub (concatMap (ni env) (map snd os))
                                     \\ nub (concatMap (ni env) (map fst os)))
    ni env (PLam fc n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi p n ty sc) = niTacImp env p ++ ni env ty ++ ni (n:env) sc
    ni env (PEq _ _ _ l r)     = ni env l ++ ni env r
    ni env (PRewrite _ l r _) = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ _ (PRef _ n) t r) = ni env t ++ ni (n:env) r
    ni env (PDPair _ _ l t r) = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative a as) = concatMap (ni env) as
    ni env (PHidden tm)    = ni env tm
    ni env (PUnifyLog tm)    = ni env tm
    ni env (PDisamb _ tm)    = ni env tm
    ni env (PNoImplicits tm) = ni env tm
    ni env _               = []

    niTacImp env (TacImp _ _ scr) = ni env scr
    niTacImp _ _                  = []

-- Return which of the given names are used in the given term.

usedNamesIn :: [Name] -> IState -> PTerm -> [Name]
usedNamesIn vars ist tm = nub $ ni [] tm
  where -- TODO THINK added niTacImp, but is it right?
    ni env (PRef _ n)
        | n `elem` vars && not (n `elem` env)
            = case lookupDefExact n (tt_ctxt ist) of
                Nothing -> [n]
                _ -> []
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PAppBind _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PCase _ c os)  = ni env c ++ concatMap (ni env) (map snd os)
    ni env (PLam fc n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi p n ty sc) = niTacImp env p ++ ni env ty ++ ni (n:env) sc
    ni env (PEq _ _ _ l r)     = ni env l ++ ni env r
    ni env (PRewrite _ l r _) = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ _ (PRef _ n) t r) = ni env t ++ ni (n:env) r
    ni env (PDPair _ _ l t r) = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative a as) = concatMap (ni env) as
    ni env (PHidden tm)    = ni env tm
    ni env (PUnifyLog tm)    = ni env tm
    ni env (PDisamb _ tm)    = ni env tm
    ni env (PNoImplicits tm) = ni env tm
    ni env _               = []

    niTacImp env (TacImp _ _ scr) = ni env scr
    niTacImp _ _                = []

-- Return the list of inaccessible (= dotted) positions for a name.
getErasureInfo :: IState -> Name -> [Int]
getErasureInfo ist n =
    case lookupCtxtExact n (idris_optimisation ist) of
        Just (Optimise inacc detagg) -> map fst inacc
        Nothing -> []


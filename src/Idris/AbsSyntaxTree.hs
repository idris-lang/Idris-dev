{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             TypeSynonymInstances, PatternGuards #-}

module Idris.AbsSyntaxTree where

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Typecheck
import IRTS.Lang
import IRTS.CodegenCommon
import Util.Pretty
import Util.DynamicLinker

import Idris.Colours

import Paths_idris

import System.Console.Haskeline
import System.IO

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Error

import Data.List hiding (group)
import Data.Char
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Map as M
import Data.Either
import qualified Data.Set as S
import Data.Word (Word)

import Debug.Trace

import Text.PrettyPrint.Annotated.Leijen

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
                         opt_optLevel   :: Word,
                         opt_cmdline    :: [Opt], -- remember whole command line
                         opt_origerr    :: Bool
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
                      , opt_codegen    = ViaC
                      , opt_outputTy   = Executable
                      , opt_ibcsubdir  = ""
                      , opt_importdirs = []
                      , opt_triple     = ""
                      , opt_cpu        = ""
                      , opt_optLevel   = 2
                      , opt_cmdline    = []
                      , opt_origerr    = False
                      }

data LanguageExt = TypeProviders | ErrorReflection deriving (Show, Eq, Read, Ord)

-- | The output mode in use
data OutputMode = RawOutput | IdeSlave Integer deriving Show

-- | How wide is the console?
data ConsoleWidth = InfinitelyWide -- ^ Have pretty-printer assume that lines should not be broken
                  | ColsWide Int -- ^ Manually specified - must be positive
                  | AutomaticWidth -- ^ Attempt to determine width, or 80 otherwise

-- TODO: Add 'module data' to IState, which can be saved out and reloaded quickly (i.e
-- without typechecking).
-- This will include all the functions and data declarations, plus fixity declarations
-- and syntax macros.

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
    idris_docstrings :: Ctxt String,
    idris_totcheck :: [(FC, Name)], -- names to check totality on 
    idris_defertotcheck :: [(FC, Name)], -- names to check at the end
    idris_options :: IOption,
    idris_name :: Int,
    idris_lineapps :: [((FilePath, Int), PTerm)],
          -- ^ Full application LHS on source line
    idris_metavars :: [(Name, (Maybe Name, Int, Bool))], -- ^ The currently defined but not proven metavariables
    idris_coercions :: [Name],
    idris_transforms :: [(Term, Term)],
    idris_errRev :: [(Term, Term)],
    syntax_rules :: [Syntax],
    syntax_keywords :: [String],
    imported :: [FilePath], -- ^ The imported modules
    idris_scprims :: [(Name, (Int, PrimFn))],
    idris_objs :: [(Codegen, FilePath)],
    idris_libs :: [(Codegen, String)],
    idris_cgflags :: [(Codegen, String)],
    idris_hdrs :: [(Codegen, String)],
    proof_list :: [(Name, [String])],
    errLine :: Maybe Int,
    lastParse :: Maybe Name,
    indent_stack :: [Int],
    brace_stack :: [Maybe Int],
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
    idris_outh :: Handle,
    idris_errorhandlers :: [Name], -- ^ Global error handlers
    idris_nameIdx :: (Int, Ctxt (Int, Name)),
    idris_function_errorhandlers :: Ctxt (M.Map Name (S.Set Name)), -- ^ Specific error handlers
    module_aliases :: M.Map [T.Text] [T.Text],
    idris_consolewidth :: ConsoleWidth -- ^ How many chars wide is the console?
   }

data SizeChange = Smaller | Same | Bigger | Unknown
    deriving (Show, Eq)
{-!
deriving instance Binary SizeChange
deriving instance NFData SizeChange
!-}

type SCGEntry = (Name, [Maybe (Int, SizeChange)])

data CGInfo = CGInfo { argsdef :: [Name],
                       calls :: [(Name, [[Name]])],
                       scg :: [SCGEntry],
                       argsused :: [Name],
                       unusedpos :: [Int] }
    deriving Show
{-!
deriving instance Binary CGInfo
deriving instance NFData CGInfo
!-}

primDefs = [sUN "unsafePerformPrimIO",
            sUN "mkLazyForeignPrim",
            sUN "mkForeignPrim",
            sUN "FalseElim"]

-- information that needs writing for the current module's .ibc file
data IBCWrite = IBCFix FixDecl
              | IBCImp Name
              | IBCStatic Name
              | IBCClass Name
              | IBCInstance Bool Name Name
              | IBCDSL Name
              | IBCData Name
              | IBCOpt Name
              | IBCSyntax Syntax
              | IBCKeyword String
              | IBCImport FilePath
              | IBCObj Codegen FilePath
              | IBCLib Codegen String
              | IBCCGFlag Codegen String
              | IBCDyLib String
              | IBCHeader Codegen String
              | IBCAccess Name Accessibility
              | IBCMetaInformation Name MetaInformation
              | IBCTotal Name Totality
              | IBCFlags Name [FnOpt]
              | IBCTrans (Term, Term)
              | IBCErrRev (Term, Term)
              | IBCCG Name
              | IBCDoc Name
              | IBCCoercion Name
              | IBCDef Name -- i.e. main context
              | IBCNameHint (Name, Name)
              | IBCLineApp FilePath Int PTerm
              | IBCErrorHandler Name
              | IBCFunctionErrorHandler Name Name Name
  deriving Show

-- | The initial state for the compiler
idrisInit :: IState
idrisInit = IState initContext [] [] emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext
                   [] [] defaultOpts 6 [] [] [] [] [] [] [] [] [] [] [] [] []
                   [] Nothing Nothing [] [] [] Hidden False [] Nothing [] [] RawOutput
                   True defaultTheme stdout [] (0, emptyContext) emptyContext M.empty
                   AutomaticWidth

-- | The monad for the main REPL - reading and processing files and updating
-- global state (hence the IO inner monad).
--type Idris = WriterT [Either String (IO ())] (State IState a))
type Idris = StateT IState (ErrorT Err IO)

-- Commands in the REPL

data Codegen = ViaC
             | ViaJava
             | ViaNode
             | ViaJavaScript
             | ViaLLVM
             | Bytecode
    deriving (Show, Eq)

-- | REPL commands
data Command = Quit
             | Help
             | Eval PTerm
             | Check PTerm
             | DocStr Name
             | TotCheck Name
             | Reload
             | Load FilePath
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
             | Info Name
             | Missing Name
             | DynamicLink FilePath
             | ListDynamic
             | Pattelab PTerm
             | DebugInfo Name
             | Search PTerm
             | CaseSplitAt Bool Int Name
             | AddClauseFrom Bool Int Name
             | AddProofClauseFrom Bool Int Name
             | AddMissing Bool Int Name
             | MakeWith Bool Int Name
             | DoProofSearch Bool Int Name [Name]
             | SetOpt Opt
             | UnsetOpt Opt
             | NOP
             | SetColour ColourType IdrisColour
             | ColourOn
             | ColourOff
             | ListErrorHandlers
             | SetConsoleWidth ConsoleWidth

data Opt = Filename String
         | Ver
         | Usage
         | Quiet
         | NoBanner
         | ColourREPL Bool
         | Ideslave
         | ShowLibs
         | ShowLibdir
         | ShowIncs
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
         | NoCoverage
         | ErrContext
         | ShowImpl
         | Verbose
         | IBCSubDir String
         | ImportDir String
         | PkgBuild String
         | PkgInstall String
         | PkgClean String
         | PkgCheck String
         | PkgREPL String
         | WarnOnly
         | Pkg String
         | BCAsm String
         | DumpDefun String
         | DumpCases String
         | UseCodegen Codegen
         | OutputTy OutputType
         | Extension LanguageExt
         | InterpretScript String
         | TargetTriple String
         | TargetCPU String
         | OptLevel Word
         | Client String
         | ShowOrigErr
         | AutoWidth -- ^ Automatically adjust terminal width
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
  deriving (Show, Eq)
{-!
deriving instance Binary Static
deriving instance NFData Static
!-}

-- Mark bindings with their explicitness, and laziness
data Plicity = Imp { pargopts :: [ArgOpt],
                     pstatic :: Static,
                     pdocstr :: String,
                     pparam :: Bool }
             | Exp { pargopts :: [ArgOpt],
                     pstatic :: Static,
                     pdocstr :: String,
                     pparam :: Bool }
             | Constraint { pargopts :: [ArgOpt],
                            pstatic :: Static,
                            pdocstr :: String }
             | TacImp { pargopts :: [ArgOpt],
                        pstatic :: Static,
                        pscript :: PTerm,
                        pdocstr :: String }
  deriving (Show, Eq)

plazy :: Plicity -> Bool
plazy tm = Lazy `elem` pargopts tm

{-!
deriving instance Binary Plicity
deriving instance NFData Plicity
!-}

impl = Imp [Lazy] Dynamic "" False
expl = Exp [] Dynamic "" False
expl_param = Exp [] Dynamic "" True
constraint = Constraint [] Dynamic ""
tacimpl t = TacImp [] Dynamic t ""

data FnOpt = Inlinable -- always evaluate when simplifying
           | TotalFn | PartialFn
           | Coinductive | AssertTotal
           | Dictionary -- type class dictionary, eval only when
                        -- a function argument, and further evaluation resutls
           | Implicit -- implicit coercion
           | CExport String    -- export, with a C name
           | ErrorHandler     -- ^^ an error handler for use with the ErrorReflection extension
           | ErrorReverse     -- ^^ attempt to reverse normalise before showing in error 
           | Reflection -- a reflecting function, compile-time only
           | Specialise [(Name, Maybe Int)] -- specialise it, freeze these names
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
data DataOpt = Codata -- Set if the the data-type is coinductive
             | DefaultEliminator -- Set if an eliminator should be generated for data type
             | DataErrRev
    deriving (Show, Eq)

type DataOpts = [DataOpt]

-- | Top-level declarations such as compiler directives, definitions,
-- datatypes and typeclasses.
data PDecl' t
   = PFix     FC Fixity [String] -- ^ Fixity declaration
   | PTy      String SyntaxInfo FC FnOpts Name t   -- ^ Type declaration
   | PPostulate String SyntaxInfo FC FnOpts Name t -- ^ Postulate
   | PClauses FC FnOpts Name [PClause' t]   -- ^ Pattern clause
   | PCAF     FC Name t -- ^ Top level constant
   | PData    String SyntaxInfo FC DataOpts (PData' t)  -- ^ Data declaration.
   | PParams  FC [(Name, t)] [PDecl' t] -- ^ Params block
   | PNamespace String [PDecl' t] -- ^ New namespace
   | PRecord  String SyntaxInfo FC Name t String Name t  -- ^ Record declaration
   | PClass   String SyntaxInfo FC
              [t] -- constraints
              Name
              [(Name, t)] -- parameters
              [PDecl' t] -- declarations
              -- ^ Type class: arguments are documentation, syntax info, source location, constraints,
              -- class name, parameters, method declarations
   | PInstance SyntaxInfo FC [t] -- constraints
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
   | PProvider SyntaxInfo FC Name t t -- ^ Type provider. The first t is the type, the second is the term
   | PTransform FC Bool t t -- ^ Source-to-source transformation rule. If
                            -- bool is True, lhs and rhs must be convertible
 deriving Functor
{-!
deriving instance Binary PDecl'
deriving instance NFData PDecl'
!-}

-- For elaborator state
type ElabD a = Elab' [PDecl] a

-- | One clause of a top-level definition. Term arguments to constructors are:
--
-- 1. The whole application (missing for PClauseR and PWithR because they're within a "with" clause)
--
-- 2. The list of extra 'with' patterns
--
-- 3. The right-hand side
--
-- 4. The where block (PDecl' t)

data PClause' t = PClause  FC Name t [t] t [PDecl' t] -- ^ A normal top-level definition.
                | PWith    FC Name t [t] t [PDecl' t]
                | PClauseR FC        [t] t [PDecl' t]
                | PWithR   FC        [t] t [PDecl' t]
    deriving Functor
{-!
deriving instance Binary PClause'
deriving instance NFData PClause'
!-}

-- | Data declaration
data PData' t  = PDatadecl { d_name :: Name, -- ^ The name of the datatype
                             d_tcon :: t, -- ^ Type constructor
                             d_cons :: [(String, Name, t, FC, [Name])] -- ^ Constructors
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
declared (PTy _ _ _ _ n t) = [n]
declared (PPostulate _ _ _ _ n t) = [n]
declared (PClauses _ _ n _) = [] -- not a declaration
declared (PCAF _ n _) = [n]
declared (PData _ _ _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (_, a, _, _, _) = a
declared (PData _ _ _ _ (PLaterdecl n _)) = [n]
declared (PParams _ _ ds) = concatMap declared ds
declared (PNamespace _ ds) = concatMap declared ds
declared (PRecord _ _ _ n _ _ c _) = [n, c]
declared (PClass _ _ _ _ n _ ms) = n : concatMap declared ms
declared (PInstance _ _ _ _ _ _ _ _) = []
declared (PDSL n _) = [n]
declared (PSyntax _ _) = []
declared (PMutual _ ds) = concatMap declared ds
declared (PDirective _) = []

-- get the names declared, not counting nested parameter blocks
tldeclared :: PDecl -> [Name]
tldeclared (PFix _ _ _) = []
tldeclared (PTy _ _ _ _ n t) = [n]
tldeclared (PPostulate _ _ _ _ n t) = [n]
tldeclared (PClauses _ _ n _) = [] -- not a declaration
tldeclared (PRecord _ _ _ n _ _ c _) = [n, c]
tldeclared (PData _ _ _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (_, a, _, _, _) = a
tldeclared (PParams _ _ ds) = []
tldeclared (PMutual _ ds) = concatMap tldeclared ds
tldeclared (PNamespace _ ds) = concatMap tldeclared ds
tldeclared (PClass _ _ _ _ n _ ms) = concatMap tldeclared ms
tldeclared (PInstance _ _ _ _ _ _ _ _) = []
tldeclared _ = []

defined :: PDecl -> [Name]
defined (PFix _ _ _) = []
defined (PTy _ _ _ _ n t) = []
defined (PPostulate _ _ _ _ n t) = []
defined (PClauses _ _ n _) = [n] -- not a declaration
defined (PCAF _ n _) = [n]
defined (PData _ _ _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (_, a, _, _, _) = a
defined (PData _ _ _ _ (PLaterdecl n _)) = []
defined (PParams _ _ ds) = concatMap defined ds
defined (PNamespace _ ds) = concatMap defined ds
defined (PRecord _ _ _ n _ _ c _) = [n, c]
defined (PClass _ _ _ _ n _ ms) = n : concatMap defined ms
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

data PunInfo = IsType | IsTerm | TypeOrTerm deriving (Eq, Show)

-- | High level language terms
data PTerm = PQuote Raw
           | PRef FC Name
           | PInferRef FC Name -- ^ A name to be defined later
           | PPatvar FC Name
           | PLam Name PTerm PTerm
           | PPi  Plicity Name PTerm PTerm
           | PLet Name PTerm PTerm PTerm
           | PTyped PTerm PTerm -- ^ Term with explicit type
           | PApp FC PTerm [PArg]
           | PAppBind FC PTerm [PArg] -- ^ implicitly bound application
           | PMatchApp FC Name -- ^ Make an application by type matching
           | PCase FC PTerm [(PTerm, PTerm)]
           | PTrue FC PunInfo
           | PFalse FC
           | PRefl FC PTerm
           | PResolveTC FC
           | PEq FC PTerm PTerm
           | PRewrite FC PTerm PTerm (Maybe PTerm)
           | PPair FC PunInfo PTerm PTerm
           | PDPair FC PTerm PTerm PTerm
           | PAlternative Bool [PTerm] -- True if only one may work
           | PHidden PTerm -- ^ Irrelevant or hidden pattern
           | PType
           | PGoal FC PTerm Name PTerm
           | PConstant Const
           | Placeholder
           | PDoBlock [PDo]
           | PIdiom FC PTerm
           | PReturn FC
           | PMetavar Name
           | PProof [PTactic] -- ^ Proof script
           | PTactics [PTactic] -- ^ As PProof, but no auto solving
           | PElabError Err -- ^ Error to report on elaboration
           | PImpossible -- ^ Special case for declaring when an LHS can't typecheck
           | PCoerced PTerm -- ^ To mark a coerced argument, so as not to coerce twice
           | PDisamb [[T.Text]] PTerm -- ^ Preferences for explicit namespaces
           | PUnifyLog PTerm -- ^ dump a trace of unifications when building term
           | PNoImplicits PTerm -- ^ never run implicit converions on the term
       deriving Eq


{-!
deriving instance Binary PTerm
deriving instance NFData PTerm
!-}

mapPT :: (PTerm -> PTerm) -> PTerm -> PTerm
mapPT f t = f (mpt t) where
  mpt (PLam n t s) = PLam n (mapPT f t) (mapPT f s)
  mpt (PPi p n t s) = PPi p n (mapPT f t) (mapPT f s)
  mpt (PLet n ty v s) = PLet n (mapPT f ty) (mapPT f v) (mapPT f s)
  mpt (PRewrite fc t s g) = PRewrite fc (mapPT f t) (mapPT f s)
                                 (fmap (mapPT f) g)
  mpt (PApp fc t as) = PApp fc (mapPT f t) (map (fmap (mapPT f)) as)
  mpt (PAppBind fc t as) = PAppBind fc (mapPT f t) (map (fmap (mapPT f)) as)
  mpt (PCase fc c os) = PCase fc (mapPT f c) (map (pmap (mapPT f)) os)
  mpt (PEq fc l r) = PEq fc (mapPT f l) (mapPT f r)
  mpt (PTyped l r) = PTyped (mapPT f l) (mapPT f r)
  mpt (PPair fc p l r) = PPair fc p (mapPT f l) (mapPT f r)
  mpt (PDPair fc l t r) = PDPair fc (mapPT f l) (mapPT f t) (mapPT f r)
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
                | Refine Name [Bool] | Rewrite t
                | Induction Name
                | Equiv t
                | MatchRefine Name
                | LetTac Name t | LetTacTy Name t t
                | Exact t | Compute | Trivial | TCInstance
                | ProofSearch (Maybe Name) Name [Name]
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
                | Qed | Abandon
    deriving (Show, Eq, Functor)
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

type PTactic = PTactic' PTerm

data PDo' t = DoExp  FC t
            | DoBind FC Name t
            | DoBindP FC t t
            | DoLet  FC Name t t
            | DoLetP FC t t
    deriving (Eq, Functor)
{-!
deriving instance Binary PDo'
deriving instance NFData PDo'
!-}

instance Sized a => Sized (PDo' a) where
  size (DoExp fc t) = 1 + size fc + size t
  size (DoBind fc nm t) = 1 + size fc + size nm + size t
  size (DoBindP fc l r) = 1 + size fc + size l + size r
  size (DoLet fc nm l r) = 1 + size fc + size nm + size l + size r
  size (DoLetP fc l r) = 1 + size fc + size l + size r

type PDo = PDo' PTerm

-- The priority gives a hint as to elaboration order. Best to elaborate
-- things early which will help give a more concrete type to other
-- variables, e.g. a before (interpTy a).

data PArg' t = PImp { priority :: Int,
                      machine_inf :: Bool, -- true if the machine inferred it
                      argopts :: [ArgOpt],
                      pname :: Name, getTm :: t,
                      pargdoc :: String }
             | PExp { priority :: Int,
                      argopts :: [ArgOpt],
                      getTm :: t,
                      pargdoc :: String }
             | PConstraint { priority :: Int,
                             argopts :: [ArgOpt],
                             getTm :: t,
                             pargdoc :: String }
             | PTacImplicit { priority :: Int,
                              argopts :: [ArgOpt],
                              pname :: Name,
                              getScript :: t,
                              getTm :: t,
                              pargdoc :: String }
    deriving (Show, Eq, Functor)

data ArgOpt = Lazy | HideDisplay
    deriving (Show, Eq)

lazyarg :: PArg' t -> Bool
lazyarg tm = Lazy `elem` argopts tm

instance Sized a => Sized (PArg' a) where
  size (PImp p _ l nm trm _) = 1 + size nm + size trm
  size (PExp p l trm _) = 1 + size trm
  size (PConstraint p l trm _) = 1 + size trm
  size (PTacImplicit p l nm scr trm _) = 1 + size nm + size scr + size trm

{-!
deriving instance Binary PArg'
deriving instance NFData PArg'
!-}

pimp n t mach = PImp 1 mach [Lazy] n t ""
pexp t = PExp 1 [] t ""
pconst t = PConstraint 1 [] t ""
ptacimp n s t = PTacImplicit 2 [Lazy] n s t ""

type PArg = PArg' PTerm

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

-- An argument is conditionally forceable iff its forceability
-- depends on the collapsibility of the whole type.
data Forceability = Conditional | Unconditional deriving (Show, Enum, Bounded, Eq, Ord)

{-!
deriving instance Binary Forceability
deriving instance NFData Forceability
!-}

data OptInfo = Optimise { collapsible :: Bool,
                          isnewtype :: Bool,
                          -- The following should actually be (IntMap Forceability)
                          -- but the corresponding Binary instance seems to be broken.
                          -- Let's store a list and convert it to IntMap whenever needed.
                          forceable :: [(Int, Forceability)],
                          recursive :: [Int] }
    deriving Show
{-!
deriving instance Binary OptInfo
deriving instance NFData OptInfo
!-}


data TypeInfo = TI { con_names :: [Name],
                     codata :: Bool,
                     data_opts :: DataOpts,
                     param_pos :: [Int] }
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
                    dsl_let     :: Maybe t
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
{-!
deriving instance Binary Syntax
deriving instance NFData Syntax
!-}

data SSymbol = Keyword Name
             | Symbol String
             | Binding Name
             | Expr Name
             | SimpleExpr Name
    deriving Show
{-!
deriving instance Binary SSymbol
deriving instance NFData SSymbol
!-}

initDSL = DSL (PRef f (sUN ">>="))
              (PRef f (sUN "return"))
              (PRef f (sUN "<$>"))
              (PRef f (sUN "pure"))
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
                        dsl_info :: DSL }
    deriving Show
{-!
deriving instance NFData SyntaxInfo
deriving instance Binary SyntaxInfo
!-}

defaultSyntax = Syn [] [] [] [] id False False initDSL

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
                      [("", inferCon, PPi impl (sMN 0 "iType") PType (
                                  PPi expl (sMN 0 "ival") (PRef bi (sMN 0 "iType"))
                                  (PRef bi inferTy)), bi, [])]
inferOpts = []

infTerm t = PApp bi (PRef bi inferCon) [pimp (sMN 0 "iType") Placeholder True, pexp t]
infP = P (TCon 6 0) inferTy (TType (UVal 0))

getInferTerm, getInferType :: Term -> Term
getInferTerm (Bind n b sc) = Bind n b $ getInferTerm sc
getInferTerm (App (App _ _) tm) = tm
getInferTerm tm = tm -- error ("getInferTerm " ++ show tm)

getInferType (Bind n b sc) = Bind n b $ getInferType sc
getInferType (App (App _ ty) _) = ty



-- Handy primitives: Unit, False, Pair, MkPair, =, mkForeign, Elim type class

primNames = [unitTy, unitCon,
             falseTy, pairTy, pairCon,
             eqTy, eqCon, inferTy, inferCon]

unitTy   = sMN 0 "__Unit"
unitCon  = sMN 0 "__II"
unitDecl = PDatadecl unitTy PType
                     [("", unitCon, PRef bi unitTy, bi, [])]
unitOpts = [DefaultEliminator]

falseTy   = sMN 0 "__False"
falseDecl = PDatadecl falseTy PType []
falseOpts = []

pairTy    = sMN 0 "__Pair"
pairCon   = sMN 0 "__MkPair"
pairDecl  = PDatadecl pairTy (piBind [(n "A", PType), (n "B", PType)] PType)
            [("", pairCon, PPi impl (n "A") PType (
                       PPi impl (n "B") PType (
                       PPi expl (n "a") (PRef bi (n "A")) (
                       PPi expl (n "b") (PRef bi (n "B"))
                           (PApp bi (PRef bi pairTy) [pexp (PRef bi (n "A")),
                                                pexp (PRef bi (n "B"))])))), bi, [])]
    where n a = sMN 0 a
pairOpts = []

eqTy = sUN "="
eqCon = sUN "refl"
eqDecl = PDatadecl eqTy (piBind [(n "A", PType), (n "B", PType),
                                 (n "x", PRef bi (n "A")), (n "y", PRef bi (n "B"))]
                                 PType)
                [("", eqCon, PPi impl (n "A") PType (
                         PPi impl (n "x") (PRef bi (n "A"))
                           (PApp bi (PRef bi eqTy) [pimp (n "A") Placeholder False,
                                                    pimp (n "B") Placeholder False,
                                                    pexp (PRef bi (n "x")),
                                                    pexp (PRef bi (n "x"))])), bi, [])]
    where n a = sMN 0 a
eqOpts = []

elimName       = sUN "__Elim"
elimMethElimTy = sUN "__elimTy"
elimMethElim   = sUN "elim"
elimDecl = PClass "Type class for eliminators" defaultSyntax bi [] elimName [(sUN "scrutineeType", PType)]
                     [PTy "" defaultSyntax bi [TotalFn] elimMethElimTy PType,
                      PTy "" defaultSyntax bi [TotalFn] elimMethElim (PRef bi elimMethElimTy)]

-- Defined in builtins.idr
sigmaTy   = sUN "Exists"
existsCon = sUN "Ex_intro"

piBind :: [(Name, PTerm)] -> PTerm -> PTerm
piBind = piBindp expl

piBindp :: Plicity -> [(Name, PTerm)] -> PTerm -> PTerm
piBindp p [] t = t
piBindp p ((n, ty):ns) t = PPi p n ty (piBindp p ns t)


-- Pretty-printing declarations and terms

-- These "show" instances render to an absurdly wide screen because inserted line breaks
-- could interfere with interactive editing, which calls "show".

instance Show PTerm where
  showsPrec _ tm = (displayS . renderPretty 1.0 10000000 . prettyImp False) tm

instance Show PDecl where
  showsPrec _ d = (displayS . renderPretty 1.0 10000000 . showDeclImp False) d

instance Show PClause where
  showsPrec _ c = (displayS . renderPretty 1.0 10000000 . showCImp True) c

instance Show PData where
  showsPrec _ d = (displayS . renderPretty 1.0 10000000 . showDImp False) d

instance Pretty PTerm OutputAnnotation where
  pretty = prettyImp False

-- | Colourise annotations according to an Idris state. It ignores the names
-- in the annotation, as there's no good way to show extended information on a
-- terminal.
consoleDecorate :: IState -> OutputAnnotation -> String -> String
consoleDecorate ist _ | not (idris_colourRepl ist) = id
consoleDecorate ist AnnConstData = let theme = idris_colourTheme ist
                                   in colouriseData theme
consoleDecorate ist AnnConstType = let theme = idris_colourTheme ist
                                   in colouriseType theme
consoleDecorate ist (AnnBoundName _ True) = colouriseImplicit (idris_colourTheme ist)
consoleDecorate ist (AnnBoundName _ False) = colouriseBound (idris_colourTheme ist)
consoleDecorate ist (AnnName n _ _) = let ctxt  = tt_ctxt ist
                                          theme = idris_colourTheme ist
                                      in case () of
                                           _ | isDConName n ctxt -> colouriseData theme
                                           _ | isFnName n ctxt   -> colouriseFun theme
                                           _ | isTConName n ctxt -> colouriseType theme
                                           _ | otherwise         -> id -- don't colourise unknown names
consoleDecorate ist (AnnFC _) = id

-- | Pretty-print a high-level closed Idris term
prettyImp :: Bool -- ^^ whether to show implicits
          -> PTerm -- ^^ the term to pretty-print
          -> Doc OutputAnnotation
prettyImp impl = pprintPTerm impl []

-- | Pretty-print a high-level Idris term in some bindings context
pprintPTerm :: Bool -- ^^ whether to show implicits
            -> [(Name, Bool)] -- ^^ the currently-bound names and whether they are implicit
            -> PTerm -- ^^ the term to pretty-print
            -> Doc OutputAnnotation
pprintPTerm impl bnd = prettySe 10 bnd
  where
    prettySe :: Int -> [(Name, Bool)] -> PTerm -> Doc OutputAnnotation
    prettySe p bnd (PQuote r) =
        text "![" <> pretty r <> text "]"
    prettySe p bnd (PPatvar fc n) = pretty n
    prettySe p bnd e
      | Just str <- slist p bnd e = str
      | Just n <- snat p e = annotate AnnConstData (text (show n))
    prettySe p bnd (PRef fc n) = prettyName impl bnd n
    prettySe p bnd (PLam n ty sc) =
      bracket p 2 . group . align . hang 2 $
      text "\\" <> bindingOf n False <+> text "=>" <$>
      prettySe 10 ((n, False):bnd) sc
    prettySe p bnd (PLet n ty v sc) =
      bracket p 2 $
      text "let" <+> bindingOf n False <+> text "=" </>
      prettySe 10 bnd v <+> text "in" </>
      prettySe 10 ((n, False):bnd) sc
    prettySe p bnd (PPi (Exp l s _ _) n ty sc)
      | n `elem` allNamesIn sc || impl =
          let open = if Lazy `elem` l then text "|" <> lparen else lparen in
            bracket p 2 . group $
            enclose open rparen (group . align $ bindingOf n False <+> colon <+> prettySe 10 bnd ty) <+>
            st <> text "->" <$> prettySe 10 ((n, False):bnd) sc
      | otherwise                      =
          bracket p 2 . group $
          group (prettySe 0 bnd ty <+> st) <> text "->" <$> group (prettySe 10 ((n, False):bnd) sc)
      where
        st =
          case s of
            Static -> text "[static]" <> space
            _      -> empty
    prettySe p bnd (PPi (Imp l s _ _) n ty sc)
      | impl =
          let open = if Lazy `elem` l then text "|" <> lbrace else lbrace in
            bracket p 2 $
            open <> bindingOf n True <+> colon <+> prettySe 10 bnd ty <> rbrace <+>
            st <> text "->" </> prettySe 10 ((n, True):bnd) sc
      | otherwise = prettySe 10 ((n, True):bnd) sc
      where
        st =
          case s of
            Static -> text "[static]" <> space
            _      -> empty
    prettySe p bnd (PPi (Constraint _ _ _) n ty sc) =
      bracket p 2 $
      prettySe 10 bnd ty <+> text "=>" </> prettySe 10 ((n, True):bnd) sc
    prettySe p bnd (PPi (TacImp _ _ s _) n ty sc) =
      bracket p 2 $
      lbrace <> text "tacimp" <+> pretty n <+> colon <+> prettySe 10 bnd ty <>
      rbrace <+> text "->" </> prettySe 10 ((n, True):bnd) sc
    prettySe p bnd (PApp _ (PRef _ f) [])
      | not impl = prettyName impl bnd f
    prettySe p bnd (PAppBind _ (PRef _ f) [])
      | not impl = text "!" <> prettyName impl bnd f
    prettySe p bnd (PApp _ (PRef _ op) args)
      | UN nm <- basename op
      , not (tnull nm) &&
        length (getExps args) == 2 && (not impl) && (not $ isAlpha (thead nm)) =
          let [l, r] = getExps args in
            bracket p 1 . align . group $
            (prettySe 1 bnd l <+> prettyName impl bnd op) <$> group (prettySe 0 bnd r)
    prettySe p bnd (PApp _ hd@(PRef fc f) [tm])
      | PConstant (Idris.Core.TT.Str str) <- getTm tm,
        f == sUN "Symbol_" = char '\'' <> prettySe 10 bnd (PRef fc (sUN str))
    prettySe p bnd (PApp _ f as) =
      let args = getExps as
          fp   = prettySe 1 bnd f
      in
        bracket p 1 . group $
          if impl
            then if null as
                   then fp
                   else fp <+> align (vsep (map (prettyArgS bnd) as))
            else if null args
                   then fp
                   else fp <+> align (vsep (map (prettyArgSe bnd) args))
    prettySe p bnd (PCase _ scr opts) =
      text "case" <+> prettySe 10 bnd scr <+> text "of" <> prettyBody
      where
        prettyBody = foldr (<>) empty $ intersperse (text "|") $ map sc opts

        sc (l, r) = nest nestingSize $ prettySe 10 bnd l <+> text "=>" <+> prettySe 10 bnd r
    prettySe p bnd (PHidden tm) = text "." <> prettySe 0 bnd tm
    prettySe p bnd (PRefl _ _) = annotate (AnnName eqCon Nothing Nothing) $ text "refl"
    prettySe p bnd (PResolveTC _) = text "resolvetc"
    prettySe p bnd (PTrue _ IsType) = annotate (AnnName unitTy Nothing Nothing) $ text "()"
    prettySe p bnd (PTrue _ IsTerm) = annotate (AnnName unitCon Nothing Nothing) $ text "()"
    prettySe p bnd (PTrue _ TypeOrTerm) = text "()"
    prettySe p bnd (PFalse _) = annotate (AnnName falseTy Nothing Nothing) $ text "_|_"
    prettySe p bnd (PEq _ l r) =
      bracket p 2 . align . group $
      prettySe 10 bnd l <+> eq <$> group (prettySe 10 bnd r)
      where eq = annotate (AnnName eqTy Nothing Nothing) (text "=")
    prettySe p bnd (PRewrite _ l r _) =
      bracket p 2 $
      text "rewrite" <+> prettySe 10 bnd l <+> text "in" <+> prettySe 10 bnd r
    prettySe p bnd (PTyped l r) =
      lparen <> prettySe 10 bnd l <+> colon <+> prettySe 10 bnd r <> rparen
    prettySe p bnd (PPair _ TypeOrTerm l r) =
      lparen <> prettySe 10 bnd l <> text "," <+> prettySe 10 bnd r <> rparen
    prettySe p bnd (PPair _ IsType l r) =
      annotate (AnnName pairTy Nothing Nothing) lparen <>
      prettySe 10 bnd l <>
      annotate (AnnName pairTy Nothing Nothing) comma <+>
      prettySe 10 bnd r <>
      annotate (AnnName pairTy Nothing Nothing) rparen
    prettySe p bnd (PPair _ IsTerm l r) =
      annotate (AnnName pairCon Nothing Nothing) lparen <>
      prettySe 10 bnd l <>
      annotate (AnnName pairCon Nothing Nothing) comma <+>
      prettySe 10 bnd r <>
      annotate (AnnName pairCon Nothing Nothing) rparen
    prettySe p bnd (PDPair _ l t r) =
      lparen <> prettySe 10 bnd l <+> text "**" <+> prettySe 10 bnd r <> rparen
    prettySe p bnd (PAlternative a as) =
      lparen <> text "|" <> prettyAs <> text "|" <> rparen
        where
          prettyAs =
            foldr (\l -> \r -> l <+> text "," <+> r) empty $ map (prettySe 10 bnd) as
    prettySe p bnd PType = annotate AnnConstType $ text "Type"
    prettySe p bnd (PConstant c) = annotate (annot c) (text (show c))
      where annot (AType _) = AnnConstType
            annot StrType   = AnnConstType
            annot PtrType   = AnnConstType
            annot VoidType  = AnnConstType
            annot _         = AnnConstData
    -- XXX: add pretty for tactics
    prettySe p bnd (PProof ts) =
      text "proof" <+> lbrace <> nest nestingSize (text . show $ ts) <> rbrace
    prettySe p bnd (PTactics ts) =
      text "tactics" <+> lbrace <> nest nestingSize (text . show $ ts) <> rbrace
    prettySe p bnd (PMetavar n) = text "?" <> pretty n
    prettySe p bnd (PReturn f) = text "return"
    prettySe p bnd PImpossible = text "impossible"
    prettySe p bnd Placeholder = text "_"
    prettySe p bnd (PDoBlock _) = text "do block pretty not implemented"
    prettySe p bnd (PElabError s) = pretty s

    prettySe p bnd _ = text "test"

    prettyArgS bnd (PImp _ _ _ n tm _) = prettyArgSi bnd (n, tm)
    prettyArgS bnd (PExp _ _ tm _)   = prettyArgSe bnd tm
    prettyArgS bnd (PConstraint _ _ tm _) = prettyArgSc bnd tm
    prettyArgS bnd (PTacImplicit _ _ n _ tm _) = prettyArgSti bnd (n, tm)

    prettyArgSe bnd arg = prettySe 0 bnd arg
    prettyArgSi bnd (n, val) = lbrace <> pretty n <+> text "=" <+> prettySe 10 bnd val <> rbrace
    prettyArgSc bnd val = lbrace <> lbrace <> prettySe 10 bnd val <> rbrace <> rbrace
    prettyArgSti bnd (n, val) = lbrace <> text "auto" <+> pretty n <+> text "=" <+> prettySe 10 bnd val <> rbrace

    basename :: Name -> Name
    basename (NS n _) = basename n
    basename n = n

    slist' p bnd (PApp _ (PRef _ nil) _)
      | not impl && nsroot nil == sUN "Nil" = Just []
    slist' p bnd (PRef _ nil)
      | not impl && nsroot nil == sUN "Nil" = Just []
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
      case es of [] -> annotate AnnConstData $ text "[]"
                 [x] -> enclose left right . group $
                        prettySe p bnd x
                 xs -> (enclose left right .
                        align . group . vsep .
                        punctuate comma .
                        map (prettySe p bnd)) xs
      where left  = (annotate AnnConstData (text "["))
            right = (annotate AnnConstData (text "]"))
            comma = (annotate AnnConstData (text ","))
    slist _ _ _ = Nothing

    natns = "Prelude.Nat."

    snat p (PRef _ z)
      | show z == (natns++"Z") || show z == "Z" = Just 0
    snat p (PApp _ s [PExp {getTm=n}])
      | show s == (natns++"S") || show s == "S",
        Just n' <- snat p n
      = Just $ 1 + n'
    snat _ _ = Nothing

    bracket outer inner doc
      | inner > outer = lparen <> doc <> rparen
      | otherwise     = doc

-- | Pretty-printer helper for the binding site of a name
bindingOf :: Name -- ^^ the bound name
          -> Bool -- ^^ whether the name is implicit
          -> Doc OutputAnnotation
bindingOf n imp = annotate (AnnBoundName n imp) (text (show n))

-- | Pretty-printer helper for names that attaches the correct annotations
prettyName :: Bool -- ^^ whether to show namespaces
           -> [(Name, Bool)] -- ^^ the current bound variables and whether they are implicit
           -> Name -- ^^ the name to pprint
           -> Doc OutputAnnotation
prettyName showNS bnd n | Just imp <- lookup n bnd = annotate (AnnBoundName n imp) (text (strName n))
                        | otherwise = annotate (AnnName n Nothing Nothing) (text (strName n))
  where strName (UN n) = T.unpack n
        strName (NS n ns) | showNS    = (concatMap (++ ".") . map T.unpack . reverse) ns ++ strName n
                          | otherwise = strName n
        strName (MN i s) = T.unpack s
        strName other = show other


showCImp :: Bool -> PClause -> Doc OutputAnnotation
showCImp impl (PClause _ n l ws r w)
 = prettyImp impl l <+> showWs ws <+> text "=" <+> prettyImp impl r
             <+> text "where" <+> text (show w)
  where
    showWs [] = empty
    showWs (x : xs) = text "|" <+> prettyImp impl x <+> showWs xs
showCImp impl (PWith _ n l ws r w)
 = prettyImp impl l <+> showWs ws <+> text "with" <+> prettyImp impl r
                 <+> braces (text (show w))
  where
    showWs [] = empty
    showWs (x : xs) = text "|" <+> prettyImp impl x <+> showWs xs


showDImp :: Bool -> PData -> Doc OutputAnnotation
showDImp impl (PDatadecl n ty cons)
 = text "data" <+> text (show n) <+> colon <+> prettyImp impl ty <+> text "where" <$>
    (indent 2 $ vsep (map (\ (_, n, t, _, _) -> pipe <+> prettyName False [] n <+> colon <+> prettyImp impl t) cons))

showDecls :: Bool -> [PDecl] -> Doc OutputAnnotation
showDecls i ds = vsep (map (showDeclImp i) ds)

showDeclImp _ (PFix _ f ops) = text (show f) <+> cat (punctuate (text ",") (map text ops))
showDeclImp i (PTy _ _ _ _ n t) = text "tydecl" <+> text (showCG n) <+> colon <+> prettyImp i t
showDeclImp i (PClauses _ _ n cs) = text "pat" <+> text (showCG n) <+> text "\t" <+>
                                      indent 2 (vsep (map (showCImp i) cs))
showDeclImp _ (PData _ _ _ _ d) = showDImp True d
showDeclImp i (PParams _ ns ps) = text "params" <+> braces (text (show ns) <> line <> showDecls i ps <> line)
showDeclImp i (PNamespace n ps) = text "namespace" <+> text n <> braces (line <> showDecls i ps <> line)
showDeclImp _ (PSyntax _ syn) = text "syntax" <+> text (show syn)
showDeclImp i (PClass _ _ _ cs n ps ds)
   = text "class" <+> text (show cs) <+> text (show n) <+> text (show ps) <> line <> showDecls i ds
showDeclImp i (PInstance _ _ cs n _ t _ ds)
   = text "instance" <+> text (show cs) <+> text (show n) <+> prettyImp i t <> line <> showDecls i ds
showDeclImp _ _ = text "..."
-- showDeclImp (PImport i) = "import " ++ i

instance Show (Doc OutputAnnotation) where
  show = flip (displayS . renderCompact) ""

getImps :: [PArg] -> [(Name, PTerm)]
getImps [] = []
getImps (PImp _ _ _ n tm _ : xs) = (n, tm) : getImps xs
getImps (_ : xs) = getImps xs

getExps :: [PArg] -> [PTerm]
getExps [] = []
getExps (PExp _ _ tm _ : xs) = tm : getExps xs
getExps (_ : xs) = getExps xs

getConsts :: [PArg] -> [PTerm]
getConsts [] = []
getConsts (PConstraint _ _ tm _ : xs) = tm : getConsts xs
getConsts (_ : xs) = getConsts xs

getAll :: [PArg] -> [PTerm]
getAll = map getTm


-- | Show Idris name
showName :: Maybe IState   -- ^^ the Idris state, for information about names and colours
         -> [(Name, Bool)] -- ^^ the bound variables and whether they're implicit
         -> Bool           -- ^^ whether to show implicits
         -> Bool           -- ^^ whether to colourise
         -> Name           -- ^^ the term to show
         -> String
showName ist bnd impl colour n = case ist of
                                   Just i -> if colour then colourise n (idris_colourTheme i) else showbasic n
                                   Nothing -> showbasic n
    where name = if impl then show n else showbasic n
          showbasic n@(UN _) = showCG n
          showbasic (MN _ s) = str s
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
showTm ist = displayDecorated (consoleDecorate ist) . renderCompact . prettyImp (opt_showimp (idris_options ist))

-- | Show a term with implicits, no colours
showTmImpls :: PTerm -> String
showTmImpls = flip (displayS . renderCompact . prettyImp True) ""


instance Sized PTerm where
  size (PQuote rawTerm) = size rawTerm
  size (PRef fc name) = size name
  size (PLam name ty bdy) = 1 + size ty + size bdy
  size (PPi plicity name ty bdy) = 1 + size ty + size bdy
  size (PLet name ty def bdy) = 1 + size ty + size def + size bdy
  size (PTyped trm ty) = 1 + size trm + size ty
  size (PApp fc name args) = 1 + size args
  size (PAppBind fc name args) = 1 + size args
  size (PCase fc trm bdy) = 1 + size trm + size bdy
  size (PTrue fc _) = 1
  size (PFalse fc) = 1
  size (PRefl fc _) = 1
  size (PResolveTC fc) = 1
  size (PEq fc left right) = 1 + size left + size right
  size (PRewrite fc left right _) = 1 + size left + size right
  size (PPair fc _ left right) = 1 + size left + size right
  size (PDPair fs left ty right) = 1 + size left + size ty + size right
  size (PAlternative a alts) = 1 + size alts
  size (PHidden hidden) = size hidden
  size (PUnifyLog tm) = size tm
  size (PDisamb _ tm) = size tm
  size (PNoImplicits tm) = size tm
  size PType = 1
  size (PConstant const) = 1 + size const
  size Placeholder = 1
  size (PDoBlock dos) = 1 + size dos
  size (PIdiom fc term) = 1 + size term
  size (PReturn fc) = 1
  size (PMetavar name) = 1
  size (PProof tactics) = size tactics
  size (PElabError err) = size err
  size PImpossible = 1

getPArity :: PTerm -> Int
getPArity (PPi _ _ _ sc) = 1 + getPArity sc
getPArity _ = 0

-- Return all names, free or globally bound, in the given term.

allNamesIn :: PTerm -> [Name]
allNamesIn tm = nub $ ni [] tm
  where
    ni env (PRef _ n)
        | not (n `elem` env) = [n]
    ni env (PPatvar _ n) = [n]
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PAppBind _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PCase _ c os)  = ni env c ++ concatMap (ni env) (map snd os)
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PHidden tm)    = ni env tm
    ni env (PEq _ l r)     = ni env l ++ ni env r
    ni env (PRewrite _ l r _) = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ (PRef _ n) t r)  = ni env t ++ ni (n:env) r
    ni env (PDPair _ l t r)  = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative a ls) = concatMap (ni env) ls
    ni env (PUnifyLog tm)    = ni env tm
    ni env (PDisamb _ tm)    = ni env tm
    ni env (PNoImplicits tm)    = ni env tm
    ni env _               = []

-- Return all names defined in binders in the given term
boundNamesIn :: PTerm -> [Name]
boundNamesIn tm = nub $ ni tm
  where
    ni (PApp _ f as)   = ni f ++ concatMap (ni) (map getTm as)
    ni (PAppBind _ f as)   = ni f ++ concatMap (ni) (map getTm as)
    ni (PCase _ c os)  = ni c ++ concatMap (ni) (map snd os)
    ni (PLam n ty sc)  = n : (ni ty ++ ni sc)
    ni (PLet n ty val sc)  = n : (ni ty ++ ni val ++ ni sc)
    ni (PPi _ n ty sc) = n : (ni ty ++ ni sc)
    ni (PEq _ l r)     = ni l ++ ni r
    ni (PRewrite _ l r _) = ni l ++ ni r
    ni (PTyped l r)    = ni l ++ ni r
    ni (PPair _ _ l r)   = ni l ++ ni r
    ni (PDPair _ (PRef _ n) t r) = ni t ++ ni r
    ni (PDPair _ l t r) = ni l ++ ni t ++ ni r
    ni (PAlternative a as) = concatMap (ni) as
    ni (PHidden tm)    = ni tm
    ni (PUnifyLog tm)    = ni tm
    ni (PDisamb _ tm)    = ni tm
    ni (PNoImplicits tm) = ni tm
    ni _               = []

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
    ni env (PCase _ c os)  = ni env c ++ concatMap (ni env) (map snd os)
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PEq _ l r)     = ni env l ++ ni env r
    ni env (PRewrite _ l r _) = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ (PRef _ n) t r) = ni env t ++ ni (n:env) r
    ni env (PDPair _ l t r) = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative a as) = concatMap (ni env) as
    ni env (PHidden tm)    = ni env tm
    ni env (PUnifyLog tm)    = ni env tm
    ni env (PDisamb _ tm)    = ni env tm
    ni env (PNoImplicits tm) = ni env tm
    ni env _               = []

-- Return which of the given names are used in the given term.

usedNamesIn :: [Name] -> IState -> PTerm -> [Name]
usedNamesIn vars ist tm = nub $ ni [] tm
  where
    ni env (PRef _ n)
        | n `elem` vars && not (n `elem` env)
            = case lookupTy n (tt_ctxt ist) of
                [] -> [n]
                _ -> []
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PAppBind _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PCase _ c os)  = ni env c ++ concatMap (ni env) (map snd os)
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PEq _ l r)     = ni env l ++ ni env r
    ni env (PRewrite _ l r _) = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ (PRef _ n) t r) = ni env t ++ ni (n:env) r
    ni env (PDPair _ l t r) = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative a as) = concatMap (ni env) as
    ni env (PHidden tm)    = ni env tm
    ni env (PUnifyLog tm)    = ni env tm
    ni env (PDisamb _ tm)    = ni env tm
    ni env (PNoImplicits tm) = ni env tm
    ni env _               = []


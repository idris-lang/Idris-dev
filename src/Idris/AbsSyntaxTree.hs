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

import Data.List
import Data.Char
import qualified Data.Text as T
import Data.Either
import Data.Word (Word)

import Debug.Trace

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
                         opt_cmdline    :: [Opt] -- remember whole command line
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
                      }

data LanguageExt = TypeProviders | ErrorReflection deriving (Show, Eq, Read, Ord)

-- | The output mode in use
data OutputMode = RawOutput | IdeSlave Integer deriving Show

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
    idris_errorhandlers :: [Name],
    idris_nameIdx :: (Int, Ctxt (Int, Name))
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
              | IBCCG Name
              | IBCDoc Name
              | IBCCoercion Name
              | IBCDef Name -- i.e. main context
              | IBCNameHint (Name, Name)
              | IBCLineApp FilePath Int PTerm
  deriving Show

-- | The initial state for the compiler
idrisInit :: IState
idrisInit = IState initContext [] [] emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext
                   emptyContext
                   [] [] defaultOpts 6 [] [] [] [] [] [] [] [] [] [] [] []
                   [] Nothing Nothing [] [] [] Hidden False [] Nothing [] [] RawOutput
                   True defaultTheme stdout [] (0, emptyContext)

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
           | PTrue FC
           | PFalse FC
           | PRefl FC PTerm
           | PResolveTC FC
           | PEq FC PTerm PTerm
           | PRewrite FC PTerm PTerm (Maybe PTerm)
           | PPair FC PTerm PTerm
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
  mpt (PPair fc l r) = PPair fc (mapPT f l) (mapPT f r)
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
                | Exact t | Compute | Trivial
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


--- Pretty printing declarations and terms

instance Show PTerm where
    show tm = showImp Nothing False False tm

instance Pretty PTerm where
  pretty = prettyImp False

instance Show PDecl where
    show d = showDeclImp False d

instance Show PClause where
    show c = showCImp True c

instance Show PData where
    show d = showDImp False d

showDecls :: Bool -> [PDecl] -> String
showDecls _ [] = ""
showDecls i (d:ds) = showDeclImp i d ++ "\n" ++ showDecls i ds

showDeclImp _ (PFix _ f ops) = show f ++ " " ++ showSep ", " ops
showDeclImp i (PTy _ _ _ _ n t) = "tydecl " ++ showCG n ++ " : " ++ showImp Nothing i False t
showDeclImp i (PClauses _ _ n cs) = "pat " ++ showCG n ++ "\t" ++ showSep "\n\t" (map (showCImp i) cs)
showDeclImp _ (PData _ _ _ _ d) = showDImp True d
showDeclImp i (PParams _ ns ps) = "params {" ++ show ns ++ "\n" ++ showDecls i ps ++ "}\n"
showDeclImp i (PNamespace n ps) = "namespace {" ++ n ++ "\n" ++ showDecls i ps ++ "}\n"
showDeclImp _ (PSyntax _ syn) = "syntax " ++ show syn
showDeclImp i (PClass _ _ _ cs n ps ds)
    = "class " ++ show cs ++ " " ++ show n ++ " " ++ show ps ++ "\n" ++ showDecls i ds
showDeclImp i (PInstance _ _ cs n _ t _ ds)
    = "instance " ++ show cs ++ " " ++ show n ++ " " ++ show t ++ "\n" ++ showDecls i ds
showDeclImp _ _ = "..."
-- showDeclImp (PImport i) = "import " ++ i


showCImp :: Bool -> PClause -> String
showCImp impl (PClause _ n l ws r w)
   = showImp Nothing impl False l ++ showWs ws ++ " = " ++ showImp Nothing impl False r
             ++ " where " ++ show w
  where
    showWs [] = ""
    showWs (x : xs) = " | " ++ showImp Nothing impl False x ++ showWs xs
showCImp impl (PWith _ n l ws r w)
   = showImp Nothing impl False l ++ showWs ws ++ " with " ++ showImp Nothing impl False r
             ++ " { " ++ show w ++ " } "
  where
    showWs [] = ""
    showWs (x : xs) = " | " ++ showImp Nothing impl False x ++ showWs xs


showDImp :: Bool -> PData -> String
showDImp impl (PDatadecl n ty cons)
   = "data " ++ show n ++ " : " ++ showImp Nothing impl False ty ++ " where\n\t"
     ++ showSep "\n\t| "
            (map (\ (_, n, t, _, _) -> show n ++ " : " ++ showImp Nothing impl False t) cons)

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

-- | Pretty-print a high-level Idris term
prettyImp :: Bool -- ^^ whether to show implicits
          -> PTerm -- ^^ the term to pretty-print
          -> Doc
prettyImp impl = prettySe 10
  where
    prettySe p (PQuote r) =
      if size r > breakingSize then
        text "![" $$ pretty r <> text "]"
      else
        text "![" <> pretty r <> text "]"
    prettySe p (PPatvar fc n) = pretty n
    prettySe p (PRef fc n) =
      if impl then
        pretty n
      else
        prettyBasic n
      where
        prettyBasic n@(UN _) = pretty n
        prettyBasic (MN _ s) = text (str s)
        prettyBasic (NS n s) = (foldr (<>) empty (intersperse (text ".") (map (text.str) $ reverse s))) <> prettyBasic n
        prettyBasic (SN sn) = text (show sn)
    prettySe p (PLam n ty sc) =
      bracket p 2 $
        if size sc > breakingSize then
          text "λ" <> pretty n <+> text "=>" $+$ pretty sc
        else
          text "λ" <> pretty n <+> text "=>" <+> pretty sc
    prettySe p (PLet n ty v sc) =
      bracket p 2 $
        if size sc > breakingSize then
          text "let" <+> pretty n <+> text "=" <+> prettySe 10 v <+> text "in" $+$
            nest nestingSize (prettySe 10 sc)
        else
          text "let" <+> pretty n <+> text "=" <+> prettySe 10 v <+> text "in" <+>
            prettySe 10 sc
    prettySe p (PPi (Exp l s _ _) n ty sc)
      | n `elem` allNamesIn sc || impl =
          let open = if Lazy `elem` l then text "|" <> lparen else lparen in
            bracket p 2 $
              if size sc > breakingSize then
                open <> pretty n <+> colon <+> prettySe 10 ty <> rparen <+>
                  st <+> text "->" $+$ prettySe 10 sc
              else
                open <> pretty n <+> colon <+> prettySe 10 ty <> rparen <+>
                  st <+> text "->" <+> prettySe 10 sc
      | otherwise                      =
          bracket p 2 $
            if size sc > breakingSize then
              prettySe 0 ty <+> st <+> text "->" $+$ prettySe 10 sc
            else
              prettySe 0 ty <+> st <+> text "->" <+> prettySe 10 sc
      where
        st =
          case s of
            Static -> text "[static]"
            _      -> empty
    prettySe p (PPi (Imp l s _ _) n ty sc)
      | impl =
          let open = if Lazy `elem` l then text "|" <> lbrace else lbrace in
            bracket p 2 $
              if size sc > breakingSize then
                open <> pretty n <+> colon <+> prettySe 10 ty <> rbrace <+>
                  st <+> text "->" <+> prettySe 10 sc
              else
                open <> pretty n <+> colon <+> prettySe 10 ty <> rbrace <+>
                  st <+> text "->" <+> prettySe 10 sc
      | otherwise = prettySe 10 sc
      where
        st =
          case s of
            Static -> text $ "[static]"
            _      -> empty
    prettySe p (PPi (Constraint _ _ _) n ty sc) =
      bracket p 2 $
        if size sc > breakingSize then
          prettySe 10 ty <+> text "=>" <+> prettySe 10 sc
        else
          prettySe 10 ty <+> text "=>" $+$ prettySe 10 sc
    prettySe p (PPi (TacImp _ _ s _) n ty sc) =
      bracket p 2 $
        if size sc > breakingSize then
          lbrace <> text "tacimp" <+> pretty n <+> colon <+> prettySe 10 ty <>
            rbrace <+> text "->" $+$ prettySe 10 sc
        else
          lbrace <> text "tacimp" <+> pretty n <+> colon <+> prettySe 10 ty <>
            rbrace <+> text "->" <+> prettySe 10 sc
    prettySe p (PApp _ (PRef _ f) [])
      | not impl = pretty f
    prettySe p (PAppBind _ (PRef _ f) [])
      | not impl = text "!" <+> pretty f
    prettySe p (PApp _ (PRef _ op@(UN nm)) args)
      | not (tnull nm) &&
        length (getExps args) == 2 && (not impl) && (not $ isAlpha (thead nm)) =
          let [l, r] = getExps args in
            bracket p 1 $
              if size r > breakingSize then
                prettySe 1 l <+> pretty op $+$ prettySe 0 r
              else
                prettySe 1 l <+> pretty op <+> prettySe 0 r
    prettySe p (PApp _ f as) =
      let args = getExps as in
        bracket p 1 $
          prettySe 1 f <+>
            if impl then
              foldl' fS empty as
              -- foldr (<+>) empty $ map prettyArgS as
            else
              foldl' fSe empty args
              -- foldr (<+>) empty $ map prettyArgSe args
      where
        fS l r =
          if size r > breakingSize then
            l $+$ nest nestingSize (prettyArgS r)
          else
            l <+> prettyArgS r

        fSe l r =
          if size r > breakingSize then
            l $+$ nest nestingSize (prettyArgSe r)
          else
            l <+> prettyArgSe r
    prettySe p (PCase _ scr opts) =
      text "case" <+> prettySe 10 scr <+> text "of" $+$ nest nestingSize prettyBody
      where
        prettyBody = foldr ($$) empty $ intersperse (text "|") $ map sc opts

        sc (l, r) = prettySe 10 l <+> text "=>" <+> prettySe 10 r
    prettySe p (PHidden tm) = text "." <> prettySe 0 tm
    prettySe p (PRefl _ _) = text "refl"
    prettySe p (PResolveTC _) = text "resolvetc"
    prettySe p (PTrue _) = text "()"
    prettySe p (PFalse _) = text "_|_"
    prettySe p (PEq _ l r) =
      bracket p 2 $
        if size r > breakingSize then
          prettySe 10 l <+> text "=" $$ nest nestingSize (prettySe 10 r)
        else
          prettySe 10 l <+> text "=" <+> prettySe 10 r
    prettySe p (PRewrite _ l r _) =
      bracket p 2 $
        if size r > breakingSize then
          text "rewrite" <+> prettySe 10 l <+> text "in" $$ nest nestingSize (prettySe 10 r)
        else
          text "rewrite" <+> prettySe 10 l <+> text "in" <+> prettySe 10 r
    prettySe p (PTyped l r) =
      lparen <> prettySe 10 l <+> colon <+> prettySe 10 r <> rparen
    prettySe p (PPair _ l r) =
      if size r > breakingSize then
        lparen <> prettySe 10 l <> text "," $+$
          prettySe 10 r <> rparen
      else
        lparen <> prettySe 10 l <> text "," <+> prettySe 10 r <> rparen
    prettySe p (PDPair _ l t r) =
      if size r > breakingSize then
        lparen <> prettySe 10 l <+> text "**" $+$
          prettySe 10 r <> rparen
      else
        lparen <> prettySe 10 l <+> text "**" <+> prettySe 10 r <> rparen
    prettySe p (PAlternative a as) =
      lparen <> text "|" <> prettyAs <> text "|" <> rparen
        where
          prettyAs =
            foldr (\l -> \r -> l <+> text "," <+> r) empty $ map (prettySe 10) as
    prettySe p PType = text "Type"
    prettySe p (PConstant c) = pretty c
    -- XXX: add pretty for tactics
    prettySe p (PProof ts) =
      text "proof" <+> lbrace $+$ nest nestingSize (text . show $ ts) $+$ rbrace
    prettySe p (PTactics ts) =
      text "tactics" <+> lbrace $+$ nest nestingSize (text . show $ ts) $+$ rbrace
    prettySe p (PMetavar n) = text "?" <> pretty n
    prettySe p (PReturn f) = text "return"
    prettySe p PImpossible = text "impossible"
    prettySe p Placeholder = text "_"
    prettySe p (PDoBlock _) = text "do block pretty not implemented"
    prettySe p (PElabError s) = pretty s

    prettySe p _ = text "test"

    prettyArgS (PImp _ _ _ n tm _) = prettyArgSi (n, tm)
    prettyArgS (PExp _ _ tm _)   = prettyArgSe tm
    prettyArgS (PConstraint _ _ tm _) = prettyArgSc tm
    prettyArgS (PTacImplicit _ _ n _ tm _) = prettyArgSti (n, tm)

    prettyArgSe arg = prettySe 0 arg
    prettyArgSi (n, val) = lbrace <> pretty n <+> text "=" <+> prettySe 10 val <> rbrace
    prettyArgSc val = lbrace <> lbrace <> prettySe 10 val <> rbrace <> rbrace
    prettyArgSti (n, val) = lbrace <> text "auto" <+> pretty n <+> text "=" <+> prettySe 10 val <> rbrace

    bracket outer inner doc
      | inner > outer = lparen <> doc <> rparen
      | otherwise     = doc

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

-- | Show Idris term
showImp :: Maybe IState -- ^^ the Idris state, for information about identifiers and colours
        -> Bool  -- ^^ whether to show implicits
        -> Bool  -- ^^ whether to colourise
        -> PTerm -- ^^ the term to show
        -> String
showImp ist impl colour tm = se 10 [] tm where
    perhapsColourise :: (ColourTheme -> String -> String) -> String -> String
    perhapsColourise col str = case ist of
                                 Just i -> if colour then col (idris_colourTheme i) str else str
                                 Nothing -> str

    se :: Int -> [(Name, Bool)] -> PTerm -> String
    se p bnd (PQuote r) = "![" ++ show r ++ "]"
    se p bnd (PPatvar fc n) = if impl then show n ++ "[p]" else show n
    se p bnd (PInferRef fc n) = "!" ++ show n -- ++ "[" ++ show fc ++ "]"
    se p bnd e
        | Just str <- slist p bnd e = str
        | Just num <- snat p e  = perhapsColourise colouriseData (show num)
    se p bnd (PRef fc n) = showName ist bnd impl colour n
    se p bnd (PLam n ty sc) = bracket p 2 $ "\\ " ++ perhapsColourise colouriseBound (show n) ++
                              (if impl then " : " ++ se 10 bnd ty else "") ++ " => "
                              ++ se 10 ((n, False):bnd) sc
    se p bnd (PLet n ty v sc) = bracket p 2 $ "let " ++ perhapsColourise colouriseBound (show n) ++
                                " = " ++ se 10 bnd v ++
                                " in " ++ se 10 ((n, False):bnd) sc
    se p bnd (PPi (Exp l s _ param) n ty sc)
        | n `elem` allNamesIn sc || impl
                                  = bracket p 2 $
                                    (if Lazy `elem` l then "|(" else "(") ++
                                    perhapsColourise colouriseBound (show n) ++ " : " ++ se 10 bnd ty ++
                                    ") " ++
                                    (if (impl && param) then "P" else "") ++
                                    st ++
                                    "-> " ++ se 10 ((n, False):bnd) sc
        | otherwise = bracket p 2 $ se 0 bnd ty ++ " " ++ st ++ "-> " ++ se 10 bnd sc
      where st = case s of
                    Static -> "[static] "
                    _ -> ""
    se p bnd (PPi (Imp l s _ _) n ty sc)
        | impl = bracket p 2 $ (if Lazy `elem` l then "|{" else "{") ++
                               perhapsColourise colouriseBound (show n) ++ " : " ++ se 10 bnd ty ++
                               "} " ++ st ++ "-> " ++ se 10 ((n, True):bnd) sc
        | otherwise = se 10 ((n, True):bnd) sc
      where st = case s of
                    Static -> "[static] "
                    _ -> ""
    se p bnd (PPi (Constraint _ _ _) n ty sc)
        = bracket p 2 $ se 10 bnd ty ++ " => " ++ se 10 bnd sc
    se p bnd (PPi (TacImp _ _ s _) n ty sc)
        = bracket p 2 $
          "{tacimp " ++ (perhapsColourise colouriseBound (show n)) ++ " : " ++ se 10 bnd ty ++ "} -> " ++
          se 10 ((n, False):bnd) sc
    se p bnd (PMatchApp _ f) = "match " ++ show f
    se p bnd (PApp _ hd@(PRef _ f) [])
        | not impl = se p bnd hd
    se p bnd (PAppBind _ hd@(PRef _ f) [])
        | not impl = "!" ++ se p bnd hd
    se p bnd (PApp _ op@(PRef _ (UN nm)) args)
        | not (tnull nm) &&
          length (getExps args) == 2 && not impl && not (isAlpha (thead nm))
            = let [l, r] = getExps args in
              bracket p 1 $ se 1 bnd l ++ " " ++ se p bnd op ++ " " ++ se 0 bnd r
    se p bnd (PApp _ f as)
        = -- let args = getExps as in
              bracket p 1 $ se 1 bnd f ++
                  if impl then concatMap (sArg bnd) as
                          else concatMap (suiArg impl bnd) as
    se p bnd (PAppBind _ f as)
        = let args = getExps as in
              "!" ++ (bracket p 1 $ se 1 bnd f ++ if impl then concatMap (sArg bnd) as
                                                         else concatMap (seArg bnd) args)
    se p bnd (PCase _ scr opts) = "case " ++ se 10 bnd scr ++ " of " ++ showSep " | " (map sc opts)
       where sc (l, r) = se 10 bnd l ++ " => " ++ se 10 bnd r
    se p bnd (PHidden tm) = "." ++ se 0 bnd tm
    se p bnd (PRefl _ t)
        | not impl = perhapsColourise colouriseData "refl"
        | otherwise = perhapsColourise colouriseData $ "refl {" ++ se 10 bnd t ++ "}"
    se p bnd (PResolveTC _) = "resolvetc"
    se p bnd (PTrue _) = perhapsColourise colouriseType "()"
    se p bnd (PFalse _) = perhapsColourise colouriseType "_|_"
    se p bnd (PEq _ l r) = bracket p 2 $ se 10 bnd l ++ perhapsColourise colouriseType " = " ++ se 10 bnd r
    se p bnd (PRewrite _ l r _) = bracket p 2 $ "rewrite " ++ se 10 bnd l ++ " in " ++ se 10 bnd r
    se p bnd (PTyped l r) = "(" ++ se 10 bnd l ++ " : " ++ se 10 bnd r ++ ")"
    se p bnd (PPair _ l r) = "(" ++ se 10 bnd l ++ ", " ++ se 10 bnd r ++ ")"
    se p bnd (PDPair _ l t r) = "(" ++ se 10 bnd l ++ " ** " ++ se 10 bnd r ++ ")"
    se p bnd (PAlternative a as) = "(|" ++ showSep " , " (map (se 10 bnd) as) ++ "|)"
    se p bnd PType = perhapsColourise colouriseType "Type"
    se p bnd (PConstant c) = perhapsColourise (cfun c) (show c)
        where cfun (AType _) = colouriseType
              cfun StrType   = colouriseType
              cfun PtrType   = colouriseType
              cfun VoidType  = colouriseType
              cfun _         = colouriseData
    se p bnd (PProof ts) = "proof { " ++ show ts ++ "}"
    se p bnd (PTactics ts) = "tactics { " ++ show ts ++ "}"
    se p bnd (PMetavar n) = "?" ++ show n
    se p bnd (PReturn f) = "return"
    se p bnd PImpossible = "impossible"
    se p bnd Placeholder = "_"
    se p bnd (PDoBlock _) = "do block show not implemented"
    se p bnd (PElabError s) = show s
    se p bnd (PCoerced t) = se p bnd t
    se p bnd (PUnifyLog t) = "%unifyLog " ++ se p bnd t
    se p bnd (PDisamb ns t) = "%disamb " ++ show ns ++ se p bnd t
    se p bnd (PNoImplicits t) = "%noimplicit " ++ se p bnd t
--     se p bnd x = "Not implemented"

    slist' p bnd (PApp _ (PRef _ nil) _)
      | not impl && nsroot nil == sUN "Nil" = Just []
    slist' p bnd (PApp _ (PRef _ cons) args)
      | nsroot cons == sUN "::",
        (PExp {getTm=tl}):(PExp {getTm=hd}):imps <- reverse args,
        all isImp imps,
        Just tl' <- slist' p bnd tl
      = Just (hd:tl')
      where
        isImp (PImp {}) = True
        isImp _         = False
    slist' _ _ _ = Nothing

    slist p bnd e | Just es <- slist' p bnd e = Just $
      case es of []  -> "[]"
                 [x] -> "[" ++ se p bnd x ++ "]"
                 xs  -> "[" ++ intercalate "," (map (se p bnd ) xs) ++ "]"
    slist _ _ _ = Nothing

    -- since Prelude is always imported, S & Z are unqualified iff they're the
    -- Nat ones.
    snat p (PRef _ o)
      | show o == (natns++"Z") || show o == "Z" = Just 0
    snat p (PApp _ s [PExp {getTm=n}])
      | show s == (natns++"S") || show s == "S",
        Just n' <- snat p n
      = Just $ 1 + n'
    snat _ _ = Nothing

    natns = "Prelude.Nat."

    sArg bnd (PImp _ _ _ n tm _) = siArg bnd (n, tm)
    sArg bnd (PExp _ _ tm _) = seArg bnd tm
    sArg bnd (PConstraint _ _ tm _) = scArg bnd tm
    sArg bnd (PTacImplicit _ _ n _ tm _) = stiArg bnd (n, tm)

    -- show argument, implicits given by the user also shown
    suiArg impl bnd (PImp _ mi _ n tm _)
        | impl || not mi = siArg bnd (n, tm)
    suiArg impl bnd (PExp _ _ tm _) = seArg bnd tm
    suiArg impl bnd _ = ""

    seArg bnd arg      = " " ++ se 0 bnd arg
    siArg bnd (n, val) =
        let n' = show n
            val' = se 10 bnd val in
            if (n' == val')
               then " {" ++ n' ++ "}"
               else " {" ++ n' ++ " = " ++ val' ++ "}"
    scArg bnd val = " {{" ++ se 10 bnd val ++ "}}"
    stiArg bnd (n, val) = " {auto " ++ show n ++ " = " ++ se 10 bnd val ++ "}"

    bracket outer inner str | inner > outer = "(" ++ str ++ ")"
                            | otherwise = str


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
  size (PTrue fc) = 1
  size (PFalse fc) = 1
  size (PRefl fc _) = 1
  size (PResolveTC fc) = 1
  size (PEq fc left right) = 1 + size left + size right
  size (PRewrite fc left right _) = 1 + size left + size right
  size (PPair fc left right) = 1 + size left + size right
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
    ni env (PPair _ l r)   = ni env l ++ ni env r
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
    ni (PPair _ l r)   = ni l ++ ni r
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
    ni env (PPair _ l r)   = ni env l ++ ni env r
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
    ni env (PPair _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ (PRef _ n) t r) = ni env t ++ ni (n:env) r
    ni env (PDPair _ l t r) = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative a as) = concatMap (ni env) as
    ni env (PHidden tm)    = ni env tm
    ni env (PUnifyLog tm)    = ni env tm
    ni env (PDisamb _ tm)    = ni env tm
    ni env (PNoImplicits tm) = ni env tm
    ni env _               = []


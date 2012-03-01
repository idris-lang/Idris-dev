{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             TypeSynonymInstances, PatternGuards #-}

module Idris.AbsSyntax where

import Core.TT
import Core.Evaluate
import Core.Elaborate hiding (Tactic(..))
import Core.Typecheck

import System.Console.Haskeline

import Control.Monad.State

import Data.List
import Data.Char
import Data.Either

import Debug.Trace

import qualified Epic.Epic as E

import Util.Pretty

data IOption = IOption { opt_logLevel :: Int,
                         opt_typecase :: Bool,
                         opt_typeintype :: Bool,
                         opt_coverage :: Bool,
                         opt_showimp  :: Bool,
                         opt_repl     :: Bool,
                         opt_verbose  :: Bool
                       }
    deriving (Show, Eq)

defaultOpts = IOption 0 False False True False True True

-- TODO: Add 'module data' to IState, which can be saved out and reloaded quickly (i.e
-- without typechecking).
-- This will include all the functions and data declarations, plus fixity declarations
-- and syntax macros.

data IState = IState { tt_ctxt :: Context,
                       idris_constraints :: [(UConstraint, FC)],
                       idris_infixes :: [FixDecl],
                       idris_implicits :: Ctxt [PArg],
                       idris_statics :: Ctxt [Bool],
                       idris_classes :: Ctxt ClassInfo,
                       idris_dsls :: Ctxt DSL,
                       idris_optimisation :: Ctxt OptInfo, 
                       idris_datatypes :: Ctxt TypeInfo,
                       idris_patdefs :: Ctxt [(Term, Term)], -- not exported
                       idris_flags :: Ctxt [FnOpt],
                       idris_callgraph :: Ctxt [Name],
                       idris_totcheck :: [(FC, Name)],
                       idris_log :: String,
                       idris_options :: IOption,
                       idris_name :: Int,
                       idris_metavars :: [Name],
                       syntax_rules :: [Syntax],
                       syntax_keywords :: [String],
                       imported :: [FilePath],
                       idris_prims :: [(Name, ([E.Name], E.Term))],
                       idris_objs :: [FilePath],
                       idris_libs :: [String],
                       idris_hdrs :: [String],
                       last_proof :: Maybe (Name, [String]),
                       errLine :: Maybe Int,
                       lastParse :: Maybe Name, 
                       indent_stack :: [Int],
                       brace_stack :: [Maybe Int],
                       hide_list :: [(Name, Maybe Accessibility)],
                       default_access :: Accessibility,
                       ibc_write :: [IBCWrite],
                       compiled_so :: Maybe String
                     }
             
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
              | IBCObj FilePath
              | IBCLib String
              | IBCHeader String
              | IBCAccess Name Accessibility
              | IBCTotal Name Totality
              | IBCFlags Name [FnOpt]
              | IBCCG Name
              | IBCDef Name -- i.e. main context
  deriving Show

idrisInit = IState initContext [] [] emptyContext emptyContext emptyContext
                   emptyContext emptyContext emptyContext emptyContext 
                   emptyContext emptyContext
                   [] "" defaultOpts 6 [] [] [] [] [] [] [] [] 
                   Nothing Nothing Nothing [] [] [] Hidden [] Nothing

-- The monad for the main REPL - reading and processing files and updating 
-- global state (hence the IO inner monad).
type Idris = StateT IState (InputT IO)

getContext :: Idris Context
getContext = do i <- get; return (tt_ctxt i)

getObjectFiles :: Idris [FilePath]
getObjectFiles = do i <- get; return (idris_objs i)

addObjectFile :: FilePath -> Idris ()
addObjectFile f = do i <- get; put (i { idris_objs = f : idris_objs i })

getLibs :: Idris [String]
getLibs = do i <- get; return (idris_libs i)

addLib :: String -> Idris ()
addLib f = do i <- get; put (i { idris_libs = f : idris_libs i })

addHdr :: String -> Idris ()
addHdr f = do i <- get; put (i { idris_hdrs = f : idris_hdrs i })

totcheck :: (FC, Name) -> Idris ()
totcheck n = do i <- get; put (i { idris_totcheck = n : idris_totcheck i })

setFlags :: Name -> [FnOpt] -> Idris ()
setFlags n fs = do i <- get; put (i { idris_flags = addDef n fs (idris_flags i) }) 

setAccessibility :: Name -> Accessibility -> Idris ()
setAccessibility n a 
         = do i <- get
              let ctxt = setAccess n a (tt_ctxt i)
              put (i { tt_ctxt = ctxt })

setTotality :: Name -> Totality -> Idris ()
setTotality n a 
         = do i <- get
              let ctxt = setTotal n a (tt_ctxt i)
              put (i { tt_ctxt = ctxt })

getTotality :: Name -> Idris Totality
getTotality n  
         = do i <- get
              case lookupTotal n (tt_ctxt i) of
                [t] -> return t
                _ -> return (Total [])

addToCG :: Name -> [Name] -> Idris ()
addToCG n ns = do i <- get
                  put (i { idris_callgraph = addDef n ns (idris_callgraph i) })

-- Add a class instance function. Dodgy hack: Put integer instances first in the
-- list so they are resolved by default.

addInstance :: Bool -> Name -> Name -> Idris ()
addInstance int n i 
    = do ist <- get
         case lookupCtxt Nothing n (idris_classes ist) of
                [CI a b c d ins] ->
                     do let cs = addDef n (CI a b c d (addI i ins)) (idris_classes ist)
                        put (ist { idris_classes = cs })
                _ -> do let cs = addDef n (CI (MN 0 "none") [] [] [] [i]) (idris_classes ist)
                        put (ist { idris_classes = cs })
  where addI i ins | int = i : ins
                   | otherwise = ins ++ [i]

addClass :: Name -> ClassInfo -> Idris ()
addClass n i 
   = do ist <- get
        let i' = case lookupCtxt Nothing n (idris_classes ist) of
                      [c] -> c { class_instances = class_instances i }
                      _ -> i
        put (ist { idris_classes = addDef n i' (idris_classes ist) }) 

addIBC :: IBCWrite -> Idris ()
addIBC ibc@(IBCDef n) 
           = do i <- get
                when (notDef (ibc_write i)) $
                  put (i { ibc_write = ibc : ibc_write i })
   where notDef [] = True
         notDef (IBCDef n': is) | n == n' = False
         notDef (_ : is) = notDef is
addIBC ibc = do i <- get; put (i { ibc_write = ibc : ibc_write i }) 

clearIBC :: Idris ()
clearIBC = do i <- get; put (i { ibc_write = [] })

getHdrs :: Idris [String]
getHdrs = do i <- get; return (idris_hdrs i)

setErrLine :: Int -> Idris ()
setErrLine x = do i <- get;
                  case (errLine i) of
                      Nothing -> put (i { errLine = Just x })
                      Just _ -> return ()

clearErr :: Idris ()
clearErr = do i <- get
              put (i { errLine = Nothing })

getSO :: Idris (Maybe String)
getSO = do i <- get
           return (compiled_so i)

setSO :: Maybe String -> Idris ()
setSO s = do i <- get
             put (i { compiled_so = s })

getIState :: Idris IState
getIState = get

putIState :: IState -> Idris ()
putIState = put

getName :: Idris Int
getName = do i <- get;
             let idx = idris_name i;
             put (i { idris_name = idx + 1 })
             return idx

checkUndefined :: FC -> Name -> Idris ()
checkUndefined fc n 
    = do i <- getContext
         case lookupTy Nothing n i of
             (_:_)  -> fail $ show fc ++ ":" ++ 
                       show n ++ " already defined"
             _ -> return ()

setContext :: Context -> Idris ()
setContext ctxt = do i <- get; put (i { tt_ctxt = ctxt } )

updateContext :: (Context -> Context) -> Idris ()
updateContext f = do i <- get; put (i { tt_ctxt = f (tt_ctxt i) } )

addConstraints :: FC -> (Int, [UConstraint]) -> Idris ()
addConstraints fc (v, cs)
    = do i <- get
         let ctxt = tt_ctxt i
         let ctxt' = ctxt { uconstraints = cs ++ uconstraints ctxt,
                            next_tvar = v }
         let ics = zip cs (repeat fc) ++ idris_constraints i
         put (i { tt_ctxt = ctxt', idris_constraints = ics })

addDeferred :: [(Name, Type)] -> Idris ()
addDeferred ns = do mapM_ (\(n, t) -> updateContext (addTyDecl n (tidyNames [] t))) ns
                    i <- get
                    put (i { idris_metavars = map fst ns ++ idris_metavars i })
  where tidyNames used (Bind (MN i x) b sc)
            = let n' = uniqueName (UN x) used in
                  Bind n' b $ tidyNames (n':used) sc
        tidyNames used (Bind n b sc)
            = let n' = uniqueName n used in
                  Bind n' b $ tidyNames (n':used) sc
        tidyNames used b = b

solveDeferred :: Name -> Idris ()
solveDeferred n = do i <- get
                     put (i { idris_metavars = idris_metavars i \\ [n] })

iputStrLn :: String -> Idris ()
iputStrLn = liftIO . putStrLn

iWarn :: FC -> String -> Idris ()
iWarn fc err = liftIO $ putStrLn (show fc ++ ":" ++ err)

setLogLevel :: Int -> Idris ()
setLogLevel l = do i <- get
                   let opts = idris_options i
                   let opt' = opts { opt_logLevel = l }
                   put (i { idris_options = opt' } )

logLevel :: Idris Int
logLevel = do i <- get
              return (opt_logLevel (idris_options i))

useREPL :: Idris Bool
useREPL = do i <- get
             return (opt_repl (idris_options i))

setREPL :: Bool -> Idris ()
setREPL t = do i <- get
               let opts = idris_options i
               let opt' = opts { opt_repl = t }
               put (i { idris_options = opt' })

verbose :: Idris Bool
verbose = do i <- get
             return (opt_verbose (idris_options i))

setVerbose :: Bool -> Idris ()
setVerbose t = do i <- get
                  let opts = idris_options i
                  let opt' = opts { opt_verbose = t }
                  put (i { idris_options = opt' })

typeInType :: Idris Bool
typeInType = do i <- get
                return (opt_typeintype (idris_options i))

setTypeInType :: Bool -> Idris ()
setTypeInType t = do i <- get
                     let opts = idris_options i
                     let opt' = opts { opt_typeintype = t }
                     put (i { idris_options = opt' })

coverage :: Idris Bool
coverage = do i <- get
              return (opt_coverage (idris_options i))

setCoverage :: Bool -> Idris ()
setCoverage t = do i <- get
                   let opts = idris_options i
                   let opt' = opts { opt_coverage = t }
                   put (i { idris_options = opt' })

impShow :: Idris Bool
impShow = do i <- get
             return (opt_showimp (idris_options i))

setImpShow :: Bool -> Idris ()
setImpShow t = do i <- get
                  let opts = idris_options i
                  let opt' = opts { opt_showimp = t }
                  put (i { idris_options = opt' })

logLvl :: Int -> String -> Idris ()
logLvl l str = do i <- get
                  let lvl = opt_logLevel (idris_options i)
                  when (lvl >= l)
                      $ do liftIO (putStrLn str)
                           put (i { idris_log = idris_log i ++ str ++ "\n" } )

iLOG :: String -> Idris ()
iLOG = logLvl 1

noErrors :: Idris Bool
noErrors = do i <- get
              case errLine i of
                Nothing -> return True
                _       -> return False

setTypeCase :: Bool -> Idris ()
setTypeCase t = do i <- get
                   let opts = idris_options i
                   let opt' = opts { opt_typecase = t }
                   put (i { idris_options = opt' })

-- Commands in the REPL

data Command = Quit | Help | Eval PTerm | Check PTerm | TotCheck Name
             | Reload | Edit
             | Compile String | Execute | ExecVal PTerm
             | Metavars | Prove Name | AddProof | Universes
             | TTShell 
             | LogLvl Int | Spec PTerm | HNF PTerm | Defn Name | Info Name
             | NOP

-- Parsed declarations

data Fixity = Infixl { prec :: Int } 
            | Infixr { prec :: Int }
            | InfixN { prec :: Int } 
            | PrefixN { prec :: Int }
    deriving Eq
{-! 
deriving instance Binary Fixity 
!-}

instance Show Fixity where
    show (Infixl i) = "infixl " ++ show i
    show (Infixr i) = "infixr " ++ show i
    show (InfixN i) = "infix " ++ show i
    show (PrefixN i) = "prefix " ++ show i

data FixDecl = Fix Fixity String 
    deriving (Show, Eq)
{-! 
deriving instance Binary FixDecl 
!-}

instance Ord FixDecl where
    compare (Fix x _) (Fix y _) = compare (prec x) (prec y)


data Static = Static | Dynamic
  deriving (Show, Eq)
{-! 
deriving instance Binary Static 
!-}

-- Mark bindings with their explicitness, and laziness
data Plicity = Imp { plazy :: Bool,
                     pstatic :: Static }
             | Exp { plazy :: Bool,
                     pstatic :: Static }
             | Constraint { plazy :: Bool,
                            pstatic :: Static }
             | TacImp { plazy :: Bool,
                        pstatic :: Static,
                        pscript :: PTerm }
  deriving (Show, Eq)

{-!
deriving instance Binary Plicity 
!-}

impl = Imp False Dynamic
expl = Exp False Dynamic
constraint = Constraint False Dynamic
tacimpl = TacImp False Dynamic

data FnOpt = Inlinable | TotalFn | AssertTotal | TCGen
           | Specialise [Name] -- specialise it, freeze these names
    deriving (Show, Eq)
{-!
deriving instance Binary FnOpt
!-}

type FnOpts = [FnOpt]

inlinable :: FnOpts -> Bool
inlinable = elem Inlinable

data PDecl' t = PFix     FC Fixity [String] -- fixity declaration
              | PTy      SyntaxInfo FC FnOpts Name t   -- type declaration
              | PClauses FC FnOpts Name [PClause' t]   -- pattern clause
              | PData    SyntaxInfo FC (PData' t)      -- data declaration
              | PParams  FC [(Name, t)] [PDecl' t] -- params block
              | PNamespace String [PDecl' t] -- new namespace
              | PRecord  SyntaxInfo FC Name t Name t     -- record declaration
              | PClass   SyntaxInfo FC 
                         [t] -- constraints
                         Name
                         [(Name, t)] -- parameters
                         [PDecl' t] -- declarations
              | PInstance SyntaxInfo FC [t] -- constraints
                                        Name -- class
                                        [t] -- parameters
                                        t -- full instance type
                                        [PDecl' t]
              | PDSL     Name (DSL' t)
              | PSyntax  FC Syntax
              | PDirective (Idris ())
    deriving Functor

data PClause' t = PClause  FC Name t [t] t [PDecl' t]
                | PWith    FC Name t [t] t [PDecl' t]
                | PClauseR FC        [t] t [PDecl' t]
                | PWithR   FC        [t] t [PDecl' t]
    deriving Functor

data PData' t  = PDatadecl { d_name :: Name,
                             d_tcon :: t,
                             d_cons :: [(Name, t, FC)] }
    deriving Functor

-- Handy to get a free function for applying PTerm -> PTerm functions
-- across a program, by deriving Functor

type PDecl   = PDecl' PTerm
type PData   = PData' PTerm
type PClause = PClause' PTerm 

-- get all the names declared in a decl

declared :: PDecl -> [Name]
declared (PFix _ _ _) = []
declared (PTy _ _ _ n t) = [n]
declared (PClauses _ _ n _) = [] -- not a declaration
declared (PData _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (a, _, _) = a
declared (PParams _ _ ds) = concatMap declared ds
declared (PNamespace _ ds) = concatMap declared ds
-- declared (PImport _) = []

defined :: PDecl -> [Name]
defined (PFix _ _ _) = []
defined (PTy _ _ _ n t) = []
defined (PClauses _ _ n _) = [n] -- not a declaration
defined (PData _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (a, _, _) = a
defined (PParams _ _ ds) = concatMap defined ds
defined (PNamespace _ ds) = concatMap defined ds
-- declared (PImport _) = []

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

-- High level language terms

data PTerm = PQuote Raw
           | PRef FC Name
           | PLam Name PTerm PTerm
           | PPi  Plicity Name PTerm PTerm
           | PLet Name PTerm PTerm PTerm 
           | PTyped PTerm PTerm -- term with explicit type
           | PApp FC PTerm [PArg]
           | PCase FC PTerm [(PTerm, PTerm)]
           | PTrue FC
           | PFalse FC
           | PRefl FC
           | PResolveTC FC
           | PEq FC PTerm PTerm
           | PPair FC PTerm PTerm
           | PDPair FC PTerm PTerm PTerm
           | PAlternative [PTerm]
           | PHidden PTerm -- irrelevant or hidden pattern
           | PSet
           | PConstant Const
           | Placeholder
           | PDoBlock [PDo]
           | PIdiom FC PTerm
           | PReturn FC
           | PMetavar Name
           | PProof [PTactic]
           | PTactics [PTactic] -- as PProof, but no auto solving
           | PElabError Err -- error to report on elaboration
           | PImpossible -- special case for declaring when an LHS can't typecheck
    deriving Eq
{-! 
deriving instance Binary PTerm 
!-}

mapPT :: (PTerm -> PTerm) -> PTerm -> PTerm
mapPT f t = f (mpt t) where
  mpt (PLam n t s) = PLam n (mapPT f t) (mapPT f s)
  mpt (PPi p n t s) = PPi p n (mapPT f t) (mapPT f s)
  mpt (PLet n ty v s) = PLet n (mapPT f ty) (mapPT f v) (mapPT f s)
  mpt (PApp fc t as) = PApp fc (mapPT f t) (map (fmap (mapPT f)) as)
  mpt (PCase fc c os) = PCase fc (mapPT f c) (map (pmap (mapPT f)) os)
  mpt (PEq fc l r) = PEq fc (mapPT f l) (mapPT f r)
  mpt (PTyped l r) = PTyped (mapPT f l) (mapPT f r)
  mpt (PPair fc l r) = PPair fc (mapPT f l) (mapPT f r)
  mpt (PDPair fc l t r) = PDPair fc (mapPT f l) (mapPT f t) (mapPT f r)
  mpt (PAlternative as) = PAlternative (map (mapPT f) as)
  mpt (PHidden t) = PHidden (mapPT f t)
  mpt (PDoBlock ds) = PDoBlock (map (fmap (mapPT f)) ds)
  mpt (PProof ts) = PProof (map (fmap (mapPT f)) ts)
  mpt (PTactics ts) = PTactics (map (fmap (mapPT f)) ts)
  mpt x = x


data PTactic' t = Intro [Name] | Intros | Focus Name
                | Refine Name [Bool] | Rewrite t | LetTac Name t
                | Exact t | Compute | Trivial
                | Solve
                | Attack
                | ProofState | ProofTerm | Undo
                | Try (PTactic' t) (PTactic' t)
                | TSeq (PTactic' t) (PTactic' t)
                | Qed | Abandon
    deriving (Show, Eq, Functor)
{-! 
deriving instance Binary PTactic' 
!-}

instance Sized a => Sized (PTactic' a) where
  size (Intro nms) = 1 + size nms
  size Intros = 1
  size (Focus nm) = 1 + size nm
  size (Refine nm bs) = 1 + size nm + length bs
  size (Rewrite t) = 1 + size t
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
                      lazyarg :: Bool, pname :: Name, getTm :: t }
             | PExp { priority :: Int,
                      lazyarg :: Bool, getTm :: t }
             | PConstraint { priority :: Int,
                             lazyarg :: Bool, getTm :: t }
             | PTacImplicit { priority :: Int,
                              lazyarg :: Bool, pname :: Name, 
                              getScript :: t,
                              getTm :: t }
    deriving (Show, Eq, Functor)

instance Sized a => Sized (PArg' a) where
  size (PImp p l nm trm) = 1 + size nm + size trm
  size (PExp p l trm) = 1 + size trm
  size (PConstraint p l trm) = 1 + size trm
  size (PTacImplicit p l nm scr trm) = 1 + size nm + size scr + size trm

{-! 
deriving instance Binary PArg' 
!-}

pimp = PImp 0 True
pexp = PExp 0 False
pconst = PConstraint 0 False
ptacimp = PTacImplicit 0 True

type PArg = PArg' PTerm

-- Type class data

data ClassInfo = CI { instanceName :: Name,
                      class_methods :: [(Name, (FnOpts, PTerm))],
                      class_defaults :: [(Name, Name)], -- method name -> default impl
                      class_params :: [Name],
                      class_instances :: [Name] }
    deriving Show
{-! 
deriving instance Binary ClassInfo 
!-}

data OptInfo = Optimise { collapsible :: Bool,
                          forceable :: [Int], -- argument positions
                          recursive :: [Int] }
    deriving Show
{-! 
deriving instance Binary OptInfo 
!-}


data TypeInfo = TI { con_names :: [Name] }
    deriving Show
{-!
deriving instance Binary TypeInfo
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
!-}

type DSL = DSL' PTerm

data SynContext = PatternSyntax | TermSyntax | AnySyntax
    deriving Show
{-! 
deriving instance Binary SynContext 
!-}

data Syntax = Rule [SSymbol] PTerm SynContext
    deriving Show
{-! 
deriving instance Binary Syntax 
!-}

data SSymbol = Keyword Name
             | Symbol String
             | Expr Name
             | SimpleExpr Name
    deriving Show
{-! 
deriving instance Binary SSymbol 
!-}

initDSL = DSL (PRef f (UN ">>=")) 
              (PRef f (UN "return"))
              (PRef f (UN "<$>"))
              (PRef f (UN "pure"))
              Nothing
              Nothing
              Nothing
              Nothing
              Nothing
  where f = FC "(builtin)" 0

data SyntaxInfo = Syn { using :: [(Name, PTerm)],
                        syn_params :: [(Name, PTerm)],
                        syn_namespace :: [String],
                        no_imp :: [Name],
                        decoration :: Name -> Name,
                        inPattern :: Bool,
                        dsl_info :: DSL }
    deriving Show

defaultSyntax = Syn [] [] [] [] id False initDSL

expandNS :: SyntaxInfo -> Name -> Name
expandNS syn n@(NS _ _) = n
expandNS syn n = case syn_namespace syn of
                        [] -> n
                        xs -> NS n xs


--- Pretty printing declarations and terms

instance Show PTerm where
    show tm = showImp False tm

instance Pretty PTerm where
  pretty = prettyImp False

instance Show PDecl where
    show d = showDeclImp False d

instance Show PClause where
    show c = showCImp True c

instance Show PData where
    show d = showDImp False d

showDeclImp _ (PFix _ f ops) = show f ++ " " ++ showSep ", " ops
showDeclImp t (PTy _ _ _ n ty) = show n ++ " : " ++ showImp t ty
showDeclImp _ (PClauses _ _ n c) = showSep "\n" (map show c)
showDeclImp _ (PData _ _ d) = show d

showCImp :: Bool -> PClause -> String
showCImp impl (PClause _ n l ws r w) 
   = showImp impl l ++ showWs ws ++ " = " ++ showImp impl r
             ++ " where " ++ show w 
  where
    showWs [] = ""
    showWs (x : xs) = " | " ++ showImp impl x ++ showWs xs
showCImp impl (PWith _ n l ws r w) 
   = showImp impl l ++ showWs ws ++ " with " ++ showImp impl r
             ++ " { " ++ show w ++ " } " 
  where
    showWs [] = ""
    showWs (x : xs) = " | " ++ showImp impl x ++ showWs xs


showDImp :: Bool -> PData -> String
showDImp impl (PDatadecl n ty cons) 
   = "data " ++ show n ++ " : " ++ showImp impl ty ++ " where\n\t"
     ++ showSep "\n\t| " 
            (map (\ (n, t, _) -> show n ++ " : " ++ showImp impl t) cons)

getImps :: [PArg] -> [(Name, PTerm)]
getImps [] = []
getImps (PImp _ _ n tm : xs) = (n, tm) : getImps xs
getImps (_ : xs) = getImps xs

getExps :: [PArg] -> [PTerm]
getExps [] = []
getExps (PExp _ _ tm : xs) = tm : getExps xs
getExps (_ : xs) = getExps xs

getConsts :: [PArg] -> [PTerm]
getConsts [] = []
getConsts (PConstraint _ _ tm : xs) = tm : getConsts xs
getConsts (_ : xs) = getConsts xs

getAll :: [PArg] -> [PTerm]
getAll = map getTm 

prettyImp :: Bool -> PTerm -> Doc
prettyImp impl = prettySe 10
  where
    prettySe p (PQuote r) =
      if size r > breakingSize then
        text "![" $$ pretty r <> text "]"
      else
        text "![" <> pretty r <> text "]"
    prettySe p (PRef fc n) =
      if impl then
        pretty n
      else
        prettyBasic n
      where
        prettyBasic n@(UN _) = pretty n
        prettyBasic (MN _ s) = text s
        prettyBasic (NS n s) = (foldr (<>) empty (intersperse (text ".") (map text $ reverse s))) <> prettyBasic n
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
    prettySe p (PPi (Exp l s) n ty sc)
      | n `elem` allNamesIn sc || impl =
          let open = if l then text "|" <> lparen else lparen in
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
    prettySe p (PPi (Imp l s) n ty sc)
      | impl =
          let open = if l then text "|" <> lbrace else lbrace in
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
    prettySe p (PPi (Constraint _ _) n ty sc) =
      bracket p 2 $
        if size sc > breakingSize then
          prettySe 10 ty <+> text "=>" <+> prettySe 10 sc
        else
          prettySe 10 ty <+> text "=>" $+$ prettySe 10 sc
    prettySe p (PPi (TacImp _ _ s) n ty sc) =
      bracket p 2 $
        if size sc > breakingSize then
          lbrace <> text "tacimp" <+> pretty n <+> colon <+> prettySe 10 ty <>
            rbrace <+> text "->" $+$ prettySe 10 sc
        else
          lbrace <> text "tacimp" <+> pretty n <+> colon <+> prettySe 10 ty <>
            rbrace <+> text "->" <+> prettySe 10 sc
    prettySe p (PApp _ (PRef _ f) [])
      | not impl = pretty f
    prettySe p (PApp _ (PRef _ op@(UN (f:_))) args)
      | length (getExps args) == 2 && (not impl) && (not $ isAlpha f) =
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
              foldl fS empty as
              -- foldr (<+>) empty $ map prettyArgS as
            else
              foldl fSe empty args
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
    prettySe p (PRefl _) = text "refl"
    prettySe p (PResolveTC _) = text "resolvetc"
    prettySe p (PTrue _) = text "()"
    prettySe p (PFalse _) = text "_|_"
    prettySe p (PEq _ l r) =
      bracket p 2 $
        if size r > breakingSize then
          prettySe 10 l <+> text "=" $$ nest nestingSize (prettySe 10 r)
        else
          prettySe 10 l <+> text "=" <+> prettySe 10 r
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
    prettySe p (PAlternative as) =
      lparen <> text "|" <> prettyAs <> text "|" <> rparen
        where
          prettyAs =
            foldr (\l -> \r -> l <+> text "," <+> r) empty $ map (prettySe 10) as
    prettySe p PSet = text "Set"
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

    prettyArgS (PImp _ _ n tm) = prettyArgSi (n, tm)
    prettyArgS (PExp _ _ tm)   = prettyArgSe tm
    prettyArgS (PConstraint _ _ tm) = prettyArgSc tm
    prettyArgS (PTacImplicit _ _ n _ tm) = prettyArgSti (n, tm)

    prettyArgSe arg = prettySe 0 arg
    prettyArgSi (n, val) = lbrace <> pretty n <+> text "=" <+> prettySe 10 val <> rbrace
    prettyArgSc val = lbrace <> lbrace <> prettySe 10 val <> rbrace <> rbrace
    prettyArgSti (n, val) = lbrace <> text "auto" <+> pretty n <+> text "=" <+> prettySe 10 val <> rbrace

    bracket outer inner doc
      | inner > outer = lparen <> doc <> rparen
      | otherwise     = doc
        
showImp :: Bool -> PTerm -> String
showImp impl tm = se 10 tm where
    se p (PQuote r) = "![" ++ show r ++ "]"
    se p (PRef fc n) = if impl then show n -- ++ "[" ++ show fc ++ "]"
                               else showbasic n
      where showbasic n@(UN _) = show n
            showbasic (MN _ s) = s
            showbasic (NS n s) = showSep "." (reverse s) ++ "." ++ showbasic n
    se p (PLam n ty sc) = bracket p 2 $ "\\ " ++ show n ++ " => " ++ show sc
    se p (PLet n ty v sc) = bracket p 2 $ "let " ++ show n ++ " = " ++ se 10 v ++
                            " in " ++ se 10 sc 
    se p (PPi (Exp l s) n ty sc)
        | n `elem` allNamesIn sc || impl
                                  = bracket p 2 $
                                    if l then "|(" else "(" ++ 
                                    show n ++ " : " ++ se 10 ty ++ 
                                    ") " ++ st ++
                                    "-> " ++ se 10 sc
        | otherwise = bracket p 2 $ se 0 ty ++ " " ++ st ++ "-> " ++ se 10 sc
      where st = case s of
                    Static -> "[static] "
                    _ -> ""
    se p (PPi (Imp l s) n ty sc)
        | impl = bracket p 2 $ if l then "|{" else "{" ++ 
                               show n ++ " : " ++ se 10 ty ++ 
                               "} " ++ st ++ "-> " ++ se 10 sc
        | otherwise = se 10 sc
      where st = case s of
                    Static -> "[static] "
                    _ -> ""
    se p (PPi (Constraint _ _) n ty sc)
        = bracket p 2 $ se 10 ty ++ " => " ++ se 10 sc
    se p (PPi (TacImp _ _ s) n ty sc)
        = bracket p 2 $ "{tacimp " ++ show n ++ " : " ++ se 10 ty ++ "} -> " ++ se 10 sc
    se p (PApp _ (PRef _ f) [])
        | not impl = show f
    se p (PApp _ (PRef _ op@(UN (f:_))) args)
        | length (getExps args) == 2 && not impl && not (isAlpha f) 
            = let [l, r] = getExps args in
              bracket p 1 $ se 1 l ++ " " ++ show op ++ " " ++ se 0 r
    se p (PApp _ f as) 
        = let args = getExps as in
              bracket p 1 $ se 1 f ++ if impl then concatMap sArg as
                                              else concatMap seArg args
    se p (PCase _ scr opts) = "case " ++ se 10 scr ++ " of " ++ showSep " | " (map sc opts)
       where sc (l, r) = se 10 l ++ " => " ++ se 10 r
    se p (PHidden tm) = "." ++ se 0 tm
    se p (PRefl _) = "refl"
    se p (PResolveTC _) = "resolvetc"
    se p (PTrue _) = "()"
    se p (PFalse _) = "_|_"
    se p (PEq _ l r) = bracket p 2 $ se 10 l ++ " = " ++ se 10 r
    se p (PTyped l r) = "(" ++ se 10 l ++ " : " ++ se 10 r ++ ")"
    se p (PPair _ l r) = "(" ++ se 10 l ++ ", " ++ se 10 r ++ ")"
    se p (PDPair _ l t r) = "(" ++ se 10 l ++ " ** " ++ se 10 r ++ ")"
    se p (PAlternative as) = "(|" ++ showSep " , " (map (se 10) as) ++ "|)"
    se p PSet = "Set"
    se p (PConstant c) = show c
    se p (PProof ts) = "proof { " ++ show ts ++ "}"
    se p (PTactics ts) = "tactics { " ++ show ts ++ "}"
    se p (PMetavar n) = "?" ++ show n
    se p (PReturn f) = "return"
    se p PImpossible = "impossible"
    se p Placeholder = "_"
    se p (PDoBlock _) = "do block show not implemented"
    se p (PElabError s) = show s
--     se p x = "Not implemented"

    sArg (PImp _ _ n tm) = siArg (n, tm)
    sArg (PExp _ _ tm) = seArg tm
    sArg (PConstraint _ _ tm) = scArg tm
    sArg (PTacImplicit _ _ n _ tm) = stiArg (n, tm)

    seArg arg      = " " ++ se 0 arg
    siArg (n, val) = " {" ++ show n ++ " = " ++ se 10 val ++ "}"
    scArg val = " {{" ++ se 10 val ++ "}}"
    stiArg (n, val) = " {auto " ++ show n ++ " = " ++ se 10 val ++ "}"

    bracket outer inner str | inner > outer = "(" ++ str ++ ")"
                            | otherwise = str

{-
 PQuote Raw
           | PRef FC Name
           | PLam Name PTerm PTerm
           | PPi  Plicity Name PTerm PTerm
           | PLet Name PTerm PTerm PTerm 
           | PTyped PTerm PTerm -- term with explicit type
           | PApp FC PTerm [PArg]
           | PCase FC PTerm [(PTerm, PTerm)]
           | PTrue FC
           | PFalse FC
           | PRefl FC
           | PResolveTC FC
           | PEq FC PTerm PTerm
           | PPair FC PTerm PTerm
           | PDPair FC PTerm PTerm PTerm
           | PAlternative [PTerm]
           | PHidden PTerm -- irrelevant or hidden pattern
           | PSet
           | PConstant Const
           | Placeholder
           | PDoBlock [PDo]
           | PIdiom FC PTerm
           | PReturn FC
           | PMetavar Name
           | PProof [PTactic]
           | PTactics [PTactic] -- as PProof, but no auto solving
           | PElabError Err -- error to report on elaboration
           | PImpossible -- special case for declaring when an LHS can't typecheck
-}

instance Sized PTerm where
  size (PQuote rawTerm) = size rawTerm
  size (PRef fc name) = size name
  size (PLam name ty bdy) = 1 + size ty + size bdy
  size (PPi plicity name ty bdy) = 1 + size ty + size bdy
  size (PLet name ty def bdy) = 1 + size ty + size def + size bdy
  size (PTyped trm ty) = 1 + size trm + size ty
  size (PApp fc name args) = 1 + size args
  size (PCase fc trm bdy) = 1 + size trm + size bdy
  size (PTrue fc) = 1
  size (PFalse fc) = 1
  size (PRefl fc) = 1
  size (PResolveTC fc) = 1
  size (PEq fc left right) = 1 + size left + size right
  size (PPair fc left right) = 1 + size left + size right
  size (PDPair fs left ty right) = 1 + size left + size ty + size right
  size (PAlternative alts) = 1 + size alts
  size (PHidden hidden) = size hidden
  size PSet = 1
  size (PConstant const) = 1 + size const
  size Placeholder = 1
  size (PDoBlock dos) = 1 + size dos
  size (PIdiom fc term) = 1 + size term
  size (PReturn fc) = 1
  size (PMetavar name) = 1
  size (PProof tactics) = size tactics
  size (PElabError err) = size err
  size PImpossible = 1

allNamesIn :: PTerm -> [Name]
allNamesIn tm = nub $ ni [] tm 
  where
    ni env (PRef _ n)        
        | not (n `elem` env) = [n]
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PCase _ c os)  = ni env c ++ concatMap (ni env) (map snd os)
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PHidden tm)    = ni env tm
    ni env (PEq _ l r)     = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ (PRef _ n) t r)  = ni env t ++ ni (n:env) r
    ni env (PDPair _ l t r)  = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative ls) = concatMap (ni env) ls
    ni env _               = []

namesIn :: [(Name, PTerm)] -> IState -> PTerm -> [Name]
namesIn uvars ist tm = nub $ ni [] tm 
  where
    ni env (PRef _ n)        
        | not (n `elem` env) 
            = case lookupTy Nothing n (tt_ctxt ist) of
                [] -> [n]
                _ -> if n `elem` (map fst uvars) then [n] else []
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PCase _ c os)  = ni env c ++ concatMap (ni env) (map snd os)
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PEq _ l r)     = ni env l ++ ni env r
    ni env (PTyped l r)    = ni env l ++ ni env r
    ni env (PPair _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ (PRef _ n) t r) = ni env t ++ ni (n:env) r
    ni env (PDPair _ l t r) = ni env l ++ ni env t ++ ni env r
    ni env (PAlternative as) = concatMap (ni env) as
    ni env (PHidden tm)    = ni env tm
    ni env _               = []

-- For inferring types of things

bi = FC "builtin" 0

inferTy   = MN 0 "__Infer"
inferCon  = MN 0 "__infer"
inferDecl = PDatadecl inferTy 
                      PSet
                      [(inferCon, PPi impl (MN 0 "A") PSet (
                                  PPi expl (MN 0 "a") (PRef bi (MN 0 "A"))
                                  (PRef bi inferTy)), bi)]

infTerm t = PApp bi (PRef bi inferCon) [pimp (MN 0 "A") Placeholder, pexp t]
infP = P (TCon 6 0) inferTy (Set (UVal 0))

getInferTerm, getInferType :: Term -> Term
getInferTerm (Bind n b sc) = Bind n b $ getInferTerm sc
getInferTerm (App (App _ _) tm) = tm
getInferTerm tm = error ("getInferTerm " ++ show tm)

getInferType (Bind n b sc) = Bind n b $ getInferType sc
getInferType (App (App _ ty) _) = ty

-- Handy primitives: Unit, False, Pair, MkPair, =, mkForeign

primNames = [unitTy, unitCon,
             falseTy, pairTy, pairCon,
             eqTy, eqCon, inferTy, inferCon]

unitTy   = MN 0 "__Unit"
unitCon  = MN 0 "__II"
unitDecl = PDatadecl unitTy PSet
                     [(unitCon, PRef bi unitTy, bi)]

falseTy   = MN 0 "__False"
falseDecl = PDatadecl falseTy PSet []

pairTy    = MN 0 "__Pair"
pairCon   = MN 0 "__MkPair"
pairDecl  = PDatadecl pairTy (piBind [(n "A", PSet), (n "B", PSet)] PSet)
            [(pairCon, PPi impl (n "A") PSet (
                       PPi impl (n "B") PSet (
                       PPi expl (n "a") (PRef bi (n "A")) (
                       PPi expl (n "b") (PRef bi (n "B"))  
                           (PApp bi (PRef bi pairTy) [pexp (PRef bi (n "A")),
                                                pexp (PRef bi (n "B"))])))), bi)]
    where n a = MN 0 a

eqTy = UN "="
eqCon = UN "refl"
eqDecl = PDatadecl eqTy (piBind [(n "a", PSet), (n "b", PSet),
                                 (n "x", PRef bi (n "a")), (n "y", PRef bi (n "b"))]
                                 PSet)
                [(eqCon, PPi impl (n "a") PSet (
                         PPi impl (n "x") (PRef bi (n "a"))
                           (PApp bi (PRef bi eqTy) [pimp (n "a") Placeholder,
                                                    pimp (n "b") Placeholder,
                                                    pexp (PRef bi (n "x")),
                                                    pexp (PRef bi (n "x"))])), bi)]
    where n a = MN 0 a

-- Defined in builtins.idr
sigmaTy   = UN "Exists"
existsCon = UN "Ex_intro"

piBind :: [(Name, PTerm)] -> PTerm -> PTerm
piBind [] t = t
piBind ((n, ty):ns) t = PPi expl n ty (piBind ns t)
    
tcname (UN ('@':_)) = True
tcname (NS n _) = tcname n
tcname _ = False

-- Dealing with parameters

expandParams :: (Name -> Name) -> [(Name, PTerm)] -> [Name] -> PTerm -> PTerm
expandParams dec ps ns tm = en tm
  where
    -- if we shadow a name (say in a lambda binding) that is used in a call to
    -- a lifted function, we need access to both names - once in the scope of the
    -- binding and once to call the lifted functions. So we'll explicitly shadow
    -- it. (Yes, it's a hack. The alternative would be to resolve names earlier
    -- but we didn't...)
    
    mkShadow (UN n) = MN 0 n
    mkShadow (MN i n) = MN (i+1) n
    mkShadow (NS x s) = NS (mkShadow x) s

    en (PLam n t s)
       | n `elem` map fst ps
               = let n' = mkShadow n in
                     PLam n' (en t) (en (shadow n n' s))
       | otherwise = PLam n (en t) (en s)
    en (PPi p n t s) 
       | n `elem` map fst ps
               = let n' = mkShadow n in
                     PPi p n' (en t) (en (shadow n n' s))
       | otherwise = PPi p n (en t) (en s)
    en (PLet n ty v s) 
       | n `elem` map fst ps
               = let n' = mkShadow n in
                     PLet n' (en ty) (en v) (en (shadow n n' s))
       | otherwise = PLet n (en ty) (en v) (en s)
    en (PEq f l r) = PEq f (en l) (en r)
    en (PTyped l r) = PTyped (en l) (en r)
    en (PPair f l r) = PPair f (en l) (en r)
    en (PDPair f l t r) = PDPair f (en l) (en t) (en r)
    en (PAlternative as) = PAlternative (map en as)
    en (PHidden t) = PHidden (en t)
    en (PDoBlock ds) = PDoBlock (map (fmap en) ds)
    en (PProof ts)   = PProof (map (fmap en) ts)
    en (PTactics ts) = PTactics (map (fmap en) ts)

    en (PQuote (Var n)) 
        | n `elem` ns = PQuote (Var (dec n))
    en (PApp fc (PRef fc' n) as)
        | n `elem` ns = PApp fc (PRef fc' (dec n)) 
                           (map (pexp . (PRef fc)) (map fst ps) ++ (map (fmap en) as))
    en (PRef fc n)
        | n `elem` ns = PApp fc (PRef fc (dec n)) 
                           (map (pexp . (PRef fc)) (map fst ps))
    en (PApp fc f as) = PApp fc (en f) (map (fmap en) as)
    en (PCase fc c os) = PCase fc (en c) (map (pmap en) os)
    en t = t

expandParamsD :: IState -> 
                 (Name -> Name) -> [(Name, PTerm)] -> [Name] -> PDecl -> PDecl
expandParamsD ist dec ps ns (PTy syn fc o n ty) 
    = if n `elem` ns
         then PTy syn fc o (dec n) (piBind ps (expandParams dec ps ns ty))
         else PTy syn fc o n (expandParams dec ps ns ty)
expandParamsD ist dec ps ns (PClauses fc opts n cs)
    = let n' = if n `elem` ns then dec n else n in
          PClauses fc opts n' (map expandParamsC cs)
  where
    expandParamsC (PClause fc n lhs ws rhs ds)
        = let -- ps' = updateps True (namesIn ist rhs) (zip ps [0..])
              ps'' = updateps False (namesIn [] ist lhs) (zip ps [0..])
              n' = if n `elem` ns then dec n else n in
              PClause fc n' (expandParams dec ps'' ns lhs)
                            (map (expandParams dec ps'' ns) ws)
                            (expandParams dec ps'' ns rhs)
                            (map (expandParamsD ist dec ps'' ns) ds)
    expandParamsC (PWith fc n lhs ws wval ds)
        = let -- ps' = updateps True (namesIn ist wval) (zip ps [0..])
              ps'' = updateps False (namesIn [] ist lhs) (zip ps [0..])
              n' = if n `elem` ns then dec n else n in
              PWith fc n' (expandParams dec ps'' ns lhs)
                          (map (expandParams dec ps'' ns) ws)
                          (expandParams dec ps'' ns wval)
                          (map (expandParamsD ist dec ps'' ns) ds)
    updateps yn nm [] = []
    updateps yn nm (((a, t), i):as)
        | (a `elem` nm) == yn = (a, t) : updateps yn nm as
        | otherwise = (MN i (show n ++ "_u"), t) : updateps yn nm as

expandParamsD ist dec ps ns d = d

-- Calculate a priority for a type, for deciding elaboration order
-- * if it's just a type variable or concrete type, do it early (0)
-- * if there's only type variables and injective constructors, do it next (1)
-- * if there's a function type, next (2)
-- * finally, everything else (3)

getPriority :: IState -> PTerm -> Int
getPriority i tm = pri tm 
  where
    pri (PRef _ n) =
        case lookupP Nothing n (tt_ctxt i) of
            ((P (DCon _ _) _ _):_) -> 1
            ((P (TCon _ _) _ _):_) -> 1
            ((P Ref _ _):_) -> 4
            [] -> 0 -- must be locally bound, if it's not an error...
    pri (PPi _ _ x y) = max 5 (max (pri x) (pri y))
    pri (PTrue _) = 0
    pri (PFalse _) = 0
    pri (PRefl _) = 1
    pri (PEq _ l r) = max 1 (max (pri l) (pri r))
    pri (PApp _ f as) = max 1 (max (pri f) (foldr max 0 (map (pri.getTm) as))) 
    pri (PCase _ f as) = max 1 (max (pri f) (foldr max 0 (map (pri.snd) as))) 
    pri (PTyped l r) = pri l
    pri (PPair _ l r) = max 1 (max (pri l) (pri r))
    pri (PDPair _ l t r) = max 1 (max (pri l) (max (pri t) (pri r)))
    pri (PAlternative as) = maximum (map pri as)
    pri (PConstant _) = 0
    pri Placeholder = 1
    pri _ = 3

addStatics :: Name -> Term -> PTerm -> Idris ()
addStatics n tm ptm =
    do let (statics, dynamics) = initStatics tm ptm
       let stnames = nub $ concatMap freeNames (map snd statics)
       let dnames = nub $ concatMap freeNames (map snd dynamics)
       when (not (null statics)) $
          logLvl 7 $ show n ++ " " ++ show statics ++ "\n" ++ show dynamics
                        ++ "\n" ++ show stnames ++ "\n" ++ show dnames
       let statics' = nub $ map fst statics ++ 
                              filter (\x -> not (elem x dnames)) stnames
       let stpos = staticList statics' tm
       i <- get
       put (i { idris_statics = addDef n stpos (idris_statics i) })
       addIBC (IBCStatic n)
  where
    initStatics (Bind n (Pi ty) sc) (PPi p _ _ s)
            = let (static, dynamic) = initStatics (instantiate (P Bound n ty) sc) s in
                  if pstatic p == Static then ((n, ty) : static, dynamic)
                                         else (static, (n, ty) : dynamic)
    initStatics t pt = ([], [])

    staticList sts (Bind n (Pi _) sc) = (n `elem` sts) : staticList sts sc
    staticList _ _ = []

-- Dealing with implicit arguments

-- Add implicit Pi bindings for any names in the term which appear in an
-- argument position.

-- This has become a right mess already. Better redo it some time...

implicit :: SyntaxInfo -> Name -> PTerm -> Idris PTerm
implicit syn n ptm 
    = do i <- get
         let (tm', impdata) = implicitise syn i ptm
--          let (tm'', spos) = findStatics i tm'
         put (i { idris_implicits = addDef n impdata (idris_implicits i) })
         addIBC (IBCImp n)
         logLvl 5 ("Implicit " ++ show n ++ " " ++ show impdata)
--          i <- get
--          put (i { idris_statics = addDef n spos (idris_statics i) })
         return tm'

implicitise :: SyntaxInfo -> IState -> PTerm -> (PTerm, [PArg])
implicitise syn ist tm
    = let (declimps, ns') = execState (imps True [] tm) ([], []) 
          ns = ns' \\ (map fst pvars ++ no_imp syn) in
          if null ns 
            then (tm, reverse declimps) 
            else implicitise syn ist (pibind uvars ns tm)
  where
    uvars = using syn
    pvars = syn_params syn

    dropAll (x:xs) ys | x `elem` ys = dropAll xs ys
                      | otherwise   = x : dropAll xs ys
    dropAll [] ys = []

    imps top env (PApp _ f as)
       = do (decls, ns) <- get
            let isn = concatMap (namesIn uvars ist) (map getTm as)
            put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PPi (Imp l _) n ty sc) 
        = do let isn = nub (namesIn uvars ist ty) `dropAll` [n]
             (decls , ns) <- get
             put (PImp (getPriority ist ty) l n ty : decls, 
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (Exp l _) n ty sc) 
        = do let isn = nub (namesIn uvars ist ty ++ case sc of
                            (PRef _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PExp (getPriority ist ty) l ty : decls, 
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (Constraint l _) n ty sc)
        = do let isn = nub (namesIn uvars ist ty ++ case sc of
                            (PRef _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PConstraint 10 l ty : decls, 
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (TacImp l _ scr) n ty sc)
        = do let isn = nub (namesIn uvars ist ty ++ case sc of
                            (PRef _ x) -> namesIn uvars ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PTacImplicit 10 l n scr ty : decls, 
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PEq _ l r)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PTyped l r)
        = imps top env l
    imps top env (PPair _ l r)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ (PRef _ n) t r)
        = do (decls, ns) <- get
             let isn = nub (namesIn uvars ist t ++ namesIn uvars ist r) \\ [n]
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ l t r)
        = do (decls, ns) <- get
             let isn = namesIn uvars ist l ++ namesIn uvars ist t ++ 
                       namesIn uvars ist r
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PAlternative as)
        = do (decls, ns) <- get
             let isn = concatMap (namesIn uvars ist) as
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PLam n ty sc)  
        = do imps False env ty
             imps False (n:env) sc
    imps top env (PHidden tm)    = imps False env tm
    imps top env _               = return ()

    pibind using []     sc = sc
    pibind using (n:ns) sc 
      = case lookup n using of
            Just ty -> PPi (Imp False Dynamic) n ty (pibind using ns sc)
            Nothing -> PPi (Imp False Dynamic) n Placeholder (pibind using ns sc)

-- Add implicit arguments in function calls
addImplPat :: IState -> PTerm -> PTerm
addImplPat = addImpl' True []

addImplBound :: IState -> [Name] -> PTerm -> PTerm
addImplBound ist ns = addImpl' False ns ist

addImpl :: IState -> PTerm -> PTerm
addImpl = addImpl' False []

-- TODO: in patterns, don't add implicits to function names guarded by constructors
-- and *not* inside a PHidden

addImpl' :: Bool -> [Name] -> IState -> PTerm -> PTerm
addImpl' inpat env ist ptm = ai env ptm
  where
    ai env (PRef fc f)    
        | not (f `elem` env) = handleErr $ aiFn inpat ist fc f []
    ai env (PHidden (PRef fc f))
        | not (f `elem` env) = handleErr $ aiFn False ist fc f []
    ai env (PEq fc l r)   = let l' = ai env l
                                r' = ai env r in
                                PEq fc l' r'
    ai env (PTyped l r) = let l' = ai env l
                              r' = ai env r in
                              PTyped l' r'
    ai env (PPair fc l r) = let l' = ai env l
                                r' = ai env r in
                                PPair fc l' r'
    ai env (PDPair fc l t r) = let l' = ai env l
                                   t' = ai env t
                                   r' = ai env r in
                                   PDPair fc l' t' r'
    ai env (PAlternative as) = let as' = map (ai env) as in
                                   PAlternative as'
    ai env (PApp fc (PRef _ f) as) 
        | not (f `elem` env)
                          = let as' = map (fmap (ai env)) as in
                                handleErr $ aiFn False ist fc f as'
    ai env (PApp fc f as) = let f' = ai env f
                                as' = map (fmap (ai env)) as in
                                mkPApp fc 1 f' as'
    ai env (PCase fc c os) = let c' = ai env c
                                 os' = map (pmap (ai env)) os in
                                 PCase fc c' os'
    ai env (PLam n ty sc) = let ty' = ai env ty
                                sc' = ai (n:env) sc in
                                PLam n ty' sc'
    ai env (PLet n ty val sc)
                          = let ty' = ai env ty
                                val' = ai env val
                                sc' = ai (n:env) sc in
                                PLet n ty' val' sc'
    ai env (PPi p n ty sc) = let ty' = ai env ty
                                 sc' = ai (n:env) sc in
                                 PPi p n ty' sc'
    ai env (PHidden tm) = PHidden (ai env tm)
    ai env (PProof ts) = PProof (map (fmap (ai env)) ts)
    ai env (PTactics ts) = PTactics (map (fmap (ai env)) ts)
    ai env tm = tm

    handleErr (Left err) = PElabError err
    handleErr (Right x) = x

-- if in a pattern, and there are no arguments, and there's no possible
-- names with zero explicit arguments, don't add implicits.

aiFn :: Bool -> IState -> FC -> Name -> [PArg] -> Either Err PTerm
aiFn True ist fc f []
  = case lookupCtxt Nothing f (idris_implicits ist) of
        [] -> Right $ PRef fc f
        alts -> if (any (all imp) alts)
                        then aiFn False ist fc f [] -- use it as a constructor
                        else Right $ PRef fc f
    where imp (PExp _ _ _) = False
          imp _ = True
aiFn inpat ist fc f as
    | f `elem` primNames = Right $ PApp fc (PRef fc f) as
aiFn inpat ist fc f as
          -- This is where namespaces get resolved by adding PAlternative
        = case lookupCtxtName Nothing f (idris_implicits ist) of
            [(f',ns)] -> Right $ mkPApp fc (length ns) (PRef fc f') (insertImpl ns as)
            [] -> if f `elem` idris_metavars ist
                    then Right $ PApp fc (PRef fc f) as
                    else Right $ mkPApp fc (length as) (PRef fc f) as
            alts -> Right $
                     PAlternative $
                       map (\(f', ns) -> mkPApp fc (length ns) (PRef fc f') 
                                                   (insertImpl ns as)) alts
  where
    insertImpl :: [PArg] -> [PArg] -> [PArg]
    insertImpl (PExp p l ty : ps) (PExp _ _ tm : given) =
                                 PExp p l tm : insertImpl ps given
    insertImpl (PConstraint p l ty : ps) (PConstraint _ _ tm : given) =
                                 PConstraint p l tm : insertImpl ps given
    insertImpl (PConstraint p l ty : ps) given =
                                 PConstraint p l (PResolveTC fc) : insertImpl ps given
    insertImpl (PImp p l n ty : ps) given =
        case find n given [] of
            Just (tm, given') -> PImp p l n tm : insertImpl ps given'
            Nothing ->           PImp p l n Placeholder : insertImpl ps given
    insertImpl (PTacImplicit p l n sc ty : ps) given =
        case find n given [] of
            Just (tm, given') -> PTacImplicit p l n sc tm : insertImpl ps given'
            Nothing ->           PTacImplicit p l n sc sc
                                    : insertImpl ps given
    insertImpl expected [] = []
    insertImpl _        given  = given

    find n []               acc = Nothing
    find n (PImp _ _ n' t : gs) acc 
         | n == n' = Just (t, reverse acc ++ gs)
    find n (g : gs) acc = find n gs (g : acc)

mkPApp fc a f [] = f
mkPApp fc a f as = let rest = drop a as in
                       appRest fc (PApp fc f (take a as)) rest
  where
    appRest fc f [] = f
    appRest fc f (a : as) = appRest fc (PApp fc f [a]) as

-- Find 'static' argument positions
-- (the declared ones, plus any names in argument position in the declared 
-- statics)
-- FIXME: It's possible that this really has to happen after elaboration

findStatics :: IState -> PTerm -> (PTerm, [Bool])
findStatics ist tm = trace (showImp True tm) $
                      let (ns, ss) = fs tm in
                         runState (pos ns ss tm) []
  where fs (PPi p n t sc)
            | Static <- pstatic p
                        = let (ns, ss) = fs sc in
                              (namesIn [] ist t : ns, n : ss)
            | otherwise = let (ns, ss) = fs sc in
                              (ns, ss)
        fs _ = ([], [])

        inOne n ns = length (filter id (map (elem n) ns)) == 1

        pos ns ss (PPi p n t sc) 
            | elem n ss = do sc' <- pos ns ss sc
                             spos <- get
                             put (True : spos)
                             return (PPi (p { pstatic = Static }) n t sc')
            | otherwise = do sc' <- pos ns ss sc
                             spos <- get
                             put (False : spos)
                             return (PPi p n t sc')
        pos ns ss t = return t

-- Debugging/logging stuff

dumpDecls :: [PDecl] -> String
dumpDecls [] = ""
dumpDecls (d:ds) = dumpDecl d ++ "\n" ++ dumpDecls ds

dumpDecl (PFix _ f ops) = show f ++ " " ++ showSep ", " ops 
dumpDecl (PTy _ _ _ n t) = "tydecl " ++ show n ++ " : " ++ showImp True t
dumpDecl (PClauses _ _ n cs) = "pat " ++ show n ++ "\t" ++ showSep "\n\t" (map (showCImp True) cs)
dumpDecl (PData _ _ d) = showDImp True d
dumpDecl (PParams _ ns ps) = "params {" ++ show ns ++ "\n" ++ dumpDecls ps ++ "}\n"
dumpDecl (PNamespace n ps) = "namespace {" ++ n ++ "\n" ++ dumpDecls ps ++ "}\n"
dumpDecl (PSyntax _ syn) = "syntax " ++ show syn
dumpDecl (PClass _ _ cs n ps ds) 
    = "class " ++ show cs ++ " " ++ show n ++ " " ++ show ps ++ "\n" ++ dumpDecls ds
dumpDecl (PInstance _ _ cs n _ t ds) 
    = "instance " ++ show cs ++ " " ++ show n ++ " " ++ show t ++ "\n" ++ dumpDecls ds
dumpDecl _ = "..."
-- dumpDecl (PImport i) = "import " ++ i

-- for 6.12/7 compatibility
data EitherErr a b = LeftErr a | RightOK b

instance Monad (EitherErr a) where
    return = RightOK

    (LeftErr e) >>= k = LeftErr e
    RightOK v   >>= k = k v

toEither (LeftErr e)  = Left e
toEither (RightOK ho) = Right ho

-- syntactic match of a against b, returning pair of variables in a 
-- and what they match. Returns the pair that failed if not a match.

matchClause :: IState -> PTerm -> PTerm -> Either (PTerm, PTerm) [(Name, PTerm)]
matchClause = matchClause' False

matchClause' :: Bool -> IState -> PTerm -> PTerm -> Either (PTerm, PTerm) [(Name, PTerm)]
matchClause' names i x y = checkRpts $ match (fullApp x) (fullApp y) where
    matchArg x y = match (fullApp (getTm x)) (fullApp (getTm y))

    fullApp (PApp _ (PApp fc f args) xs) = fullApp (PApp fc f (args ++ xs))
    fullApp x = x

    match' x y = match (fullApp x) (fullApp y)
    match (PApp _ (PRef _ (NS (UN "fromInteger") ["builtins"])) [_,_,x]) x' 
        | PConstant (I _) <- getTm x = match (getTm x) x'
    match x' (PApp _ (PRef _ (NS (UN "fromInteger") ["builtins"])) [_,_,x])
        | PConstant (I _) <- getTm x = match (getTm x) x'
    match (PApp _ (PRef _ (UN "lazy")) [_,x]) x' = match (getTm x) x'
    match x (PApp _ (PRef _ (UN "lazy")) [_,x']) = match x (getTm x')
    match (PApp _ f args) (PApp _ f' args')
        | length args == length args'
            = do mf <- match' f f'
                 ms <- zipWithM matchArg args args'
                 return (mf ++ concat ms)
--     match (PRef _ n) (PRef _ n') | n == n' = return []
--                                  | otherwise = Nothing
    match (PRef f n) (PApp _ x []) = match (PRef f n) x
    match (PApp _ x []) (PRef f n) = match x (PRef f n)
    match (PRef _ n) (PRef _ n') | n == n' = return []
    match (PRef _ n) tm 
        | not names && (not (isConName Nothing n (tt_ctxt i)) || tm == Placeholder)
            = return [(n, tm)]
    match (PEq _ l r) (PEq _ l' r') = do ml <- match' l l'
                                         mr <- match' r r'
                                         return (ml ++ mr)
    match (PTyped l r) (PTyped l' r') = do ml <- match l l'
                                           mr <- match r r'
                                           return (ml ++ mr)
    match (PTyped l r) x = match l x
    match x (PTyped l r) = match x l
    match (PPair _ l r) (PPair _ l' r') = do ml <- match' l l'
                                             mr <- match' r r'
                                             return (ml ++ mr)
    match (PDPair _ l t r) (PDPair _ l' t' r') = do ml <- match' l l'
                                                    mt <- match' t t'
                                                    mr <- match' r r'
                                                    return (ml ++ mt ++ mr)
    match (PAlternative as) (PAlternative as') 
        = do ms <- zipWithM match' as as' 
             return (concat ms)
    match a@(PAlternative as) b
        = do let ms = zipWith match' as (repeat b)
             case (rights (map toEither ms)) of
                (x: _) -> return x
                _ -> LeftErr (a, b)
    match (PCase _ _ _) _ = return [] -- lifted out
    match (PMetavar _) _ = return [] -- modified
    match (PQuote _) _ = return []
    match (PProof _) _ = return []
    match (PTactics _) _ = return []
    match (PRefl _) (PRefl _) = return []
    match (PResolveTC _) (PResolveTC _) = return []
    match (PTrue _) (PTrue _) = return []
    match (PFalse _) (PFalse _) = return []
    match (PReturn _) (PReturn _) = return []
    match (PPi _ _ t s) (PPi _ _ t' s') = do mt <- match' t t'
                                             ms <- match' s s'
                                             return (mt ++ ms)
    match (PLam _ t s) (PLam _ t' s') = do mt <- match' t t'
                                           ms <- match' s s'
                                           return (mt ++ ms)
    match (PLet _ t ty s) (PLet _ t' ty' s') = do mt <- match' t t'
                                                  mty <- match' ty ty'
                                                  ms <- match' s s'
                                                  return (mt ++ mty ++ ms)
    match (PHidden x) (PHidden y) = match' x y
    match Placeholder _ = return []
--     match _ Placeholder = return []
    match (PResolveTC _) _ = return []
    match a b | a == b = return []
              | otherwise = LeftErr (a, b)

    checkRpts (RightOK ms) = check ms where
        check ((n,t):xs) 
            | Just t' <- lookup n xs = if t/=t' && t/=Placeholder && t'/=Placeholder
                                                then Left (t, t') 
                                                else check xs
        check (_:xs) = check xs
        check [] = Right ms
    checkRpts (LeftErr x) = Left x

substMatches :: [(Name, PTerm)] -> PTerm -> PTerm
substMatches [] t = t
substMatches ((n,tm):ns) t = substMatch n tm (substMatches ns t)

substMatch :: Name -> PTerm -> PTerm -> PTerm
substMatch n tm t = sm t where
    sm (PRef _ n') | n == n' = tm
    sm (PLam x t sc) = PLam x (sm t) (sm sc)
    sm (PPi p x t sc) = PPi p x (sm t) (sm sc)
    sm (PApp f x as) = PApp f (sm x) (map (fmap sm) as)
    sm (PCase f x as) = PCase f (sm x) (map (pmap sm) as)
    sm (PEq f x y) = PEq f (sm x) (sm y)
    sm (PTyped x y) = PTyped (sm x) (sm y)
    sm (PPair f x y) = PPair f (sm x) (sm y)
    sm (PDPair f x t y) = PDPair f (sm x) (sm t) (sm y)
    sm (PAlternative as) = PAlternative (map sm as)
    sm (PHidden x) = PHidden (sm x)
    sm x = x

shadow :: Name -> Name -> PTerm -> PTerm
shadow n n' t = sm t where
    sm (PRef fc x) | n == x = PRef fc n'
    sm (PLam x t sc) = PLam x (sm t) (sm sc)
    sm (PPi p x t sc) = PPi p x (sm t) (sm sc)
    sm (PApp f x as) = PApp f (sm x) (map (fmap sm) as)
    sm (PCase f x as) = PCase f (sm x) (map (pmap sm) as)
    sm (PEq f x y) = PEq f (sm x) (sm y)
    sm (PTyped x y) = PTyped (sm x) (sm y)
    sm (PPair f x y) = PPair f (sm x) (sm y)
    sm (PDPair f x t y) = PDPair f (sm x) (sm t) (sm y)
    sm (PAlternative as) = PAlternative (map sm as)
    sm (PHidden x) = PHidden (sm x)
    sm x = x


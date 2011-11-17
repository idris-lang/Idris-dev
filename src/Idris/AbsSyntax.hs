{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             TypeSynonymInstances, PatternGuards #-}

module Idris.AbsSyntax where

import Core.TT
import Core.Evaluate
import Core.Elaborate
import Core.Typecheck

import Control.Monad.State
import Data.List
import Data.Char
import Debug.Trace

import qualified Epic.Epic as E

data IOption = IOption { opt_logLevel :: Int,
                         opt_typecase :: Bool 
                       }
    deriving (Show, Eq)

defaultOpts = IOption 0 False

-- TODO: Add 'module data' to IState, which can be saved out and reloaded quickly (i.e
-- without typechecking).
-- This will include all the functions and data declarations, plus fixity declarations
-- and syntax macros.

data IState = IState { tt_ctxt :: Context,
                       idris_infixes :: [FixDecl],
                       idris_implicits :: Ctxt [PArg],
                       idris_statics :: Ctxt [Bool],
                       idris_classes :: Ctxt ClassInfo,
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
                       errLine :: Maybe Int
                     }
                   
idrisInit = IState emptyContext [] emptyContext emptyContext emptyContext
                   "" defaultOpts 6 [] [] [] [] [] [] [] Nothing

-- The monad for the main REPL - reading and processing files and updating 
-- global state (hence the IO inner monad).
type Idris a = StateT IState IO a

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

setErrLine :: Int -> Idris ()
setErrLine x = do i <- get;
                  case (errLine i) of
                      Nothing -> put (i { errLine = Just x })
                      Just _ -> return ()

clearErr :: Idris ()
clearErr = do i <- get
              put (i { errLine = Nothing })

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
         case lookupCtxt n i of
             Just _ -> fail $ show fc ++ ":" ++ 
                       show n ++ " already defined"
             _ -> return ()

setContext :: Context -> Idris ()
setContext ctxt = do i <- get; put (i { tt_ctxt = ctxt } )

updateContext :: (Context -> Context) -> Idris ()
updateContext f = do i <- get; put (i { tt_ctxt = f (tt_ctxt i) } )

addDeferred :: [(Name, Type)] -> Idris ()
addDeferred ns = do mapM_ (\(n, t) -> updateContext (addTyDecl n (tidyNames [] t))) ns
                    i <- get
                    put (i { idris_metavars = map fst ns ++ idris_metavars i })
  where tidyNames used (Bind (MN i x) b sc)
            = let n' = uniqueName (UN [x]) used in
                  Bind n' b $ tidyNames (n':used) sc
        tidyNames used (Bind n b sc)
            = let n' = uniqueName n used in
                  Bind n' b $ tidyNames (n':used) sc
        tidyNames used b = b

solveDeferred :: Name -> Idris ()
solveDeferred n = do i <- get
                     put (i { idris_metavars = idris_metavars i \\ [n] })

iputStrLn :: String -> Idris ()
iputStrLn = lift.putStrLn

setLogLevel :: Int -> Idris ()
setLogLevel l = do i <- get
                   let opts = idris_options i
                   let opt' = opts { opt_logLevel = l }
                   put (i { idris_options = opt' } )

logLevel :: Idris Int
logLevel = do i <- get
              return (opt_logLevel (idris_options i))

logLvl :: Int -> String -> Idris ()
logLvl l str = do i <- get
                  let lvl = opt_logLevel (idris_options i)
                  when (lvl >= l)
                      $ do lift (putStrLn str)
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

data Command = Quit | Help | Eval PTerm | Check PTerm | Reload | Edit
             | Compile String | Execute String
             | Metavars | Prove Name
             | TTShell 
             | LogLvl Int | Spec PTerm | HNF PTerm | Defn Name
             | NOP

-- Parsed declarations

data Fixity = Infixl { prec :: Int } 
            | Infixr { prec :: Int }
            | InfixN { prec :: Int } 
            | PrefixN { prec :: Int }
    deriving Eq

instance Show Fixity where
    show (Infixl i) = "infixl " ++ show i
    show (Infixr i) = "infixr " ++ show i
    show (InfixN i) = "infix " ++ show i
    show (PrefixN i) = "prefix " ++ show i

data FixDecl = Fix Fixity String 
    deriving (Show, Eq)

instance Ord FixDecl where
    compare (Fix x _) (Fix y _) = compare (prec x) (prec y)


data Static = Static | Dynamic
  deriving (Show, Eq)

-- Mark bindings with their explicitness, and laziness
data Plicity = Imp { plazy :: Bool,
                     pstatic :: Static }
             | Exp { plazy :: Bool,
                     pstatic :: Static }
             | Constraint { plazy :: Bool,
                            pstatic :: Static }
  deriving (Show, Eq)

impl = Imp False Dynamic
expl = Exp False Dynamic
constraint = Constraint False Static

type FnOpts = Bool -- just inlinable, for now

inlinable :: FnOpts -> Bool
inlinable x = x

data PDecl' t = PFix     FC Fixity [String] -- fixity declaration
              | PTy      SyntaxInfo FC Name t          -- type declaration
              | PClauses FC FnOpts Name [PClause' t]   -- pattern clause
              | PData    SyntaxInfo FC (PData' t)      -- data declaration
              | PParams  FC [(Name, t)] [PDecl' t] -- params block
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
              | PSyntax  FC Syntax
              | PDirective (Idris ())
    deriving Functor

data PClause' t = PClause Name t [t] t [PDecl' t]
                | PWith   Name t [t] t [PDecl' t]
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
declared (PTy _ _ n t) = [n]
declared (PClauses _ _ n _) = [] -- not a declaration
declared (PData _ _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (a, _, _) = a
declared (PParams _ _ ds) = concatMap declared ds
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
           | PApp FC PTerm [PArg]
           | PTrue FC
           | PFalse FC
           | PRefl FC
           | PResolveTC FC
           | PEq FC PTerm PTerm
           | PPair FC PTerm PTerm
           | PDPair FC PTerm PTerm PTerm
           | PHidden PTerm -- irrelevant or hidden pattern
           | PSet
           | PConstant Const
           | Placeholder
           | PDoBlock [PDo]
           | PReturn FC
           | PMetavar Name
           | PProof [PTactic]
           | PTactics [PTactic] -- as PProof, but no auto solving
           | PElabError String -- error to report on elaboration
    deriving Eq

mapPT :: (PTerm -> PTerm) -> PTerm -> PTerm
mapPT f t = f (mpt t) where
  mpt (PLam n t s) = PLam n (mapPT f t) (mapPT f s)
  mpt (PPi p n t s) = PPi p n (mapPT f t) (mapPT f s)
  mpt (PLet n ty v s) = PLet n (mapPT f ty) (mapPT f v) (mapPT f s)
  mpt (PApp fc t as) = PApp fc (mapPT f t) (map (fmap (mapPT f)) as)
  mpt (PEq fc l r) = PEq fc (mapPT f l) (mapPT f r)
  mpt (PPair fc l r) = PPair fc (mapPT f l) (mapPT f r)
  mpt (PDPair fc l t r) = PDPair fc (mapPT f l) (mapPT f t) (mapPT f r)
  mpt (PHidden t) = PHidden (mapPT f t)
  mpt (PDoBlock ds) = PDoBlock (map (fmap (mapPT f)) ds)
  mpt (PProof ts) = PProof (map (fmap (mapPT f)) ts)
  mpt (PTactics ts) = PTactics (map (fmap (mapPT f)) ts)
  mpt x = x


data PTactic' t = Intro [Name] | Focus Name
                | Refine Name [Bool] | Rewrite t
                | Exact t | Compute | Trivial
                | Solve
                | Attack
                | ProofState | ProofTerm | Undo
                | Try (PTactic' t) (PTactic' t)
                | TSeq (PTactic' t) (PTactic' t)
                | Qed
    deriving (Show, Eq, Functor)

type PTactic = PTactic' PTerm

data PDo' t = DoExp  FC t
            | DoBind FC Name t
            | DoLet  FC Name t
    deriving (Eq, Functor)

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
    deriving (Show, Eq, Functor)

pimp = PImp 0 False
pexp = PExp 0 False
pconst = PConstraint 0 False

type PArg = PArg' PTerm

-- Type class data

data ClassInfo = CI { instanceName :: Name,
                      class_methods :: [(Name, PTerm)],
                      class_params :: [Name] }


-- Syntactic sugar info (TODO: namespaces, modules)

data DSL = DSL { dsl_bind :: Name,
                 dsl_return :: Name }
    deriving Show

data SynContext = PatternSyntax | TermSyntax | AnySyntax
    deriving Show

data Syntax = Rule [SSymbol] PTerm SynContext
    deriving Show

data SSymbol = Keyword Name
             | Symbol String
             | Expr Name
    deriving Show

initDSL = DSL (UN [">>="]) (UN ["return"])

data SyntaxInfo = Syn { using :: [(Name, PTerm)],
                        syn_params :: [(Name, PTerm)],
                        no_imp :: [Name],
                        decoration :: Name -> Name,
                        inPattern :: Bool,
                        dsl_info :: DSL }
    deriving Show

defaultSyntax = Syn [] [] [] id False initDSL

--- Pretty printing declarations and terms

instance Show PTerm where
    show tm = showImp False tm

instance Show PDecl where
    show (PFix _ f ops) = show f ++ " " ++ showSep ", " ops
    show (PTy _ _ n ty) = show n ++ " : " ++ show ty
    show (PClauses _ _ n c) = showSep "\n" (map show c)
    show (PData _ _ d) = show d

instance Show PClause where
    show c = showCImp True c

instance Show PData where
    show d = showDImp False d

showCImp :: Bool -> PClause -> String
showCImp impl (PClause n l ws r w) 
   = showImp impl l ++ showWs ws ++ " = " ++ showImp impl r
             ++ " where " ++ show w 
  where
    showWs [] = ""
    showWs (x : xs) = " | " ++ showImp impl x ++ showWs xs
showCImp impl (PWith n l ws r w) 
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

showImp :: Bool -> PTerm -> String
showImp impl tm = se 10 tm where
    se p (PQuote r) = "![" ++ show r ++ "]"
    se p (PRef _ n) = show n
    se p (PLam n ty sc) = bracket p 2 $ "\\ " ++ show n ++ " => " ++ show sc
    se p (PLet n ty v sc) = bracket p 2 $ "let " ++ show n ++ " = " ++ se 10 v ++
                            " in " ++ se 10 sc 
    se p (PPi (Exp l s) n ty sc)
        | n `elem` allNamesIn sc = bracket p 2 $
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
    se p (PApp _ (PRef _ f) [])
        | not impl = show f
    se p (PApp _ (PRef _ op@(UN [f:_])) args)
        | length (getExps args) == 2 && not impl && not (isAlpha f) 
            = let [l, r] = getExps args in
              bracket p 1 $ se 1 l ++ " " ++ show op ++ " " ++ se 0 r
    se p (PApp _ f as) 
        = let args = getExps as in
              bracket p 1 $ se 1 f ++ if impl then concatMap sArg as
                                              else concatMap seArg args
    se p (PHidden tm) = "." ++ se 0 tm
    se p (PRefl _) = "refl"
    se p (PResolveTC _) = "resolvetc"
    se p (PTrue _) = "()"
    se p (PFalse _) = "_|_"
    se p (PEq _ l r) = bracket p 2 $ se 10 l ++ " = " ++ se 10 r
    se p (PPair _ l r) = "(" ++ se 10 l ++ ", " ++ se 10 r ++ ")"
    se p (PDPair _ l t r) = "(" ++ se 10 l ++ " ** " ++ se 10 r ++ ")"
    se p PSet = "Set"
    se p (PConstant c) = show c
    se p (PProof ts) = "proof { " ++ show ts ++ "}"
    se p (PTactics ts) = "tactics { " ++ show ts ++ "}"
    se p (PMetavar n) = "?" ++ show n
    se p Placeholder = "_"

    sArg (PImp _ _ n tm) = siArg (n, tm)
    sArg (PExp _ _ tm) = seArg tm
    sArg (PConstraint _ _ tm) = scArg tm

    seArg arg      = " " ++ se 0 arg
    siArg (n, val) = " {" ++ show n ++ " = " ++ se 10 val ++ "}"
    scArg val = " {{" ++ se 10 val ++ "}}"

    bracket outer inner str | inner > outer = "(" ++ str ++ ")"
                            | otherwise = str

allNamesIn :: PTerm -> [Name]
allNamesIn tm = nub $ ni [] tm 
  where
    ni env (PRef _ n)        
        | not (n `elem` env) = [n]
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PHidden tm)    = ni env tm
    ni env (PEq _ l r)     = ni env l ++ ni env r
    ni env (PPair _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ l t r)  = ni env l ++ ni env t ++ ni env r
    ni env _               = []

namesIn :: IState -> PTerm -> [Name]
namesIn ist tm = nub $ ni [] tm 
  where
    ni env (PRef _ n)        
        | not (n `elem` env) 
            = case lookupCtxt n (tt_ctxt ist) of
                Nothing -> [n]
                _ -> []
    ni env (PApp _ f as)   = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PEq _ l r)     = ni env l ++ ni env r
    ni env (PPair _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ l t r) = ni env l ++ ni env t ++ ni env r
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
infP = P (TCon 6 0) inferTy (Set 0)

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

eqTy = UN ["="]
eqCon = UN ["refl"]
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
sigmaTy   = UN ["Sigma"]
existsCon = UN ["Exists"]

piBind :: [(Name, PTerm)] -> PTerm -> PTerm
piBind [] t = t
piBind ((n, ty):ns) t = PPi expl n ty (piBind ns t)

-- Dealing with parameters

expandParams :: (Name -> Name) -> [(Name, PTerm)] -> [Name] -> PTerm -> PTerm
expandParams dec ps ns tm = en tm
  where
    en (PLam n t s) = PLam n (en t) (en s)
    en (PPi p n t s) = PPi p n (en t) (en s)
    en (PLet n ty v s) = PLet n (en ty) (en v) (en s)
    en (PEq f l r) = PEq f (en l) (en r)
    en (PPair f l r) = PPair f (en l) (en r)
    en (PDPair f l t r) = PDPair f (en l) (en t) (en r)
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
    en t = t

expandParamsD :: IState -> 
                 (Name -> Name) -> [(Name, PTerm)] -> [Name] -> PDecl -> PDecl
expandParamsD ist dec ps ns (PTy syn fc n ty) 
    = if n `elem` ns
         then PTy syn fc (dec n) (piBind ps (expandParams dec ps ns ty))
         else PTy syn fc n (expandParams dec ps ns ty)
expandParamsD ist dec ps ns (PClauses fc opts n cs)
    = let n' = if n `elem` ns then dec n else n in
          PClauses fc opts n' (map expandParamsC cs)
  where
    expandParamsC (PClause n lhs ws rhs ds)
        = let -- ps' = updateps True (namesIn ist rhs) (zip ps [0..])
              ps'' = updateps False (namesIn ist lhs) (zip ps [0..])
              n' = if n `elem` ns then dec n else n in
              PClause n' (expandParams dec ps'' ns lhs)
                         (map (expandParams dec ps'' ns) ws)
                         (expandParams dec ps'' ns rhs)
                         (map (expandParamsD ist dec ps'' ns) ds)
    expandParamsC (PWith n lhs ws wval ds)
        = let -- ps' = updateps True (namesIn ist wval) (zip ps [0..])
              ps'' = updateps False (namesIn ist lhs) (zip ps [0..])
              n' = if n `elem` ns then dec n else n in
              PWith n' (expandParams dec ps'' ns lhs)
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
        case lookupP n (tt_ctxt i) of
            Just (P (DCon _ _) _ _) -> 1
            Just (P (TCon _ _) _ _) -> 1
            Just (P Ref _ _) -> 3
            Nothing -> 0 -- must be locally bound, if it's not an error...
    pri (PPi _ _ x y) = max 4 (max (pri x) (pri y))
    pri (PTrue _) = 0
    pri (PFalse _) = 0
    pri (PRefl _) = 1
    pri (PEq _ l r) = max 1 (max (pri l) (pri r))
    pri (PApp _ f as) = max 1 (max (pri f) (foldr max 0 (map (pri.getTm) as))) 
    pri (PPair _ l r) = max 1 (max (pri l) (pri r))
    pri (PDPair _ l t r) = max 1 (max (pri l) (max (pri t) (pri r)))
    pri (PConstant _) = 0
    pri Placeholder = 1
    pri _ = 3

-- Dealing with implicit arguments

-- Add implicit Pi bindings for any names in the term which appear in an
-- argument position.

-- This has become a right mess already. Better redo it some time...

implicit :: SyntaxInfo -> Name -> PTerm -> Idris PTerm
implicit syn n ptm 
    = do i <- get
         let (tm', impdata) = implicitise syn i ptm
         let (tm'', spos) = findStatics i tm'
         put (i { idris_implicits = addDef n impdata (idris_implicits i) })
         logLvl 5 ("Implicit " ++ show n ++ " " ++ show impdata)
         i <- get
         put (i { idris_statics = addDef n spos (idris_statics i) })
         return tm''

implicitise :: SyntaxInfo -> IState -> PTerm -> (PTerm, [PArg])
implicitise syn ist tm
    = let uvars = using syn
          pvars = syn_params syn
          (declimps, ns') = execState (imps True [] tm) ([], []) 
          ns = ns' \\ (map fst pvars ++ no_imp syn) in
          if null ns 
            then (tm, reverse declimps) 
            else implicitise syn ist (pibind uvars ns tm)
  where
    dropAll (x:xs) ys | x `elem` ys = dropAll xs ys
                      | otherwise   = x : dropAll xs ys
    dropAll [] ys = []

    imps top env (PApp _ f as)
       = do (decls, ns) <- get
            let isn = concatMap (namesIn ist) (map getTm as)
            put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PPi (Imp l _) n ty sc) 
        = do let isn = nub (namesIn ist ty) `dropAll` [n]
             (decls , ns) <- get
             put (PImp (getPriority ist ty) l n ty : decls, 
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (Exp l _) n ty sc) 
        = do let isn = nub (namesIn ist ty ++ case sc of
                            (PRef _ x) -> namesIn ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PExp (getPriority ist ty) l ty : decls, 
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi (Constraint l _) n ty sc)
        = do let isn = nub (namesIn ist ty ++ case sc of
                            (PRef _ x) -> namesIn ist sc `dropAll` [n]
                            _ -> [])
             (decls, ns) <- get -- ignore decls in HO types
             put (PConstraint 10 l ty : decls, 
                  nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PEq _ l r)
        = do (decls, ns) <- get
             let isn = namesIn ist l ++ namesIn ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PPair _ l r)
        = do (decls, ns) <- get
             let isn = namesIn ist l ++ namesIn ist r
             put (decls, nub (ns ++ (isn `dropAll` (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ (PRef _ n) t r)
        = do (decls, ns) <- get
             let isn = nub (namesIn ist t ++ namesIn ist r) \\ [n]
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ l t r)
        = do (decls, ns) <- get
             let isn = namesIn ist l ++ namesIn ist t ++ namesIn ist r
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
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

addImpl :: IState -> PTerm -> PTerm
addImpl ist ptm = ai [] ptm
  where
    ai env (PRef fc f)       = aiFn ist fc f []
    ai env (PEq fc l r)   = let l' = ai env l
                                r' = ai env r in
                                PEq fc l' r'
    ai env (PPair fc l r) = let l' = ai env l
                                r' = ai env r in
                                PPair fc l' r'
    ai env (PDPair fc l t r) = let l' = ai env l
                                   t' = ai env t
                                   r' = ai env r in
                                   PDPair fc l' t' r'
    ai env (PApp fc (PRef _ f) as) 
                          = let as' = map (fmap (ai env)) as in
                                aiFn ist fc f as'
    ai env (PApp fc f as) = let f' = ai env f
                                as' = map (fmap (ai env)) as in
                                mkPApp fc 1 f' as'
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

aiFn :: IState -> FC -> Name -> [PArg] -> PTerm
aiFn ist fc f as
    | f `elem` primNames = PApp fc (PRef fc f) as
aiFn ist fc f as
        = case lookupCtxt f (idris_implicits ist) of
            Just ns -> mkPApp fc (length ns) (PRef fc f) (insertImpl ns as)
            Nothing -> mkPApp fc 1 (PRef fc f) as
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
    insertImpl expected [] = []
    insertImpl []       given  = given

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
findStatics ist tm = let (ns, ss) = fs tm in
                         runState (pos ns ss tm) []
  where fs (PPi p n t sc)
            | Static <- pstatic p
                        = let (ns, ss) = fs sc in
                              (namesIn ist t : ns, namesIn ist t ++ n : ss)
            | otherwise = let (ns, ss) = fs sc in
                              (namesIn ist t : ns, ss)
        fs _ = ([], [])

        inOne n ns = length (filter id (map (elem n) ns)) == 1

        pos ns ss (PPi p n t sc) 
            | n `inOne` ns && elem n ss
                        = do sc' <- pos ns ss sc
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
dumpDecl (PTy _ _ n t) = "tydecl " ++ show n ++ " : " ++ showImp True t
dumpDecl (PClauses _ _ n cs) = "pat " ++ show n ++ "\t" ++ showSep "\n\t" (map (showCImp True) cs)
dumpDecl (PData _ _ d) = showDImp True d
dumpDecl (PParams _ ns ps) = "params {" ++ show ns ++ "\n" ++ dumpDecls ps ++ "}\n"
dumpDecl (PSyntax _ syn) = "syntax " ++ show syn
dumpDecl (PClass _ _ cs n ps ds) 
    = "class " ++ show cs ++ " " ++ show n ++ " " ++ show ps ++ "\n" ++ dumpDecls ds
dumpDecl (PInstance _ _ cs n _ t ds) 
    = "instance " ++ show cs ++ " " ++ show n ++ " " ++ show t ++ "\n" ++ dumpDecls ds
dumpDecl _ = "..."
-- dumpDecl (PImport i) = "import " ++ i

-- syntactic match of a against b, returning pair of variables in a 
-- and what they match. Returns 'Nothing' if not a match.

matchClause :: PTerm -> PTerm -> Maybe [(Name, PTerm)]
matchClause x y = match x y where
    matchArg x y = match (getTm x) (getTm y)

    match (PApp _ f args) (PApp _ f' args')
        | length args == length args'
            = do mf <- match f f'
                 ms <- zipWithM matchArg args args'
                 return (mf ++ concat ms)
    match (PRef _ n) (PRef _ n') | n == n' = return []
                                 | otherwise = Nothing
    match (PRef _ n) tm = return [(n, tm)]
    match (PEq _ l r) (PEq _ l' r') = do ml <- match l l'
                                         mr <- match r r'
                                         return (ml ++ mr)
    match (PPair _ l r) (PPair _ l' r') = do ml <- match l l'
                                             mr <- match r r'
                                             return (ml ++ mr)
    match (PDPair _ l t r) (PDPair _ l' t' r') = do ml <- match l l'
                                                    mt <- match t t'
                                                    mr <- match r r'
                                                    return (ml ++ mt ++ mr)
    match (PRefl _) (PRefl _) = return []
    match (PResolveTC _) (PResolveTC _) = return []
    match (PTrue _) (PTrue _) = return []
    match (PFalse _) (PFalse _) = return []
    match (PReturn _) (PReturn _) = return []
    match (PPi _ _ t s) (PPi _ _ t' s') = do mt <- match t t'
                                             ms <- match s s'
                                             return (mt ++ ms)
    match (PLam _ t s) (PLam _ t' s') = do mt <- match t t'
                                           ms <- match s s'
                                           return (mt ++ ms)
    match (PHidden x) (PHidden y) = match x y
    match a b | a == b = return []
              | otherwise = Nothing

substMatches :: [(Name, PTerm)] -> PTerm -> PTerm
substMatches [] t = t
substMatches ((n,tm):ns) t = substMatch n tm (substMatches ns t)

substMatch :: Name -> PTerm -> PTerm -> PTerm
substMatch n tm t = sm t where
    sm (PRef _ n') | n == n' = tm
    sm (PLam x t sc) = PLam x (sm t) (sm sc)
    sm (PPi p x t sc) = PPi p x (sm t) (sm sc)
    sm (PApp f x as) = PApp f (sm x) (map (fmap sm) as)
    sm (PEq f x y) = PEq f (sm x) (sm y)
    sm (PPair f x y) = PPair f (sm x) (sm y)
    sm (PDPair f x t y) = PDPair f (sm x) (sm t) (sm y)
    sm (PHidden x) = PHidden (sm x)
    sm x = x


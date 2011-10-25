{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             TypeSynonymInstances #-}

module Idris.AbsSyntax where

import Core.TT
import Core.Evaluate

import Control.Monad.State
import Data.List
import Data.Char
import Debug.Trace

import qualified Epic.Epic as E

data IOption = IOption { opt_logLevel :: Int }
    deriving (Show, Eq)

defaultOpts = IOption 0

-- TODO: Add 'module data' to IState, which can be saved out and reloaded quickly (i.e
-- without typechecking).
-- This will include all the functions and data declarations, plus fixity declarations
-- and syntax macros.

data IState = IState { tt_ctxt :: Context,
                       idris_infixes :: [FixDecl],
                       idris_implicits :: Ctxt [PArg],
                       idris_log :: String,
                       idris_options :: IOption,
                       idris_name :: Int,
                       idris_metavars :: [Name],
                       syntax_rules :: [Syntax],
                       imported :: [FilePath],
                       idris_prims :: [(Name, ([E.Name], E.Term))]
                     }
                   
idrisInit = IState emptyContext [] emptyContext "" defaultOpts 0 [] [] [] []

-- The monad for the main REPL - reading and processing files and updating 
-- global state (hence the IO inner monad).
type Idris a = StateT IState IO a

getContext :: Idris Context
getContext = do i <- get; return (tt_ctxt i)

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
addDeferred ns = do mapM_ (\(n, t) -> updateContext (addTyDecl n t)) ns
                    i <- get
                    put (i { idris_metavars = map fst ns ++ idris_metavars i })

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

-- Commands in the REPL

data Command = Quit | Help | Eval PTerm 
             | Compile String
             | Metavars
             | TTShell 
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

data Plicity = Imp | Exp deriving (Show, Eq)

data PDecl' t = PFix     FC Fixity [String] -- fixity declaration
              | PTy      FC Name t          -- type declaration
              | PClauses FC Name [PClause' t]    -- pattern clause
              | PData    FC (PData' t)      -- data declaration
              | PParams  FC [(Name, PTerm)] [PDecl' t] -- params block
              | PSyntax  FC Syntax
    deriving Functor

data PClause' t = PClause Name t [t] t [PDecl]
                | PWith   Name t [t] t [PDecl]
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
declared (PTy _ n t) = [n]
declared (PClauses _ n _) = [] -- not a declaration
declared (PData _ (PDatadecl n _ ts)) = n : map fstt ts
   where fstt (a, _, _) = a
declared (PParams _ _ ds) = concatMap declared ds
-- declared (PImport _) = []

-- High level language terms
--
data PTerm = PQuote Raw
           | PRef FC Name
           | PLam Name PTerm PTerm
           | PPi  Plicity Name PTerm PTerm
           | PLet Name PTerm PTerm PTerm -- not implemented yet
           | PApp FC PTerm [PArg]
           | PTrue FC
           | PFalse FC
           | PPair FC PTerm PTerm
           | PDPair FC PTerm PTerm
           | PHidden PTerm -- irrelevant or hidden pattern
           | PSet
           | PConstant Const
           | Placeholder
           | PDoBlock [PDo]
           | PReturn FC
           | PMetavar Name
           | PElabError String -- error to report on elaboration
    deriving Eq

data PDo = DoExp  FC PTerm
         | DoBind FC Name PTerm
         | DoLet  FC Name PTerm
    deriving Eq

data PArg' t = PImp { pname :: Name, getTm :: t }
             | PExp { getTm :: t }
    deriving (Show, Eq, Functor)

type PArg = PArg' PTerm

-- Syntactic sugar info (TODO: namespaces, modules)

data DSL = DSL { dsl_bind :: Name,
                 dsl_return :: Name }
    deriving Show

data Syntax = Rule [SSymbol] PTerm
    deriving Show

data SSymbol = Keyword Name
             | Symbol String
             | Expr Name
    deriving Show

initDSL = DSL (UN ["io_bind"]) (UN ["io_return"])

data SyntaxInfo = Syn { using :: [(Name, PTerm)],
                        syn_params :: [(Name, PTerm)],
                        no_imp :: [Name],
                        dsl_info :: DSL }
    deriving Show

defaultSyntax = Syn [] [] [] initDSL

--- Pretty printing declarations and terms

instance Show PTerm where
    show tm = showImp False tm

instance Show PDecl where
    show (PFix _ f ops) = show f ++ " " ++ showSep ", " ops
    show (PTy _ n ty) = show n ++ " : " ++ show ty
    show (PClauses _ n c) = showSep "\n" (map show c)
    show (PData _ d) = show d

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
getImps (PImp n tm : xs) = (n, tm) : getImps xs
getImps (_ : xs) = getImps xs

getExps :: [PArg] -> [PTerm]
getExps [] = []
getExps (PExp tm : xs) = tm : getExps xs
getExps (_ : xs) = getExps xs

getAll :: [PArg] -> [PTerm]
getAll = map getTm 

showImp :: Bool -> PTerm -> String
showImp impl tm = se 10 tm where
    se p (PQuote r) = "![" ++ show r ++ "]"
    se p (PRef _ n) = show n
    se p (PLam n ty sc) = bracket p 2 $ "\\ " ++ show n ++ " => " ++ show sc
    se p (PLet n ty v sc) = bracket p 2 $ "let " ++ show n ++ " = " ++ se 10 v ++
                            " in " ++ se 10 sc 
    se p (PPi Exp n ty sc)
        | n `elem` allNamesIn sc = bracket p 2 $
                                    "(" ++ show n ++ " : " ++ se 10 ty ++ 
                                    ") -> " ++ se 10 sc
        | otherwise = bracket p 2 $ se 0 ty ++ " -> " ++ se 10 sc
    se p (PPi Imp n ty sc)
        | impl = bracket p 2 $ "{" ++ show n ++ " : " ++ se 10 ty ++ 
                               "} -> " ++ se 10 sc
        | otherwise = se 10 sc
    se p (PApp _ (PRef _ f) [])
        | not impl = show f
    se p (PApp _ (PRef _ op@(UN [f:_])) args)
        | length (getExps args) == 2 && not impl && not (isAlpha f) 
            = let [l, r] = getExps args in
              bracket p 1 $ se 1 l ++ " " ++ show op ++ " " ++ se 0 r
    se p (PApp _ f as) 
        = let (imps, args) = (getImps as, getExps as) in
              bracket p 1 $ se 1 f ++ (if impl then concatMap siArg imps else "")
                                   ++ concatMap seArg args
    se p (PHidden tm) = "." ++ se 0 tm
    se p (PTrue _) = "()"
    se p (PFalse _) = "_|_"
    se p (PPair _ l r) = "(" ++ se 10 l ++ ", " ++ se 10 r ++ ")"
    se p (PDPair _ l r) = "(" ++ se 10 l ++ " ** " ++ se 10 r ++ ")"
    se p PSet = "Set"
    se p (PConstant c) = show c
    se p (PMetavar n) = "?" ++ show n
    se p Placeholder = "_"

    seArg arg      = " " ++ se 0 arg
    siArg (n, val) = " {" ++ show n ++ " = " ++ se 10 val ++ "}"

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
    ni env (PPair _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ l r)  = ni env l ++ ni env r
    ni env _               = []

namesIn :: IState -> PTerm -> [Name]
namesIn ist tm = nub $ ni [] tm 
  where
    ni env (PRef _ n)        
        | not (n `elem` env) 
            = case lookupCtxt n (idris_implicits ist) of
                Nothing -> [n]
                _ -> []
    ni env (PApp _ f as)  = ni env f ++ concatMap (ni env) (map getTm as)
    ni env (PLam n ty sc)  = ni env ty ++ ni (n:env) sc
    ni env (PPi _ n ty sc) = ni env ty ++ ni (n:env) sc
    ni env (PPair _ l r)   = ni env l ++ ni env r
    ni env (PDPair _ l r)  = ni env l ++ ni env r
    ni env (PHidden tm)    = ni env tm
    ni env _               = []

-- For inferring types of things

bi = FC "builtin" 0

inferTy   = MN 0 "__Infer"
inferCon  = MN 0 "__infer"
inferDecl = PDatadecl inferTy 
                      PSet
                      [(inferCon, PPi Imp (MN 0 "A") PSet (
                                  PPi Exp (MN 0 "a") (PRef bi (MN 0 "A"))
                                  (PRef bi inferTy)), bi)]

infTerm t = PApp bi (PRef bi inferCon) [PImp (MN 0 "A") Placeholder, PExp t]
infP = P (TCon 0) inferTy (Set 0)

getInferTerm, getInferType :: Term -> Term
getInferTerm (Bind n b sc) = Bind n b $ getInferTerm sc
getInferTerm (App (App _ _) tm) = tm
getInferTerm tm = error ("getInferTerm " ++ show tm)

getInferType (Bind n b sc) = Bind n b $ getInferType sc
getInferType (App (App _ ty) _) = ty

-- Handy primitives: Unit, False, Pair, MkPair, mkForeign


unitTy   = MN 0 "__Unit"
unitCon  = MN 0 "__II"
unitDecl = PDatadecl unitTy PSet
                     [(unitCon, PRef bi unitTy, bi)]

falseTy   = MN 0 "__False"
falseDecl = PDatadecl falseTy PSet []

pairTy    = MN 0 "__Pair"
pairCon   = MN 0 "__MkPair"
pairDecl  = PDatadecl pairTy (piBind [(n "A", PSet), (n "B", PSet)] PSet)
            [(pairCon, PPi Imp (n "A") PSet (
                       PPi Imp (n "B") PSet (
                       PPi Exp (n "a") (PRef bi (n "A")) (
                       PPi Exp (n "b") (PRef bi (n "B"))  
                           (PApp bi (PRef bi pairTy) [PExp (PRef bi (n "A")),
                                                PExp (PRef bi (n "B"))])))), bi)]
    where n a = MN 0 a

-- Defined in builtins.idr
sigmaTy   = UN ["Sigma"]
existsCon = UN ["Exists"]

piBind :: [(Name, PTerm)] -> PTerm -> PTerm
piBind [] t = t
piBind ((n, ty):ns) t = PPi Exp n ty (piBind ns t)

-- Dealing with implicit arguments

-- Add implicit Pi bindings for any names in the term which appear in an
-- argument position.

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
    imps top env (PApp _ f as)
       = do (decls, ns) <- get
            let isn = concatMap (namesIn ist) (map getTm as)
            put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PPi Imp n ty sc) 
        = do let isn = namesIn ist ty \\ [n]
             (decls , ns) <- get
             put (PImp n ty : decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPi Exp n ty sc) 
        = do let isn = (namesIn ist ty ++ case sc of
                            (PRef _ x) -> namesIn ist sc
                            _ -> []) \\ [n]
             (decls, ns) <- get -- ignore decls in HO types
             put (PExp ty : decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
             imps True (n:env) sc
    imps top env (PPair _ l r)
        = do (decls, ns) <- get
             let isn = namesIn ist l ++ namesIn ist r
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ (PRef _ n) r)
        = do (decls, ns) <- get
             let isn = namesIn ist r \\ [n]
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PDPair _ l r)
        = do (decls, ns) <- get
             let isn = namesIn ist l ++ namesIn ist r
             put (decls, nub (ns ++ (isn \\ (env ++ map fst (getImps decls)))))
    imps top env (PLam n ty sc)  
        = do imps False env ty
             imps False (n:env) sc
    imps top env (PHidden tm)    = imps False env tm
    imps top env _               = return ()

    pibind using []     sc = sc
    pibind using (n:ns) sc = case lookup n using of
                               Just ty -> PPi Imp n ty (pibind using ns sc)
                               Nothing -> PPi Imp n Placeholder (pibind using ns sc)

-- Add implicit arguments in function calls

addImpl :: IState -> PTerm -> PTerm
addImpl ist ptm = ai [] ptm
  where
    ai env (PRef fc f)       = aiFn fc env (PRef fc f) []
    ai env (PPair fc l r) = let l' = ai env l
                                r' = ai env r in
                                PPair fc l' r'
    ai env (PDPair fc l r) = let l' = ai env l
                                 r' = ai env r in
                                 PDPair fc l' r'
    ai env (PApp fc (PRef _ f) as) 
                          = let as' = map (fmap (ai env)) as in
                                aiFn fc env (PRef fc f) as'
    ai env (PApp fc f as) = let f' = ai env f
                                as' = map (fmap (ai env)) as in
                                      aiFn fc env f' as'
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
    ai env tm = tm

    aiFn _ env (PRef fc f) as | not (f `elem` env)
        = case lookupCtxt f (idris_implicits ist) of
            Just ns -> pApp fc (length ns) (PRef fc f) (insertImpl ns as)
            Nothing -> pApp fc 1 (PRef fc f) as
    aiFn fc env f as = pApp fc 1 f as

    pApp fc a f [] = f
    pApp fc a f as = let rest = drop a as in
                        appRest fc (PApp fc f (take a as)) rest

    appRest fc f [] = f
    appRest fc f (a : as) = appRest fc (PApp fc f [a]) as

    insertImpl :: [PArg] -> [PArg] -> [PArg]
    insertImpl (PExp ty : ps) (PExp tm : given) =
                                 PExp tm : insertImpl ps given
    insertImpl (PImp n ty : ps) given =
        case find n given [] of
            Just (tm, given') -> PImp n tm : insertImpl ps given'
            Nothing ->           PImp n Placeholder : insertImpl ps given
    insertImpl expected [] = []
    insertImpl []       given  = given

    find n []               acc = Nothing
    find n (PImp n' t : gs) acc 
         | n == n' = Just (t, reverse acc ++ gs)
    find n (g : gs) acc = find n gs (g : acc)

-- Debugging/logging stuff

dumpDecls :: [PDecl] -> String
dumpDecls [] = ""
dumpDecls (d:ds) = dumpDecl d ++ "\n" ++ dumpDecls ds

dumpDecl (PFix _ f ops) = show f ++ " " ++ showSep ", " ops 
dumpDecl (PTy _ n t) = "tydecl " ++ show n ++ " : " ++ showImp True t
dumpDecl (PClauses _ n cs) = "pat\t" ++ showSep "\n\t" (map (showCImp True) cs)
dumpDecl (PData _ d) = showDImp True d
dumpDecl (PParams _ ns ps) = "params {" ++ show ns ++ "\n" ++ dumpDecls ps ++ "}\n"
dumpDecl (PSyntax _ syn) = "syntax " ++ show syn
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
    match (PPair _ l r) (PPair _ l' r') = do ml <- match l l'
                                             mr <- match r r'
                                             return (ml ++ mr)
    match (PDPair _ l r) (PDPair _ l' r') = do ml <- match l l'
                                               mr <- match r r'
                                               return (ml ++ mr)
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
    sm (PPair f x y) = PPair f (sm x) (sm y)
    sm (PDPair f x y) = PDPair f (sm x) (sm y)
    sm (PHidden x) = PHidden (sm x)
    sm x = x


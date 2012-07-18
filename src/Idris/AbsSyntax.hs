{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             TypeSynonymInstances, PatternGuards #-}

module Idris.AbsSyntax(module Idris.AbsSyntax, module Idris.AbsSyntaxTree) where

import Core.TT
import Core.Evaluate
import Core.Elaborate hiding (Tactic(..))
import Core.Typecheck
import Idris.AbsSyntaxTree
import RTS.SC

import Paths_idris

import System.Console.Haskeline

import Control.Monad.State

import Data.List
import Data.Char
import Data.Either

import Debug.Trace

import qualified Epic.Epic as E

import Util.Pretty


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

addToCalledG :: Name -> [Name] -> Idris ()
addToCalledG n ns = return () -- TODO

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

setErrContext :: Bool -> Idris ()
setErrContext t = do i <- get
                     let opts = idris_options i
                     let opt' = opts { opt_errContext = t }
                     put (i { idris_options = opt' })

errContext :: Idris Bool
errContext = do i <- get
                return (opt_errContext (idris_options i))

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

setIBCSubDir :: FilePath -> Idris ()
setIBCSubDir fp = do i <- get
                     let opts = idris_options i
                     let opt' = opts { opt_ibcsubdir = fp }
                     put (i { idris_options = opt' })

valIBCSubDir :: IState -> Idris FilePath
valIBCSubDir i = return (opt_ibcsubdir (idris_options i))

setImportDirs :: [FilePath] -> Idris ()
setImportDirs fps = do i <- get
                       let opts = idris_options i
                       let opt' = opts { opt_importdirs = fps }
                       put (i { idris_options = opt' })

allImportDirs :: IState -> Idris [FilePath]
allImportDirs i = do datadir <- liftIO $ getDataDir
                     let optdirs = opt_importdirs (idris_options i)
                     return ("." : (optdirs ++ [datadir]))

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
    en (PAlternative a as) = PAlternative a (map en as)
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
    pri (PAlternative a as) = maximum (map pri as)
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
    imps top env (PAlternative a as)
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
        | not (f `elem` env) = handleErr $ aiFn inpat inpat ist fc f []
    ai env (PHidden (PRef fc f))
        | not (f `elem` env) = handleErr $ aiFn inpat False ist fc f []
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
    ai env (PAlternative a as) = let as' = map (ai env) as in
                                     PAlternative a as'
    ai env (PApp fc (PRef _ f) as) 
        | not (f `elem` env)
                          = let as' = map (fmap (ai env)) as in
                                handleErr $ aiFn inpat False ist fc f as'
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

aiFn :: Bool -> Bool -> IState -> FC -> Name -> [PArg] -> Either Err PTerm
aiFn inpat True ist fc f []
  = case lookupCtxt Nothing f (idris_implicits ist) of
        [] -> Right $ PRef fc f
        alts -> if (any (all imp) alts)
                        then aiFn inpat False ist fc f [] -- use it as a constructor
                        else Right $ PRef fc f
    where imp (PExp _ _ _) = False
          imp _ = True
aiFn inpat expat ist fc f as
    | f `elem` primNames = Right $ PApp fc (PRef fc f) as
aiFn inpat expat ist fc f as
          -- This is where namespaces get resolved by adding PAlternative
        = case lookupCtxtName Nothing f (idris_implicits ist) of
            [(f',ns)] -> Right $ mkPApp fc (length ns) (PRef fc f') (insertImpl ns as)
            [] -> if f `elem` idris_metavars ist
                    then Right $ PApp fc (PRef fc f) as
                    else Right $ mkPApp fc (length as) (PRef fc f) as
            alts -> Right $
                     PAlternative True $
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
            Nothing -> if inpat 
                          then PTacImplicit p l n sc Placeholder : insertImpl ps given
                          else PTacImplicit p l n sc sc : insertImpl ps given
    insertImpl expected [] = []
    insertImpl _        given  = given

    find n []               acc = Nothing
    find n (PImp _ _ n' t : gs) acc 
         | n == n' = Just (t, reverse acc ++ gs)
    find n (PTacImplicit _ _ n' _ t : gs) acc 
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
dumpDecl (PInstance _ _ cs n _ t _ ds) 
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
    match (PAlternative a as) (PAlternative a' as') 
        = do ms <- zipWithM match' as as' 
             return (concat ms)
    match a@(PAlternative _ as) b
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
    sm (PAlternative a as) = PAlternative a (map sm as)
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
    sm (PAlternative a as) = PAlternative a (map sm as)
    sm (PHidden x) = PHidden (sm x)
    sm x = x


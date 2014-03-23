{-# LANGUAGE PatternGuards, TypeSynonymInstances, CPP #-}

module IRTS.Compiler where

import IRTS.Lang
import IRTS.Defunctionalise
import IRTS.Simplified
import IRTS.CodegenCommon
import IRTS.CodegenC
import IRTS.CodegenJava
import IRTS.DumpBC
import IRTS.CodegenJavaScript
#ifdef IDRIS_LLVM
import IRTS.CodegenLLVM
#else
import Util.LLVMStubs
#endif
import IRTS.Inliner

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Erasure
import Idris.Error

import Debug.Trace

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.CaseTree

import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.List
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S
import System.Process
import System.IO
import System.Directory
import System.Environment
import System.FilePath ((</>), addTrailingPathSeparator)

import Paths_idris

compile :: Codegen -> FilePath -> Term -> Idris ()
compile codegen f tm
   = do checkMVs  -- check for undefined metavariables
        reachableNames <- performUsageAnalysis
        maindef <- irMain tm
        iLOG $ "MAIN: " ++ show maindef
        objs <- getObjectFiles codegen
        libs <- getLibs codegen
        flags <- getFlags codegen
        hdrs <- getHdrs codegen
        impdirs <- allImportDirs
        defsIn <- mkDecls tm reachableNames
        let defs = defsIn ++ [(sMN 0 "runMain", maindef)]
        -- iputStrLn $ showSep "\n" (map show defs)
        let (nexttag, tagged) = addTags 65536 (liftAll defs)
        let ctxtIn = addAlist tagged emptyContext
        iLOG "Defunctionalising"
        let defuns_in = defunctionalise nexttag ctxtIn
        logLvl 5 $ show defuns_in
        iLOG "Inlining"
        let defuns = inline defuns_in
        logLvl 5 $ show defuns
        iLOG "Resolving variables for CG"
        -- iputStrLn $ showSep "\n" (map show (toAlist defuns))
        let checked = checkDefs defuns (toAlist defuns)
        outty <- outputTy
        dumpCases <- getDumpCases
        dumpDefun <- getDumpDefun
        case dumpCases of
            Nothing -> return ()
            Just f -> runIO $ writeFile f (showCaseTrees defs)
        case dumpDefun of
            Nothing -> return ()
            Just f -> runIO $ writeFile f (dumpDefuns defuns)
        triple <- Idris.AbsSyntax.targetTriple
        cpu <- Idris.AbsSyntax.targetCPU
        optimise <- optLevel
        iLOG "Building output"

        case checked of
            OK c -> do let cginfo = CodegenInfo f outty triple cpu optimise
                                                hdrs impdirs objs libs flags
                                                NONE c (toAlist defuns)
                                                tagged
                       runIO $ case codegen of
                              ViaC -> codegenC cginfo
                              ViaJava -> codegenJava cginfo 
                              ViaJavaScript -> codegenJavaScript cginfo
                              ViaNode -> codegenNode cginfo
                              ViaLLVM -> codegenLLVM cginfo
                              Bytecode -> dumpBC c f
            Error e -> ierror e
  where checkMVs = do i <- getIState
                      case map fst (idris_metavars i) \\ primDefs of
                            [] -> return ()
                            ms -> ifail $ "There are undefined metavariables: " ++ show ms
        inDir d h = do let f = d </> h
                       ex <- doesFileExist f
                       if ex then return f else return h

irMain :: TT Name -> Idris LDecl
irMain tm = do
    i <- irTerm M.empty [] tm
    return $ LFun [] (sMN 0 "runMain") [] (LForce i)

mkDecls :: Term -> [Name] -> Idris [(Name, LDecl)]
mkDecls t used
    = do i <- getIState
         let ds = filter (\(n, d) -> n `elem` used || isCon d) $ ctxtAlist (tt_ctxt i)
         decls <- mapM build ds
         return decls

showCaseTrees :: [(Name, LDecl)] -> String
showCaseTrees ds = showSep "\n\n" (map showCT ds)
  where
    showCT (n, LFun _ f args lexp)
       = show n ++ " " ++ showSep " " (map show args) ++ " =\n\t "
            ++ show lexp
    showCT (n, LConstructor c t a) = "data " ++ show n ++ " " ++ show a

isCon (TyDecl _ _) = True
isCon _ = False

build :: (Name, Def) -> Idris (Name, LDecl)
build (n, d)
    = do i <- getIState
         case lookup n (idris_scprims i) of
              Just (ar, op) ->
                  let args = map (\x -> sMN x "op") [0..] in
                      return (n, (LFun [] n (take ar args)
                                         (LOp op (map (LV . Glob) (take ar args)))))
              _ -> do def <- mkLDecl n d
                      logLvl 3 $ "Compiled " ++ show n ++ " =\n\t" ++ show def
                      return (n, def)

declArgs args inl n (LLam xs x) = declArgs (args ++ xs) inl n x
declArgs args inl n x = LFun (if inl then [Inline] else []) n args x

mkLDecl n (Function tm _)
    = declArgs [] True n <$> irTerm M.empty [] tm

mkLDecl n (CaseOp ci _ _ _ pats cd)
    = declArgs [] (case_inlinable ci) n <$> irTree args sc
  where
    (args, sc) = cases_runtime cd

mkLDecl n (TyDecl (DCon tag arity) _) =
    LConstructor n tag . erasedArity . lookup n <$> getIState
  where
    lookup n = lookupCtxtExact n . idris_callgraph
    erasedArity = maybe 0 (length . usedpos)

mkLDecl n (TyDecl (TCon t a) _) = return $ LConstructor n (-1) a
mkLDecl n _ = return $ (declArgs [] True n LNothing) -- postulate, never run

data VarInfo = VI
    { viMethod :: Maybe Name
    }
    deriving Show

type Vars = M.Map Name VarInfo

irTerm :: Vars -> [Name] -> Term -> Idris LExp
irTerm vs env tm@(App f a) = case unApply tm of
    (P _ (UN m) _, args)
        | m == txt "mkForeignPrim"
        -> doForeign vs env args

    (P _ (UN u) _, [_, arg])
        | u == txt "unsafePerformPrimIO"
        -> irTerm vs env arg

    -- TMP HACK - until we get inlining.
    (P _ (UN r) _, [_, _, _, _, _, arg])
        | r == txt "replace"
        -> irTerm vs env arg

    -- Laziness, the old way
    (P _ (UN l) _, [_, arg])
        | l == txt "lazy"
        -> error "lazy has crept in somehow"

    (P _ (UN l) _, [_, arg])
        | l == txt "force"
        -> LForce <$> irTerm vs env arg

    -- Laziness, the new way
    (P _ (UN l) _, [_, _, arg])
        | l == txt "Delay"
        -> LLazyExp <$> irTerm vs env arg

    (P _ (UN l) _, [_, _, arg])
        | l == txt "Force"
        -> LForce <$> irTerm vs env arg

    (P _ (UN a) _, [_, _, arg])
        | a == txt "assert_smaller"
        -> irTerm vs env arg

    (P _ (UN a) _, [_, arg])
        | a == txt "assert_total"
        -> irTerm vs env arg

    (P _ (UN p) _, [_, arg])
        | p == txt "par"
        -> do arg' <- irTerm vs env arg
              return $ LOp LPar [LLazyExp arg']

    (P _ (UN pf) _, [arg])
        | pf == txt "prim_fork"
        -> do arg' <- irTerm vs env arg
              return $ LOp LFork [LLazyExp arg']

    (P _ (UN m) _, [_,size,t])
        | m == txt "malloc"
        -> irTerm vs env t

    (P _ (UN tm) _, [_,t])
        | tm == txt "trace_malloc"
        -> irTerm vs env t -- TODO

    -- This case is here until we get more general inlining. It's just
    -- a really common case, and the laziness hurts...
    (P _ (NS (UN be) [b,p]) _, [_,x,(App (P _ (UN d) _) t),
                                        (App (P _ (UN d') _) e)])
        | be == txt "boolElim"
        , d  == txt "Delay"
        , d' == txt "Delay"
        -> do
            x' <- irTerm vs env x
            t' <- irTerm vs env t
            e' <- irTerm vs env e
            return (LCase x' [LConCase 0 (sNS (sUN "False") ["Bool","Prelude"]) [] e'
                             ,LConCase 1 (sNS (sUN "True" ) ["Bool","Prelude"]) [] t'
                             ])

    (P (DCon t arity) n _, args) -> do
        ist <- getIState
        let detag = maybe False detaggable . lookupCtxtExact n $ idris_optimisation ist
            used  = maybe [] (map fst . usedpos) . lookupCtxtExact n $ idris_callgraph ist
            args' = [a | (i,a) <- zip [0..] args, i `elem` used]

        when (length args > arity) $
            ifail ("oversaturated data ctor: " ++ show tm)

        if length args' == 1 && detag -- detaggable
            then irTerm vs env (head args')  -- newtype
            else irCon vs env (length used) n args'

    (P (TCon t a) n _, args) -> return LNothing

    (P _ n _, args) -> do
        ist <- getIState
        case lookup n (idris_scprims ist) of
            -- if it's a primitive that is already saturated,
            -- compile to the corresponding op here already to save work
            Just (arity, op) | length args == arity
                -> LOp op <$> mapM (irTerm vs env) args

            -- otherwise, just apply the name
            _   -> applyName n ist args

    -- turn de bruijn vars into regular named references and try again
    (V i, args) -> irTerm vs env $ mkApp (P Bound (env !! i) Erased) args

    (f, args)
        -> LApp False
            <$> irTerm vs env f
            <*> mapM (irTerm vs env) args

  where
    applyName :: Name -> IState -> [Term] -> Idris LExp
    applyName n ist args =
        LApp False (LV $ Glob n) <$> mapM (irTerm vs env . erase) (zip [0..] args)
        where
            erase (i, x)
                | i >= arity || i `elem` used = x
                | otherwise = Erased

            arity = case fst4 <$> lookupCtxt n (definitions . tt_ctxt $ ist) of
                [CaseOp ci ty tys def tot cdefs] -> length tys
                [TyDecl (DCon tag ar) _]         -> ar
                [TyDecl Ref ty]                  -> length $ getArgTys ty
                [Operator ty ar op]              -> ar
                []  -> 0  -- no definition, probably local name => can't erase anything
                def -> error $ "unknown arity: " ++ show (n, def)

            -- name for purposes of usage info lookup
            uName
                | Just n' <- viMethod =<< M.lookup n vs = n'
                | otherwise = n

            used = maybe [] (map fst . usedpos) $ lookupCtxtExact uName (idris_callgraph ist)
            fst4 (x,_,_,_) = x

irTerm vs env (P _ n _) = return $ LV (Glob n)
irTerm vs env (V i)
    | i >= 0 && i < length env = return $ LV (Glob (env!!i))
    | otherwise = ifail $ "bad de bruijn index: " ++ show i

irTerm vs env (Bind n (Lam _) sc) = LLam [n'] <$> irTerm vs (n':env) sc
  where
    n' = uniqueName n env

irTerm vs env (Bind n (Let _ v) sc)
    = LLet n <$> irTerm vs env v <*> irTerm vs (n : env) sc

irTerm vs env (Bind _ _ _) = return $ LNothing

irTerm vs env (Proj t (-1)) = do
    t' <- irTerm vs env t
    return $ LOp (LMinus (ATInt ITBig)) 
                 [t', LConst (BI 1)]

irTerm vs env (Proj t i)   = LProj <$> irTerm vs env t <*> pure i
irTerm vs env (Constant c) = return $ LConst c
irTerm vs env (TType _)    = return $ LNothing
irTerm vs env Erased       = return $ LNothing
irTerm vs env Impossible   = return $ LNothing

irCon :: Vars -> [Name] -> Int -> Name -> [Term] -> Idris LExp
irCon vs env arity n args
    | length args > arity
    = error $ "oversaturated data constructor: " ++ show (n, args)

    -- saturated
    | length args == arity
    = buildApp (LV (Glob n)) args

    -- undersaturated, wrap in lambdas
    | otherwise
    = let extraNs = [sMN i "sat" | i <- [length args .. arity-1]]
          extraTs = [P Bound n undefined | n <- extraNs]
        in LLam extraNs <$> irCon vs env arity n (args ++ extraTs)
  where
    buildApp e [] = return e
    buildApp e xs = LApp False e <$> mapM (irTerm vs env) xs

doForeign :: Vars -> [Name] -> [TT Name] -> Idris LExp
doForeign vs env (_ : fgn : args)
    | (_, (Constant (Str fgnName) : fgnArgTys : ret : [])) <- unApply fgn
    = case getFTypes fgnArgTys of
        Nothing -> ifail $ "Foreign type specification is not a constant list: " ++ show (fgn:args)
        Just tys -> do
            args' <- mapM (irTerm vs env) (init args)
            return $ LForeign LANG_C (mkIty' ret) fgnName (zip tys args')

    | otherwise = ifail "Badly formed foreign function call"
  where
    getFTypes :: TT Name -> Maybe [FType]
    getFTypes tm = case unApply tm of
        -- nil : {a : Type} -> List a
        (nil,  [_])         -> Just []
        -- cons : {a : Type} -> a -> List a -> List a
        (cons, [_, ty, xs]) -> (mkIty' ty :) <$> getFTypes xs
        _ -> Nothing

    mkIty' (P _ (UN ty) _) = mkIty (str ty)
    mkIty' (App (P _ (UN fi) _) (P _ (UN intTy) _))
        | fi == txt "FIntT"
        = mkIntIty (str intTy)

    mkIty' (App (App (P _ (UN ff) _) _) (App (P _ (UN fa) _) (App (P _ (UN io) _) _))) 
        | ff == txt "FFunction"
        , fa == txt "FAny"
        , io == txt "IO" 
        = FFunctionIO

    mkIty' (App (App (P _ (UN ff) _) _) _) 
        | ff == txt "FFunction"
        = FFunction

    mkIty' _ = FAny

    -- would be better if these FInt types were evaluated at compile time
    -- TODO: add %eval directive for such things

    mkIty "FFloat"      = FArith ATFloat
    mkIty "FInt"        = mkIntIty "ITNative"
    mkIty "FChar"       = mkIntIty "ITChar"
    mkIty "FByte"       = mkIntIty "IT8"
    mkIty "FShort"      = mkIntIty "IT16"
    mkIty "FLong"       = mkIntIty "IT64"
    mkIty "FBits8"      = mkIntIty "IT8"
    mkIty "FBits16"     = mkIntIty "IT16"
    mkIty "FBits32"     = mkIntIty "IT32"
    mkIty "FBits64"     = mkIntIty "IT64"
    mkIty "FString"     = FString
    mkIty "FPtr"        = FPtr
    mkIty "FManagedPtr" = FManagedPtr
    mkIty "FUnit"       = FUnit
    mkIty "FFunction"   = FFunction
    mkIty "FFunctionIO" = FFunctionIO
    mkIty "FBits8x16"   = FArith (ATInt (ITVec IT8 16))
    mkIty "FBits16x8"   = FArith (ATInt (ITVec IT16 8))
    mkIty "FBits32x4"   = FArith (ATInt (ITVec IT32 4))
    mkIty "FBits64x2"   = FArith (ATInt (ITVec IT64 2))
    mkIty x             = error $ "Unknown type " ++ x

    mkIntIty "ITNative" = FArith (ATInt ITNative)
    mkIntIty "ITChar" = FArith (ATInt ITChar)
    mkIntIty "IT8"  = FArith (ATInt (ITFixed IT8))
    mkIntIty "IT16" = FArith (ATInt (ITFixed IT16))
    mkIntIty "IT32" = FArith (ATInt (ITFixed IT32))
    mkIntIty "IT64" = FArith (ATInt (ITFixed IT64))

irTree :: [Name] -> SC -> Idris LExp
irTree args tree = do
    logLvl 3 $ "Compiling " ++ show args ++ "\n" ++ show tree
    LLam args <$> irSC M.empty tree

irSC :: Vars -> SC -> Idris LExp
irSC vs (STerm t) = irTerm vs [] t
irSC vs (UnmatchedCase str) = return $ LError str
irSC vs (ProjCase tm alt) = do
    tm'  <- irTerm vs [] tm
    alt' <- irAlt vs tm' alt
    return $ LCase tm' [alt']

-- There are two transformations in this case:
--
--  1. Newtype-case elimination:
--      case {e0} of
--          wrap({e1}) -> P({e1})   ==>   P({e0})
--
-- This is important because newtyped constructors are compiled away entirely
-- and we need to do that everywhere.
--
--  2. Unused-case elimination (only valid for singleton branches):
--      case {e0} of                                ==>     P
--          C(x,y) -> P[... x,y not used ...]
--
-- This is important for runtime because sometimes we case on irrelevant data:
--
-- In the example above, {e0} will most probably have been erased
-- so this vain projection would make the resulting program segfault
-- because the code generator still emits a PROJECT(...) STG instruction.
--
-- Hence, we check whether the variables are used at all
-- and erase the casesplit if they are not.
irSC vs (Case n [alt]) = do
    replacement <- case alt of
        ConCase cn a ns sc -> do
            detag <- maybe False detaggable . lookupCtxtExact cn . idris_optimisation <$> getIState
            used  <- maybe [] (map fst . usedpos) . lookupCtxtExact cn . idris_callgraph <$> getIState
            if detag && length used == 1
                then return . Just $ substSC (ns !! head used) n sc
                else return Nothing
        _ -> return Nothing

    case replacement of
        Just sc -> irSC vs sc
        _ -> do
            alt' <- irAlt vs (LV (Glob n)) alt
            return $ case namesBoundIn alt' `usedIn` subexpr alt' of
                [] -> subexpr alt'  -- strip the unused top-most case
                _  -> LCase (LV (Glob n)) [alt']
  where
    namesBoundIn :: LAlt -> [Name]
    namesBoundIn (LConCase cn i ns sc) = ns
    namesBoundIn (LConstCase c sc)     = []
    namesBoundIn (LDefaultCase sc)     = []

    subexpr :: LAlt -> LExp
    subexpr (LConCase _ _ _ e) = e
    subexpr (LConstCase _   e) = e
    subexpr (LDefaultCase   e) = e

irSC vs (Case n alts)  = LCase (LV (Glob n)) <$> mapM (irAlt vs (LV (Glob n))) alts
irSC vs ImpossibleCase = return LNothing

irAlt :: Vars -> LExp -> CaseAlt -> Idris LAlt

-- this leaves out all unused arguments of the constructor
irAlt vs _ (ConCase n t args sc) = do
    used <- getUsed . lookup n <$> getIState
    let usedArgs = [a | (i,a) <- zip [0..] args, i `elem` used]
    LConCase (-1) n usedArgs <$> irSC (methodVars `M.union` vs) sc
  where
    lookup n = lookupCtxtExact n . idris_callgraph
    getUsed  = maybe [] (map fst . usedpos)

    methodVars = case n of
        SN (InstanceCtorN className)
            -> M.fromList [(v, VI
                { viMethod = Just $ mkFieldName n i
                }) | (v,i) <- zip args [0..]]
        _
            -> M.empty -- not an instance constructor

irAlt vs _ (ConstCase x rhs)
    | matchable   x = LConstCase x <$> irSC vs rhs
    | matchableTy x = LDefaultCase <$> irSC vs rhs
  where
    matchable (I _) = True
    matchable (BI _) = True
    matchable (Ch _) = True
    matchable (Str _) = True
    matchable _ = False

    matchableTy (AType (ATInt ITNative)) = True
    matchableTy (AType (ATInt ITBig)) = True
    matchableTy (AType (ATInt ITChar)) = True
    matchableTy StrType = True

    matchableTy (AType (ATInt (ITFixed IT8)))  = True
    matchableTy (AType (ATInt (ITFixed IT16))) = True
    matchableTy (AType (ATInt (ITFixed IT32))) = True
    matchableTy (AType (ATInt (ITFixed IT64))) = True

    matchableTy _ = False

irAlt vs tm (SucCase n rhs) = do
    rhs' <- irSC vs rhs
    return $ LDefaultCase (LLet n (LOp (LMinus (ATInt ITBig))
                                            [tm,
                                            LConst (BI 1)]) rhs')

irAlt vs _ (ConstCase c rhs)
    = ifail $ "Can't match on (" ++ show c ++ ")"

irAlt vs _ (DefaultCase rhs)
    = LDefaultCase <$> irSC vs rhs

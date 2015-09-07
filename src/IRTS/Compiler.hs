{-# LANGUAGE PatternGuards, TypeSynonymInstances, CPP #-}

module IRTS.Compiler(compile, generate) where

import IRTS.Lang
import IRTS.LangOpts
import IRTS.Defunctionalise
import IRTS.Simplified
import IRTS.CodegenCommon
import IRTS.CodegenC
import IRTS.DumpBC
import IRTS.CodegenJavaScript
import IRTS.Inliner
import IRTS.Exports

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.ASTUtils
import Idris.Erasure
import Idris.Error

import Debug.Trace

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.CaseTree

import Control.Category
import Prelude hiding (id, (.))

import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.List
import Data.Ord
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S
import System.Process
import System.IO
import System.Exit
import System.Directory
import System.Environment
import System.FilePath ((</>), addTrailingPathSeparator)

-- |  Given a 'main' term to compiler, return the IRs which can be used to
-- generate code.
compile :: Codegen -> FilePath -> Maybe Term -> Idris CodegenInfo
compile codegen f mtm
   = do checkMVs  -- check for undefined metavariables
        checkTotality -- refuse to compile if there are totality problems
        exports <- findExports
        let rootNames = case mtm of
                             Nothing -> []
                             Just t -> freeNames t

        reachableNames <- performUsageAnalysis 
                              (rootNames ++ getExpNames exports)
        maindef <- case mtm of
                        Nothing -> return []
                        Just tm -> do md <- irMain tm
                                      logLvl 1 $ "MAIN: " ++ show md
                                      return [(sMN 0 "runMain", md)]
        objs <- getObjectFiles codegen
        libs <- getLibs codegen
        flags <- getFlags codegen
        hdrs <- getHdrs codegen
        impdirs <- allImportDirs
        defsIn <- mkDecls reachableNames
        -- if no 'main term' given, generate interface files
        let iface = case mtm of
                         Nothing -> True
                         Just _ -> False

        let defs = defsIn ++ maindef
        -- iputStrLn $ showSep "\n" (map show defs)
        -- Inlined top level LDecl made here
        let defsInlined = inlineAll defs
        let defsUniq = map (allocUnique (addAlist defsInlined emptyContext))
                           defsInlined

        let (nexttag, tagged) = addTags 65536 (liftAll defsUniq)
        let ctxtIn = addAlist tagged emptyContext

        logLvl 1 "Defunctionalising"
        let defuns_in = defunctionalise nexttag ctxtIn
        logLvl 5 $ show defuns_in
        logLvl 1 "Inlining"
        let defuns = inline defuns_in
        logLvl 5 $ show defuns
        logLvl 1 "Resolving variables for CG"
        -- iputStrLn $ showSep "\n" (map show (toAlist defuns))
        let checked = simplifyDefs defuns (toAlist defuns)
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
        logLvl 1 "Building output"
        case checked of
            OK c -> do return $ CodegenInfo f outty triple cpu
                                            hdrs impdirs objs libs flags
                                            NONE c (toAlist defuns)
                                            tagged iface exports
--                        runIO $ case codegen of
--                               ViaC -> codegenC cginfo
--                               ViaJava -> codegenJava cginfo
--                               ViaJavaScript -> codegenJavaScript cginfo
--                               ViaNode -> codegenNode cginfo
--                               ViaLLVM -> codegenLLVM cginfo
--                               Bytecode -> dumpBC c f
            Error e -> ierror e
  where checkMVs = do i <- getIState
                      case map fst (idris_metavars i) \\ primDefs of
                            [] -> return ()
                            ms -> ifail $ "There are undefined holes: " ++ show ms
        checkTotality = do i <- getIState
                           case idris_totcheckfail i of
                             [] -> return ()
                             ((fc, msg):fs) -> ierror . At fc . Msg $ "Cannot compile:\n  " ++ msg
        inDir d h = do let f = d </> h
                       ex <- doesFileExist f
                       if ex then return f else return h

generate :: Codegen -> FilePath -> CodegenInfo -> IO ()
generate codegen mainmod ir
  = case codegen of
       -- Built-in code generators (FIXME: lift these out!)
       Via "c" -> codegenC ir
       -- Any external code generator
       Via cg -> do let cmd = "idris-codegen-" ++ cg
                        args = ["--yes-really", mainmod, "-o", outputFile ir] ++ compilerFlags ir
                    exit <- rawSystem cmd args
                    when (exit /= ExitSuccess) $
                       putStrLn ("FAILURE: " ++ show cmd ++ " " ++ show args)
       Bytecode -> dumpBC (simpleDecls ir) (outputFile ir)

irMain :: TT Name -> Idris LDecl
irMain tm = do
    i <- irTerm M.empty [] tm
    return $ LFun [] (sMN 0 "runMain") [] (LForce i)

mkDecls :: [Name] -> Idris [(Name, LDecl)]
mkDecls used
    = do i <- getIState
         let ds = filter (\(n, d) -> n `elem` used || isCon d) $ ctxtAlist (tt_ctxt i)
         decls <- mapM build ds
         return decls

showCaseTrees :: [(Name, LDecl)] -> String
showCaseTrees = showSep "\n\n" . map showCT . sortBy (comparing defnRank)
  where
    showCT (n, LFun _ f args lexp)
       = show n ++ " " ++ showSep " " (map show args) ++ " =\n\t"
            ++ show lexp
    showCT (n, LConstructor c t a) = "data " ++ show n ++ " " ++ show a

    defnRank :: (Name, LDecl) -> String
    defnRank (n, LFun _ _ _ _)       = "1" ++ nameRank n
    defnRank (n, LConstructor _ _ _) = "2" ++ nameRank n

    nameRank :: Name -> String
    nameRank (UN s)   = "1" ++ show s
    nameRank (MN i s) = "2" ++ show s ++ show i
    nameRank (NS n ns) = "3" ++ concatMap show (reverse ns) ++ nameRank n
    nameRank (SN sn) = "4" ++ snRank sn
    nameRank n = "5" ++ show n

    snRank :: SpecialName -> String
    snRank (WhereN i n n') = "1" ++ nameRank n' ++ nameRank n ++ show i
    snRank (InstanceN n args) = "2" ++ nameRank n ++ concatMap show args
    snRank (ParentN n s) = "3" ++ nameRank n ++ show s
    snRank (MethodN n) = "4" ++ nameRank n
    snRank (CaseN n) = "5" ++ nameRank n
    snRank (ElimN n) = "6" ++ nameRank n
    snRank (InstanceCtorN n) = "7" ++ nameRank n
    snRank (WithN i n) = "8" ++ nameRank n ++ show i

isCon (TyDecl _ _) = True
isCon _ = False

build :: (Name, Def) -> Idris (Name, LDecl)
build (n, d)
    = do i <- getIState
         case getPrim n i of
              Just (ar, op) ->
                  let args = map (\x -> sMN x "op") [0..] in
                      return (n, (LFun [] n (take ar args)
                                         (LOp op (map (LV . Glob) (take ar args)))))
              _ -> do def <- mkLDecl n d
                      logLvl 3 $ "Compiled " ++ show n ++ " =\n\t" ++ show def
                      return (n, def)
   where getPrim n i 
             | Just (ar, op) <- lookup n (idris_scprims i) 
                  = Just (ar, op)
             | Just ar <- lookup n (S.toList (idris_externs i))
                  = Just (ar, LExternal n)
         getPrim n i = Nothing

declArgs args inl n (LLam xs x) = declArgs (args ++ xs) inl n x
declArgs args inl n x = LFun (if inl then [Inline] else []) n args x

mkLDecl n (Function tm _)
    = declArgs [] True n <$> irTerm M.empty [] tm

mkLDecl n (CaseOp ci _ _ _ pats cd)
    = declArgs [] (case_inlinable ci || caseName n) n <$> irTree args sc
  where
    (args, sc) = cases_runtime cd

    -- Always attempt to inline functions arising from 'case' expressions
    caseName (SN (CaseN _)) = True
    caseName (SN (WithN _ _)) = True
    caseName (NS n _) = caseName n
    caseName _ = False

mkLDecl n (TyDecl (DCon tag arity _) _) =
    LConstructor n tag . length <$> fgetState (cg_usedpos . ist_callgraph n)

mkLDecl n (TyDecl (TCon t a) _) = return $ LConstructor n (-1) a
mkLDecl n _ = return $ (declArgs [] True n LNothing) -- postulate, never run

data VarInfo = VI
    { viMethod :: Maybe Name
    }
    deriving Show

type Vars = M.Map Name VarInfo

irTerm :: Vars -> [Name] -> Term -> Idris LExp
irTerm vs env tm@(App _ f a) = do 
  ist <- getIState
  case unApply tm of
    (P _ (UN m) _, args)
        | m == txt "mkForeignPrim"
        -> doForeign vs env (reverse (drop 4 args)) -- drop implicits

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

    (P _ (UN a) _, [_, _, _, arg])
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
    (P _ (NS (UN be) [b,p]) _, [_,x,(App _ (App _ (App _ (P _ (UN d) _) _) _) t),
                                    (App _ (App _ (App _ (P _ (UN d') _) _) _) e)])
        | be == txt "ifThenElse"
        , d  == txt "Delay"
        , d' == txt "Delay"
        , b  == txt "Bool"
        , p  == txt "Prelude"
        -> do
            x' <- irTerm vs env x
            t' <- irTerm vs env t
            e' <- irTerm vs env e
            return (LCase Shared x'
                             [LConCase 0 (sNS (sUN "False") ["Bool","Prelude"]) [] e'
                             ,LConCase 1 (sNS (sUN "True" ) ["Bool","Prelude"]) [] t'
                             ])

    -- data constructor
    (P (DCon t arity _) n _, args) -> do
        detag <- fgetState (opt_detaggable . ist_optimisation n)
        used  <- map fst <$> fgetState (cg_usedpos . ist_callgraph n)

        let isNewtype = length used == 1 && detag
        let argsPruned = [a | (i,a) <- zip [0..] args, i `elem` used]

        -- The following code removes fields from data constructors
        -- and performs the newtype optimisation.
        --
        -- The general rule here is:
        -- Everything we get as input is not touched by erasure,
        -- so it conforms to the official arities and types
        -- and we can reason about it like it's plain TT.
        --
        -- It's only the data that leaves this point that's erased
        -- and possibly no longer typed as the original TT version.
        --
        -- Especially, underapplied constructors must yield functions
        -- even if all the remaining arguments are erased
        -- (the resulting function *will* be applied, to NULLs).
        --
        -- This will probably need rethinking when we get erasure from functions.

        -- "padLams" will wrap our term in LLam-bdas and give us
        -- the "list of future unerased args" coming from these lambdas.
        --
        -- We can do whatever we like with the list of unerased args,
        -- hence it takes a lambda: \unerased_argname_list -> resulting_LExp.
        let padLams = padLambdas used (length args) arity

        case compare (length args) arity of

            -- overapplied
            GT  -> ifail ("overapplied data constructor: " ++ show tm)

            -- exactly saturated
            EQ  | isNewtype
                -> irTerm vs env (head argsPruned)

                | otherwise  -- not newtype, plain data ctor
                -> buildApp (LV $ Glob n) argsPruned

            -- not saturated, underapplied
            LT  | isNewtype               -- newtype
                , length argsPruned == 1  -- and we already have the value
                -> padLams . (\tm [] -> tm)  -- the [] asserts there are no unerased args
                    <$> irTerm vs env (head argsPruned)

                | isNewtype  -- newtype but the value is not among args yet
                -> return . padLams $ \[vn] -> LApp False (LV $ Glob n) [LV $ Glob vn]

                -- not a newtype, just apply to a constructor
                | otherwise
                -> padLams . applyToNames <$> buildApp (LV $ Glob n) argsPruned

    -- type constructor
    (P (TCon t a) n _, args) -> return LNothing

    -- an external name applied to arguments
    (P _ n _, args) | S.member (n, length args) (idris_externs ist) -> do
        LOp (LExternal n) <$> mapM (irTerm vs env) args

    -- a name applied to arguments
    (P _ n _, args) -> do
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
    buildApp :: LExp -> [Term] -> Idris LExp
    buildApp e [] = return e
    buildApp e xs = LApp False e <$> mapM (irTerm vs env) xs

    applyToNames :: LExp -> [Name] -> LExp
    applyToNames tm [] = tm
    applyToNames tm ns = LApp False tm $ map (LV . Glob) ns

    padLambdas :: [Int] -> Int -> Int -> ([Name] -> LExp) -> LExp
    padLambdas used startIdx endSIdx mkTerm
        = LLam allNames $ mkTerm nonerasedNames
      where
        allNames       = [sMN i "sat" | i <- [startIdx .. endSIdx-1]]
        nonerasedNames = [sMN i "sat" | i <- [startIdx .. endSIdx-1], i `elem` used]

    applyName :: Name -> IState -> [Term] -> Idris LExp
    applyName n ist args =
        LApp False (LV $ Glob n) <$> mapM (irTerm vs env . erase) (zip [0..] args)
      where
        erase (i, x)
            | i >= arity || i `elem` used = x
            | otherwise = Erased

        arity = case fst4 <$> lookupCtxtExact n (definitions . tt_ctxt $ ist) of
            Just (CaseOp ci ty tys def tot cdefs) -> length tys
            Just (TyDecl (DCon tag ar _) _)       -> ar
            Just (TyDecl Ref ty)                  -> length $ getArgTys ty
            Just (Operator ty ar op)              -> ar
            Just def -> error $ "unknown arity: " ++ show (n, def)
            Nothing  -> 0  -- no definition, probably local name => can't erase anything

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
irTerm vs env (Constant TheWorld) = return $ LNothing
irTerm vs env (Constant c) = return $ LConst c
irTerm vs env (TType _)    = return $ LNothing
irTerm vs env Erased       = return $ LNothing
irTerm vs env Impossible   = return $ LNothing

doForeign :: Vars -> [Name] -> [Term] -> Idris LExp
doForeign vs env (ret : fname : world : args)
     = do args' <- mapM splitArg args
          let fname' = toFDesc fname 
          let ret' = toFDesc ret
          return $ LForeign ret' fname' args'
  where
    splitArg tm | (_, [_,_,l,r]) <- unApply tm -- pair, two implicits
        = do let l' = toFDesc l 
             r' <- irTerm vs env r
             return (l', r')
    splitArg _ = ifail "Badly formed foreign function call"

    toFDesc (Constant (Str str)) = FStr str 
    toFDesc tm 
       | (P _ n _, []) <- unApply tm = FCon (deNS n) 
       | (P _ n _, as) <- unApply tm = FApp (deNS n) (map toFDesc as)
    toFDesc _ = FUnknown

    deNS (NS n _) = n
    deNS n = n
doForeign vs env xs = ifail "Badly formed foreign function call"

{-
 - | (_, (Constant (Str fgnName) : fgnArgTys : ret : [])) <- unApply fgn
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
    -- Issue #1742 on the issue tracker.
    --     https://github.com/idris-lang/Idris-dev/issues/1742
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
-}

irTree :: [Name] -> SC -> Idris LExp
irTree args tree = do
    logLvl 3 $ "Compiling " ++ show args ++ "\n" ++ show tree
    LLam args <$> irSC M.empty tree

irSC :: Vars -> SC -> Idris LExp
irSC vs (STerm t) = irTerm vs [] t
irSC vs (UnmatchedCase str) = return $ LError str

irSC vs (ProjCase tm alts) = do
    tm'   <- irTerm vs [] tm
    alts' <- mapM (irAlt vs tm') alts
    return $ LCase Shared tm' alts'

-- Transform matching on Delay to applications of Force.
irSC vs (Case up n [ConCase (UN delay) i [_, _, n'] sc])
    | delay == txt "Delay"
    = do sc' <- irSC vs $ mkForce n' n sc
         return $ LLet n' (LForce (LV (Glob n))) sc'

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
-- because the code generator still emits a PROJECT(...) G-machine instruction.
--
-- Hence, we check whether the variables are used at all
-- and erase the casesplit if they are not.
--
irSC vs (Case up n [alt]) = do
    replacement <- case alt of
        ConCase cn a ns sc -> do
            detag <- fgetState (opt_detaggable . ist_optimisation cn)
            used  <- map fst <$> fgetState (cg_usedpos . ist_callgraph cn)
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
                _  -> LCase up (LV (Glob n)) [alt']
  where
    namesBoundIn :: LAlt -> [Name]
    namesBoundIn (LConCase cn i ns sc) = ns
    namesBoundIn (LConstCase c sc)     = []
    namesBoundIn (LDefaultCase sc)     = []

    subexpr :: LAlt -> LExp
    subexpr (LConCase _ _ _ e) = e
    subexpr (LConstCase _   e) = e
    subexpr (LDefaultCase   e) = e

-- FIXME: When we have a non-singleton case-tree of the form
--
--     case {e0} of
--         C(x) => ...
--         ...  => ...
--
-- and C is detaggable (the only constructor of the family), we can be sure
-- that the first branch will be always taken -- so we add special handling
-- to remove the dead default branch.
--
-- If we don't do so and C is newtype-optimisable, we will miss this newtype
-- transformation and the resulting code will probably segfault.
--
-- This work-around is not entirely optimal; the best approach would be
-- to ensure that such case trees don't arise in the first place.
--
irSC vs (Case up n alts@[ConCase cn a ns sc, DefaultCase sc']) = do
    detag <- fgetState (opt_detaggable . ist_optimisation cn)
    if detag
        then irSC vs (Case up n [ConCase cn a ns sc])
        else LCase up (LV (Glob n)) <$> mapM (irAlt vs (LV (Glob n))) alts

irSC vs sc@(Case up n alts) = do
    -- check that neither alternative needs the newtype optimisation,
    -- see comment above
    goneWrong <- or <$> mapM isDetaggable alts
    when goneWrong
        $ ifail ("irSC: non-trivial case-match on detaggable data: " ++ show sc)

    -- everything okay
    LCase up (LV (Glob n)) <$> mapM (irAlt vs (LV (Glob n))) alts
  where
    isDetaggable (ConCase cn _ _ _) = fgetState $ opt_detaggable . ist_optimisation cn
    isDetaggable  _                 = return False

irSC vs ImpossibleCase = return LNothing

irAlt :: Vars -> LExp -> CaseAlt -> Idris LAlt

-- this leaves out all unused arguments of the constructor
irAlt vs _ (ConCase n t args sc) = do
    used <- map fst <$> fgetState (cg_usedpos . ist_callgraph n)
    let usedArgs = [a | (i,a) <- zip [0..] args, i `elem` used]
    LConCase (-1) n usedArgs <$> irSC (methodVars `M.union` vs) sc
  where
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
    matchable (B8 _) = True
    matchable (B16 _) = True
    matchable (B32 _) = True
    matchable (B64 _) = True
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

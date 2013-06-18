{-# LANGUAGE TypeSynonymInstances #-}

module Idris.IBC where

import Core.Evaluate
import Core.TT
import Core.CaseTree
import Idris.Compiler
import Idris.AbsSyntax
import Idris.Imports
import Idris.Error

import Data.Binary
import Data.List
import Data.ByteString.Lazy as B hiding (length, elem)
import Control.Monad
import Control.Monad.State hiding (get, put)
import System.FilePath
import System.Directory

import Debug.Trace

import Paths_idris

ibcVersion :: Word8
ibcVersion = 30

data IBCFile = IBCFile { ver :: Word8,
                         sourcefile :: FilePath,
                         ibc_imports :: [FilePath],
                         ibc_implicits :: [(Name, [PArg])],
                         ibc_fixes :: [FixDecl],
                         ibc_statics :: [(Name, [Bool])],
                         ibc_classes :: [(Name, ClassInfo)],
                         ibc_instances :: [(Bool, Name, Name)],
                         ibc_dsls :: [(Name, DSL)],
                         ibc_datatypes :: [(Name, TypeInfo)],
                         ibc_optimise :: [(Name, OptInfo)],
                         ibc_syntax :: [Syntax],
                         ibc_keywords :: [String],
                         ibc_objs :: [(Target, FilePath)],
                         ibc_libs :: [(Target, String)],
                         ibc_dynamic_libs :: [String],
                         ibc_hdrs :: [(Target, String)],
                         ibc_access :: [(Name, Accessibility)],
                         ibc_total :: [(Name, Totality)],
                         ibc_flags :: [(Name, [FnOpt])],
                         ibc_cg :: [(Name, CGInfo)],
                         ibc_defs :: [(Name, Def)],
                         ibc_docstrings :: [(Name, String)],
                         ibc_coercions :: [Name]
                       }
   deriving Show
{-! 
deriving instance Binary IBCFile 
!-}

initIBC :: IBCFile
initIBC = IBCFile ibcVersion "" [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []

loadIBC :: FilePath -> Idris ()
loadIBC fp = do iLOG $ "Loading ibc " ++ fp
                ibcf <- liftIO $ (decodeFile fp :: IO IBCFile)
                process ibcf fp

writeIBC :: FilePath -> FilePath -> Idris ()
writeIBC src f 
    = do iLOG $ "Writing ibc " ++ show f
         i <- getIState
         case idris_metavars i \\ primDefs of
                (_:_) -> fail "Can't write ibc when there are unsolved metavariables"
                [] -> return ()
         ibcf <- mkIBC (ibc_write i) (initIBC { sourcefile = src }) 
         idrisCatch (do liftIO $ createDirectoryIfMissing True (dropFileName f)
                        liftIO $ encodeFile f ibcf
                        iLOG "Written")
            (\c -> do iLOG $ "Failed " ++ show c)
         return ()

mkIBC :: [IBCWrite] -> IBCFile -> Idris IBCFile
mkIBC [] f = return f
mkIBC (i:is) f = do ist <- getIState
                    logLvl 5 $ show i ++ " " ++ show (Data.List.length is)
                    f' <- ibc ist i f
                    mkIBC is f'

ibc i (IBCFix d) f = return f { ibc_fixes = d : ibc_fixes f } 
ibc i (IBCImp n) f = case lookupCtxt n (idris_implicits i) of
                        [v] -> return f { ibc_implicits = (n,v): ibc_implicits f     }
                        _ -> fail "IBC write failed"
ibc i (IBCStatic n) f 
                   = case lookupCtxt n (idris_statics i) of
                        [v] -> return f { ibc_statics = (n,v): ibc_statics f     }
                        _ -> fail "IBC write failed"
ibc i (IBCClass n) f 
                   = case lookupCtxt n (idris_classes i) of
                        [v] -> return f { ibc_classes = (n,v): ibc_classes f     }
                        _ -> fail "IBC write failed"
ibc i (IBCInstance int n ins) f 
                   = return f { ibc_instances = (int,n,ins): ibc_instances f     }
ibc i (IBCDSL n) f 
                   = case lookupCtxt n (idris_dsls i) of
                        [v] -> return f { ibc_dsls = (n,v): ibc_dsls f     }
                        _ -> fail "IBC write failed"
ibc i (IBCData n) f 
                   = case lookupCtxt n (idris_datatypes i) of
                        [v] -> return f { ibc_datatypes = (n,v): ibc_datatypes f     }
                        _ -> fail "IBC write failed"
ibc i (IBCOpt n) f = case lookupCtxt n (idris_optimisation i) of
                        [v] -> return f { ibc_optimise = (n,v): ibc_optimise f     }
                        _ -> fail "IBC write failed"
ibc i (IBCSyntax n) f = return f { ibc_syntax = n : ibc_syntax f }
ibc i (IBCKeyword n) f = return f { ibc_keywords = n : ibc_keywords f }
ibc i (IBCImport n) f = return f { ibc_imports = n : ibc_imports f }
ibc i (IBCObj tgt n) f = return f { ibc_objs = (tgt, n) : ibc_objs f }
ibc i (IBCLib tgt n) f = return f { ibc_libs = (tgt, n) : ibc_libs f }
ibc i (IBCDyLib n) f = return f {ibc_dynamic_libs = n : ibc_dynamic_libs f }
ibc i (IBCHeader tgt n) f = return f { ibc_hdrs = (tgt, n) : ibc_hdrs f }
ibc i (IBCDef n) f = case lookupDef n (tt_ctxt i) of
                        [v] -> return f { ibc_defs = (n,v) : ibc_defs f     }
                        _ -> fail "IBC write failed"
ibc i (IBCDoc n) f = case lookupCtxt n (idris_docstrings i) of
                        [v] -> return f { ibc_docstrings = (n,v) : ibc_docstrings f }
                        _ -> fail "IBC write failed"
ibc i (IBCCG n) f = case lookupCtxt n (idris_callgraph i) of
                        [v] -> return f { ibc_cg = (n,v) : ibc_cg f     }
                        _ -> fail "IBC write failed"
ibc i (IBCCoercion n) f = return f { ibc_coercions = n : ibc_coercions f }
ibc i (IBCAccess n a) f = return f { ibc_access = (n,a) : ibc_access f }
ibc i (IBCFlags n a) f = return f { ibc_flags = (n,a) : ibc_flags f }
ibc i (IBCTotal n a) f = return f { ibc_total = (n,a) : ibc_total f }

process :: IBCFile -> FilePath -> Idris ()
process i fn
   | ver i /= ibcVersion = do iLOG "ibc out of date"
                              fail "Incorrect ibc version"
   | otherwise =
            do srcok <- liftIO $ doesFileExist (sourcefile i)
               when srcok $ liftIO $ timestampOlder (sourcefile i) fn
               v <- verbose
               quiet <- getQuiet
               when (v && srcok && not quiet) $ iputStrLn $ "Skipping " ++ sourcefile i
               pImports (ibc_imports i)
               pImps (ibc_implicits i)
               pFixes (ibc_fixes i)
               pStatics (ibc_statics i)
               pClasses (ibc_classes i)
               pInstances (ibc_instances i)
               pDSLs (ibc_dsls i)
               pDatatypes (ibc_datatypes i)
               pOptimise (ibc_optimise i)
               pSyntax (ibc_syntax i)
               pKeywords (ibc_keywords i)
               pObjs (ibc_objs i)
               pLibs (ibc_libs i)
               pDyLibs (ibc_dynamic_libs i)
               pHdrs (ibc_hdrs i)
               pDefs (ibc_defs i)
               pAccess (ibc_access i)
               pTotal (ibc_total i)
               pCG (ibc_cg i)
               pDocs (ibc_docstrings i)
               pCoercions (ibc_coercions i)

timestampOlder :: FilePath -> FilePath -> IO ()
timestampOlder src ibc = do srct <- getModificationTime src
                            ibct <- getModificationTime ibc
                            if (srct > ibct)
                               then fail "Needs reloading"
                               else return ()

pImports :: [FilePath] -> Idris ()
pImports fs 
  = do mapM_ (\f -> do i <- getIState
                       ibcsd <- valIBCSubDir i
                       ids <- allImportDirs i
                       fp <- liftIO $ findImport ids ibcsd f
                       if (f `elem` imported i)
                        then iLOG $ "Already read " ++ f
                        else do putIState (i { imported = f : imported i })
                                case fp of 
                                    LIDR fn -> do iLOG $ "Failed at " ++ fn
                                                  fail "Must be an ibc"
                                    IDR fn -> do iLOG $ "Failed at " ++ fn
                                                 fail "Must be an ibc"
                                    IBC fn src -> loadIBC fn) 
             fs

pImps :: [(Name, [PArg])] -> Idris ()
pImps imps = mapM_ (\ (n, imp) -> 
                        do i <- getIState
                           putIState (i { idris_implicits 
                                            = addDef n imp (idris_implicits i) }))
                   imps

pFixes :: [FixDecl] -> Idris ()
pFixes f = do i <- getIState
              putIState (i { idris_infixes = sort $ f ++ idris_infixes i })

pStatics :: [(Name, [Bool])] -> Idris ()
pStatics ss = mapM_ (\ (n, s) ->
                        do i <- getIState
                           putIState (i { idris_statics
                                           = addDef n s (idris_statics i) }))
                    ss

pClasses :: [(Name, ClassInfo)] -> Idris ()
pClasses cs = mapM_ (\ (n, c) ->
                        do i <- getIState
                           putIState (i { idris_classes
                                           = addDef n c (idris_classes i) }))
                    cs

pInstances :: [(Bool, Name, Name)] -> Idris ()
pInstances cs = mapM_ (\ (i, n, ins) -> addInstance i n ins) cs

pDSLs :: [(Name, DSL)] -> Idris ()
pDSLs cs = mapM_ (\ (n, c) ->
                        do i <- getIState
                           putIState (i { idris_dsls
                                           = addDef n c (idris_dsls i) }))
                    cs

pDatatypes :: [(Name, TypeInfo)] -> Idris ()
pDatatypes cs = mapM_ (\ (n, c) ->
                        do i <- getIState
                           putIState (i { idris_datatypes
                                           = addDef n c (idris_datatypes i) }))
                    cs

pOptimise :: [(Name, OptInfo)] -> Idris ()
pOptimise cs = mapM_ (\ (n, c) ->
                        do i <- getIState
                           putIState (i { idris_optimisation
                                           = addDef n c (idris_optimisation i) }))
                    cs

pSyntax :: [Syntax] -> Idris ()
pSyntax s = do i <- getIState
               putIState (i { syntax_rules = s ++ syntax_rules i })

pKeywords :: [String] -> Idris ()
pKeywords k = do i <- getIState
                 putIState (i { syntax_keywords = k ++ syntax_keywords i })

pObjs :: [(Target, FilePath)] -> Idris ()
pObjs os = mapM_ (uncurry addObjectFile) os

pLibs :: [(Target, String)] -> Idris ()
pLibs ls = mapM_ (uncurry addLib) ls

pDyLibs :: [String] -> Idris ()
pDyLibs ls = do res <- mapM (addDyLib . return) ls
                mapM_ checkLoad res
                return ()
    where checkLoad (Left _) = return ()
          checkLoad (Right err) = fail err

pHdrs :: [(Target, String)] -> Idris ()
pHdrs hs = mapM_ (uncurry addHdr) hs

pDefs :: [(Name, Def)] -> Idris ()
pDefs ds = mapM_ (\ (n, d) -> 
                     do i <- getIState
                        logLvl 5 $ "Added " ++ show (n, d)
                        putIState (i { tt_ctxt = addCtxtDef n d (tt_ctxt i) }))
                 ds       

pDocs :: [(Name, String)] -> Idris ()
pDocs ds = mapM_ (\ (n, a) -> addDocStr n a) ds

pAccess :: [(Name, Accessibility)] -> Idris ()
pAccess ds = mapM_ (\ (n, a) ->
                      do i <- getIState
                         putIState (i { tt_ctxt = setAccess n a (tt_ctxt i) }))
                   ds

pFlags :: [(Name, [FnOpt])] -> Idris ()
pFlags ds = mapM_ (\ (n, a) -> setFlags n a) ds

pTotal :: [(Name, Totality)] -> Idris ()
pTotal ds = mapM_ (\ (n, a) ->
                      do i <- getIState
                         putIState (i { tt_ctxt = setTotal n a (tt_ctxt i) }))
                   ds

pCG :: [(Name, CGInfo)] -> Idris ()
pCG ds = mapM_ (\ (n, a) -> addToCG n a) ds

pCoercions :: [Name] -> Idris ()
pCoercions ns = mapM_ (\ n -> addCoercion n) ns

----- Generated by 'derive'

instance Binary SizeChange where
        put x
          = case x of
                Smaller -> putWord8 0
                Same -> putWord8 1
                Bigger -> putWord8 2
                Unknown -> putWord8 3
        get
          = do i <- getWord8
               case i of
                   0 -> return Smaller
                   1 -> return Same
                   2 -> return Bigger
                   3 -> return Unknown
                   _ -> error "Corrupted binary data for SizeChange"

instance Binary CGInfo where
        put (CGInfo x1 x2 x3 x4 x5)
          = do put x1
               put x2
               put x3
               put x4
               put x5
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               x4 <- get
               x5 <- get
               return (CGInfo x1 x2 x3 x4 x5)

instance Binary FC where
        put (FC x1 x2)
          = do put x1
               put x2
        get
          = do x1 <- get
               x2 <- get
               return (FC x1 x2)

 
instance Binary Name where
        put x
          = {-# SCC "putName" #-}
            case x of
                UN x1 -> {-# SCC "putUN" #-}
                         do putWord8 0
                            {-# SCC "putNString" #-} put x1
                NS x1 x2 -> {-# SCC "putNS" #-}
                            do putWord8 1
                               put x1
                               put x2
                MN x1 x2 -> {-# SCC "putMN" #-}
                            do putWord8 2
                               put x1
                               put x2
                NErased -> {-# SCC "putNErased" #-}
                         putWord8 3
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (UN x1)
                   1 -> do x1 <- get
                           x2 <- get
                           return (NS x1 x2)
                   2 -> do x1 <- get
                           x2 <- get
                           return (MN x1 x2)
                   3 -> return NErased
                   _ -> error "Corrupted binary data for Name"


instance Binary Const where
        put x
          = case x of
                I x1 -> do putWord8 0
                           put x1
                BI x1 -> do putWord8 1
                            put x1
                Fl x1 -> do putWord8 2
                            put x1
                Ch x1 -> do putWord8 3
                            put x1
                Str x1 -> do putWord8 4
                             put x1
                B8 x1 -> putWord8 5 >> put x1
                B16 x1 -> putWord8 6 >> put x1
                B32 x1 -> putWord8 7 >> put x1
                B64 x1 -> putWord8 8 >> put x1

                (AType (ATInt ITNative)) -> putWord8 9
                (AType (ATInt ITBig)) -> putWord8 10
                (AType ATFloat) -> putWord8 11
                ChType -> putWord8 12
                StrType -> putWord8 13
                PtrType -> putWord8 14
                Forgot -> putWord8 15
                (AType (ATInt (ITFixed ity))) -> put (16 + fromEnum ity) -- 16-19 inclusive
                (AType (ATInt (ITVec ity count))) -> do
                        putWord8 20
                        putWord8 (fromIntegral . fromEnum $ ity)
                        putWord8 (fromIntegral count)
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (I x1)
                   1 -> do x1 <- get
                           return (BI x1)
                   2 -> do x1 <- get
                           return (Fl x1)
                   3 -> do x1 <- get
                           return (Ch x1)
                   4 -> do x1 <- get
                           return (Str x1)
                   5 -> fmap B8 get
                   6 -> fmap B16 get
                   7 -> fmap B32 get
                   8 -> fmap B64 get

                   9 -> return (AType (ATInt ITNative))
                   10 -> return (AType (ATInt ITBig))
                   11 -> return (AType ATFloat)
                   12 -> return ChType
                   13 -> return StrType
                   14 -> return PtrType
                   15 -> return Forgot

                   16 -> return (AType (ATInt (ITFixed IT8)))
                   17 -> return (AType (ATInt (ITFixed IT16)))
                   18 -> return (AType (ATInt (ITFixed IT32)))
                   19 -> return (AType (ATInt (ITFixed IT64)))

                   20 -> do
                        e <- getWord8
                        c <- getWord8
                        return (AType (ATInt (ITVec (toEnum . fromIntegral $ e) (fromIntegral c))))

                   _ -> error "Corrupted binary data for Const"

 
instance Binary Raw where
        put x
          = case x of
                Var x1 -> do putWord8 0
                             put x1
                RBind x1 x2 x3 -> do putWord8 1
                                     put x1
                                     put x2
                                     put x3
                RApp x1 x2 -> do putWord8 2
                                 put x1
                                 put x2
                RType -> putWord8 3
                RConstant x1 -> do putWord8 4
                                   put x1
                RForce x1 -> do putWord8 5
                                put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Var x1)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (RBind x1 x2 x3)
                   2 -> do x1 <- get
                           x2 <- get
                           return (RApp x1 x2)
                   3 -> return RType
                   4 -> do x1 <- get
                           return (RConstant x1)
                   5 -> do x1 <- get
                           return (RForce x1)
                   _ -> error "Corrupted binary data for Raw"

 
instance (Binary b) => Binary (Binder b) where
        put x
          = case x of
                Lam x1 -> do putWord8 0
                             put x1
                Pi x1 -> do putWord8 1
                            put x1
                Let x1 x2 -> do putWord8 2
                                put x1
                                put x2
                NLet x1 x2 -> do putWord8 3
                                 put x1
                                 put x2
                Hole x1 -> do putWord8 4
                              put x1
                GHole x1 -> do putWord8 5
                               put x1
                Guess x1 x2 -> do putWord8 6
                                  put x1
                                  put x2
                PVar x1 -> do putWord8 7
                              put x1
                PVTy x1 -> do putWord8 8
                              put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Lam x1)
                   1 -> do x1 <- get
                           return (Pi x1)
                   2 -> do x1 <- get
                           x2 <- get
                           return (Let x1 x2)
                   3 -> do x1 <- get
                           x2 <- get
                           return (NLet x1 x2)
                   4 -> do x1 <- get
                           return (Hole x1)
                   5 -> do x1 <- get
                           return (GHole x1)
                   6 -> do x1 <- get
                           x2 <- get
                           return (Guess x1 x2)
                   7 -> do x1 <- get
                           return (PVar x1)
                   8 -> do x1 <- get
                           return (PVTy x1)
                   _ -> error "Corrupted binary data for Binder"

 
instance Binary NameType where
        put x
          = case x of
                Bound -> putWord8 0
                Ref -> putWord8 1
                DCon x1 x2 -> do putWord8 2
                                 put x1
                                 put x2
                TCon x1 x2 -> do putWord8 3
                                 put x1
                                 put x2
        get
          = do i <- getWord8
               case i of
                   0 -> return Bound
                   1 -> return Ref
                   2 -> do x1 <- get
                           x2 <- get
                           return (DCon x1 x2)
                   3 -> do x1 <- get
                           x2 <- get
                           return (TCon x1 x2)
                   _ -> error "Corrupted binary data for NameType"


instance {-(Binary n) =>-} Binary (TT Name) where
        put x
          = {-# SCC "putTT" #-} 
            case x of
                P x1 x2 x3 -> do putWord8 0
                                 put x1
                                 put x2
                                 put x3
                V x1 -> do putWord8 1
                           put x1
                Bind x1 x2 x3 -> do putWord8 2
                                    put x1
                                    put x2
                                    put x3
                App x1 x2 -> do putWord8 3
                                put x1
                                put x2
                Constant x1 -> do putWord8 4
                                  put x1
                Proj x1 x2 -> do putWord8 5
                                 put x1
                                 put x2
                Erased -> putWord8 6
                TType x1 -> do putWord8 7
                               put x1
                Impossible -> putWord8 8
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (P x1 x2 x3)
                   1 -> do x1 <- get
                           return (V x1)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Bind x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           return (App x1 x2)
                   4 -> do x1 <- get
                           return (Constant x1)
                   5 -> do x1 <- get
                           x2 <- get
                           return (Proj x1 x2)
                   6 -> return Erased
                   7 -> do x1 <- get
                           return (TType x1)
                   8 -> return Impossible
                   _ -> error "Corrupted binary data for TT"

instance Binary SC where
        put x
          = case x of
                Case x1 x2 -> do putWord8 0
                                 put x1
                                 put x2
                ProjCase x1 x2 -> do putWord8 1
                                     put x1
                                     put x2
                STerm x1 -> do putWord8 2
                               put x1
                UnmatchedCase x1 -> do putWord8 3
                                       put x1
                ImpossibleCase -> do putWord8 4
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           return (Case x1 x2)
                   1 -> do x1 <- get
                           x2 <- get
                           return (ProjCase x1 x2)
                   2 -> do x1 <- get
                           return (STerm x1)
                   3 -> do x1 <- get
                           return (UnmatchedCase x1)
                   4 -> return ImpossibleCase
                   _ -> error "Corrupted binary data for SC" 

 
instance Binary CaseAlt where
        put x
          = {-# SCC "putCaseAlt" #-} 
            case x of
                ConCase x1 x2 x3 x4 -> do putWord8 0
                                          put x1
                                          put x2
                                          put x3
                                          put x4
                ConstCase x1 x2 -> do putWord8 1
                                      put x1
                                      put x2
                DefaultCase x1 -> do putWord8 2
                                     put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (ConCase x1 x2 x3 x4)
                   1 -> do x1 <- get
                           x2 <- get
                           return (ConstCase x1 x2)
                   2 -> do x1 <- get
                           return (DefaultCase x1)
                   _ -> error "Corrupted binary data for CaseAlt"

 
instance Binary Def where
        put x
          = {-# SCC "putDef" #-} 
            case x of
                Function x1 x2 -> do putWord8 0
                                     put x1
                                     put x2
                TyDecl x1 x2 -> do putWord8 1
                                   put x1
                                   put x2
                -- all primitives just get added at the start, don't write
                Operator x1 x2 x3 -> do return ()
                CaseOp x1 x2 x3 x3a x4 x5 x6 x7 x8 -> 
                                               do putWord8 3
                                                  put x1
                                                  put x2
                                                  put x3
                                                  -- no x3a
                                                  put x4
                                                  put x5
                                                  put x6
                                                  put x7
                                                  put x8
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           return (Function x1 x2)
                   1 -> do x1 <- get
                           x2 <- get
                           return (TyDecl x1 x2)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Operator x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           -- x3 <- get always []
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           x7 <- get
                           x8 <- get
                           return (CaseOp x1 x2 x3 [] x4 x5 x6 x7 x8)
                   _ -> error "Corrupted binary data for Def"

instance Binary Accessibility where
        put x
          = case x of
                Public -> putWord8 0
                Frozen -> putWord8 1
                Hidden -> putWord8 2
        get
          = do i <- getWord8
               case i of
                   0 -> return Public
                   1 -> return Frozen
                   2 -> return Hidden
                   _ -> error "Corrupted binary data for Accessibility"

instance Binary PReason where
        put x
          = case x of
                Other x1 -> do putWord8 0
                               put x1
                Itself -> putWord8 1
                NotCovering -> putWord8 2
                NotPositive -> putWord8 3
                Mutual x1 -> do putWord8 4
                                put x1
                NotProductive -> putWord8 5
                BelieveMe -> putWord8 6
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Other x1)
                   1 -> return Itself
                   2 -> return NotCovering
                   3 -> return NotPositive
                   4 -> do x1 <- get
                           return (Mutual x1)
                   5 -> return NotProductive
                   6 -> return BelieveMe
                   _ -> error "Corrupted binary data for PReason"

instance Binary Totality where
        put x
          = case x of
                Total x1 -> do putWord8 0
                               put x1
                Partial x1 -> do putWord8 1
                                 put x1
                Unchecked -> do putWord8 2
                Productive -> do putWord8 3
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Total x1)
                   1 -> do x1 <- get
                           return (Partial x1)
                   2 -> return Unchecked
                   3 -> return Productive
                   _ -> error "Corrupted binary data for Totality"

instance Binary IBCFile where
        put x@(IBCFile x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24)
         = {-# SCC "putIBCFile" #-} 
            do put x1
               put x2
               put x3
               put x4
               put x5
               put x6
               put x7
               put x8
               put x9
               put x10
               put x11
               put x12
               put x13
               put x14
               put x15
               put x16
               put x17
               put x18
               put x19
               put x20
               put x21
               put x22
               put x23
               put x24
        get
          = do x1 <- get
               if x1 == ibcVersion then 
                 do x2 <- get
                    x3 <- get
                    x4 <- get
                    x5 <- get
                    x6 <- get
                    x7 <- get
                    x8 <- get
                    x9 <- get
                    x10 <- get
                    x11 <- get
                    x12 <- get
                    x13 <- get
                    x14 <- get
                    x15 <- get
                    x16 <- get
                    x17 <- get
                    x18 <- get
                    x19 <- get
                    x20 <- get
                    x21 <- get
                    x22 <- get
                    x23 <- get
                    x24 <- get
                    return (IBCFile x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24)
                  else return (initIBC { ver = x1 })
 
instance Binary FnOpt where
        put x
          = case x of
                Inlinable -> putWord8 0
                TotalFn -> putWord8 1
                TCGen -> putWord8 2
                AssertTotal -> putWord8 3
                Specialise x -> do putWord8 4
                                   put x
                Coinductive -> putWord8 5
                PartialFn -> putWord8 6
                Implicit -> putWord8 7
        get
          = do i <- getWord8
               case i of
                   0 -> return Inlinable
                   1 -> return TotalFn
                   2 -> return TCGen
                   3 -> return AssertTotal
                   4 -> do x <- get
                           return (Specialise x)
                   5 -> return Coinductive
                   6 -> return PartialFn
                   7 -> return Implicit
                   _ -> error "Corrupted binary data for FnOpt"

instance Binary Fixity where
        put x
          = case x of
                Infixl x1 -> do putWord8 0
                                put x1
                Infixr x1 -> do putWord8 1
                                put x1
                InfixN x1 -> do putWord8 2
                                put x1
                PrefixN x1 -> do putWord8 3
                                 put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Infixl x1)
                   1 -> do x1 <- get
                           return (Infixr x1)
                   2 -> do x1 <- get
                           return (InfixN x1)
                   3 -> do x1 <- get
                           return (PrefixN x1)
                   _ -> error "Corrupted binary data for Fixity"

 
instance Binary FixDecl where
        put (Fix x1 x2)
          = do put x1
               put x2
        get
          = do x1 <- get
               x2 <- get
               return (Fix x1 x2)

 
instance Binary Static where
        put x
          = case x of
                Static -> putWord8 0
                Dynamic -> putWord8 1
        get
          = do i <- getWord8
               case i of
                   0 -> return Static
                   1 -> return Dynamic
                   _ -> error "Corrupted binary data for Static"

 
instance Binary Plicity where
        put x
          = case x of
                Imp x1 x2 x3 -> 
                             do putWord8 0
                                put x1
                                put x2
                                put x3
                Exp x1 x2 x3 -> 
                             do putWord8 1
                                put x1
                                put x2
                                put x3
                Constraint x1 x2 x3 -> 
                                    do putWord8 2
                                       put x1
                                       put x2
                                       put x3
                TacImp x1 x2 x3 x4 -> 
                                   do putWord8 3
                                      put x1
                                      put x2
                                      put x3
                                      put x4
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Imp x1 x2 x3)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Exp x1 x2 x3)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Constraint x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (TacImp x1 x2 x3 x4)
                   _ -> error "Corrupted binary data for Plicity"

 
instance (Binary t) => Binary (PDecl' t) where
        put x
          = case x of
                PFix x1 x2 x3 -> do putWord8 0
                                    put x1
                                    put x2
                                    put x3
                PTy x1 x2 x3 x4 x5 x6
                                   -> do putWord8 1
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                                         put x5
                                         put x6
                PClauses x1 x2 x3 x4 -> do putWord8 2
                                           put x1
                                           put x2
                                           put x3
                                           put x4
                PData x1 x2 x3 x4 x5 -> 
                                     do putWord8 3
                                        put x1
                                        put x2
                                        put x3
                                        put x4
                                        put x5
                PParams x1 x2 x3 -> do putWord8 4
                                       put x1
                                       put x2
                                       put x3
                PNamespace x1 x2 -> do putWord8 5
                                       put x1
                                       put x2
                PRecord x1 x2 x3 x4 x5 x6 x7 x8 -> 
                                             do putWord8 6
                                                put x1
                                                put x2
                                                put x3
                                                put x4
                                                put x5
                                                put x6
                                                put x7
                                                put x8
                PClass x1 x2 x3 x4 x5 x6 x7
                                         -> do putWord8 7
                                               put x1
                                               put x2
                                               put x3
                                               put x4
                                               put x5
                                               put x6
                                               put x7
                PInstance x1 x2 x3 x4 x5 x6 x7 x8 -> do putWord8 8
                                                        put x1
                                                        put x2
                                                        put x3
                                                        put x4
                                                        put x5
                                                        put x6
                                                        put x7
                                                        put x8
                PDSL x1 x2 -> do putWord8 9
                                 put x1
                                 put x2
                PCAF x1 x2 x3 -> do putWord8 10
                                    put x1
                                    put x2
                                    put x3
                PMutual x1 x2  -> do putWord8 11
                                     put x1
                                     put x2
                PPostulate x1 x2 x3 x4 x5 x6
                                   -> do putWord8 12
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                                         put x5
                                         put x6
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PFix x1 x2 x3)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           return (PTy x1 x2 x3 x4 x5 x6)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PClauses x1 x2 x3 x4)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           return (PData x1 x2 x3 x4 x5)
                   4 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PParams x1 x2 x3)
                   5 -> do x1 <- get
                           x2 <- get
                           return (PNamespace x1 x2)
                   6 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           x7 <- get
                           x8 <- get
                           return (PRecord x1 x2 x3 x4 x5 x6 x7 x8)
                   7 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           x7 <- get
                           return (PClass x1 x2 x3 x4 x5 x6 x7)
                   8 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           x7 <- get
                           x8 <- get
                           return (PInstance x1 x2 x3 x4 x5 x6 x7 x8)
                   9 -> do x1 <- get
                           x2 <- get
                           return (PDSL x1 x2)
                   10 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PCAF x1 x2 x3)
                   11 -> do x1 <- get
                            x2 <- get
                            return (PMutual x1 x2)
                   12 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            x5 <- get
                            x6 <- get
                            return (PPostulate x1 x2 x3 x4 x5 x6)
                   _ -> error "Corrupted binary data for PDecl'"

instance Binary Using where
        put (UImplicit x1 x2) = do putWord8 0; put x1; put x2
        put (UConstraint x1 x2) = do putWord8 1; put x1; put x2

        get = do i <- getWord8
                 case i of
                    0 -> do x1 <- get; x2 <- get; return (UImplicit x1 x2)
                    1 -> do x1 <- get; x2 <- get; return (UConstraint x1 x2)

instance Binary SyntaxInfo where
        put (Syn x1 x2 x3 x4 x5 x6 x7 x8)
          = do put x1
               put x2
               put x3
               put x4
               put x5
               put x6
               put x7
               put x8
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               x4 <- get
               x5 <- get
               x6 <- get
               x7 <- get
               x8 <- get
               return (Syn x1 x2 x3 x4 x5 x6 x7 x8)

instance (Binary t) => Binary (PClause' t) where
        put x
          = case x of
                PClause x1 x2 x3 x4 x5 x6 -> do putWord8 0
                                                put x1
                                                put x2
                                                put x3
                                                put x4
                                                put x5
                                                put x6
                PWith x1 x2 x3 x4 x5 x6 -> do putWord8 1
                                              put x1
                                              put x2
                                              put x3
                                              put x4
                                              put x5
                                              put x6
                PClauseR x1 x2 x3 x4 -> do putWord8 2
                                           put x1
                                           put x2
                                           put x3
                                           put x4
                PWithR x1 x2 x3 x4 -> do putWord8 3
                                         put x1
                                         put x2
                                         put x3
                                         put x4
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           return (PClause x1 x2 x3 x4 x5 x6)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           return (PWith x1 x2 x3 x4 x5 x6)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PClauseR x1 x2 x3 x4)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PWithR x1 x2 x3 x4)
                   _ -> error "Corrupted binary data for PClause'"

instance (Binary t) => Binary (PData' t) where
        put x
          = case x of
                PDatadecl x1 x2 x3 -> do putWord8 0
                                         put x1
                                         put x2
                                         put x3
                PLaterdecl x1 x2 -> do putWord8 1
                                       put x1
                                       put x2
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PDatadecl x1 x2 x3)
                   1 -> do x1 <- get
                           x2 <- get
                           return (PLaterdecl x1 x2)
                   _ -> error "Corrupted binary data for PData'"

instance Binary PTerm where
        put x
          = case x of
                PQuote x1 -> do putWord8 0
                                put x1
                PRef x1 x2 -> do putWord8 1
                                 put x1
                                 put x2
                PLam x1 x2 x3 -> do putWord8 2
                                    put x1
                                    put x2
                                    put x3
                PPi x1 x2 x3 x4 -> do putWord8 3
                                      put x1
                                      put x2
                                      put x3
                                      put x4
                PLet x1 x2 x3 x4 -> do putWord8 4
                                       put x1
                                       put x2
                                       put x3
                                       put x4
                PTyped x1 x2 -> do putWord8 5
                                   put x1
                                   put x2
                PApp x1 x2 x3 -> do putWord8 6
                                    put x1
                                    put x2
                                    put x3
                PCase x1 x2 x3 -> do putWord8 7
                                     put x1
                                     put x2
                                     put x3
                PTrue x1 -> do putWord8 8
                               put x1
                PFalse x1 -> do putWord8 9
                                put x1
                PRefl x1 x2 -> do putWord8 10
                                  put x1
                                  put x2
                PResolveTC x1 -> do putWord8 11
                                    put x1
                PEq x1 x2 x3 -> do putWord8 12
                                   put x1
                                   put x2
                                   put x3
                PPair x1 x2 x3 -> do putWord8 13
                                     put x1
                                     put x2
                                     put x3
                PDPair x1 x2 x3 x4 -> do putWord8 14
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                PAlternative x1 x2 -> do putWord8 15
                                         put x1
                                         put x2
                PHidden x1 -> do putWord8 16
                                 put x1
                PType -> putWord8 17
                PConstant x1 -> do putWord8 18
                                   put x1
                Placeholder -> putWord8 19
                PDoBlock x1 -> do putWord8 20
                                  put x1
                PIdiom x1 x2 -> do putWord8 21
                                   put x1
                                   put x2
                PReturn x1 -> do putWord8 22
                                 put x1
                PMetavar x1 -> do putWord8 23
                                  put x1
                PProof x1 -> do putWord8 24
                                put x1
                PTactics x1 -> do putWord8 25
                                  put x1
                PImpossible -> putWord8 27
                PPatvar x1 x2 -> do putWord8 28
                                    put x1
                                    put x2
                PInferRef x1 x2 -> do putWord8 29
                                      put x1
                                      put x2
                PRewrite x1 x2 x3 -> do putWord8 30
                                        put x1
                                        put x2
                                        put x3
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (PQuote x1)
                   1 -> do x1 <- get
                           x2 <- get
                           return (PRef x1 x2)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PLam x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PPi x1 x2 x3 x4)
                   4 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PLet x1 x2 x3 x4)
                   5 -> do x1 <- get
                           x2 <- get
                           return (PTyped x1 x2)
                   6 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PApp x1 x2 x3)
                   7 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PCase x1 x2 x3)
                   8 -> do x1 <- get
                           return (PTrue x1)
                   9 -> do x1 <- get
                           return (PFalse x1)
                   10 -> do x1 <- get
                            x2 <- get
                            return (PRefl x1 x2)
                   11 -> do x1 <- get
                            return (PResolveTC x1)
                   12 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PEq x1 x2 x3)
                   13 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PPair x1 x2 x3)
                   14 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            return (PDPair x1 x2 x3 x4)
                   15 -> do x1 <- get
                            x2 <- get
                            return (PAlternative x1 x2)
                   16 -> do x1 <- get
                            return (PHidden x1)
                   17 -> return PType
                   18 -> do x1 <- get
                            return (PConstant x1)
                   19 -> return Placeholder
                   20 -> do x1 <- get
                            return (PDoBlock x1)
                   21 -> do x1 <- get
                            x2 <- get
                            return (PIdiom x1 x2)
                   22 -> do x1 <- get
                            return (PReturn x1)
                   23 -> do x1 <- get
                            return (PMetavar x1)
                   24 -> do x1 <- get
                            return (PProof x1)
                   25 -> do x1 <- get
                            return (PTactics x1)
                   27 -> return PImpossible
                   28 -> do x1 <- get
                            x2 <- get
                            return (PPatvar x1 x2)
                   29 -> do x1 <- get
                            x2 <- get
                            return (PInferRef x1 x2)
                   30 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PRewrite x1 x2 x3)
                   _ -> error "Corrupted binary data for PTerm"
 
instance (Binary t) => Binary (PTactic' t) where
        put x
          = case x of
                Intro x1 -> do putWord8 0
                               put x1
                Focus x1 -> do putWord8 1
                               put x1
                Refine x1 x2 -> do putWord8 2
                                   put x1
                                   put x2
                Rewrite x1 -> do putWord8 3
                                 put x1
                LetTac x1 x2 -> do putWord8 4
                                   put x1
                                   put x2
                Exact x1 -> do putWord8 5
                               put x1
                Compute -> putWord8 6
                Trivial -> putWord8 7
                Solve -> putWord8 8
                Attack -> putWord8 9
                ProofState -> putWord8 10
                ProofTerm -> putWord8 11
                Undo -> putWord8 12
                Try x1 x2 -> do putWord8 13
                                put x1
                                put x2
                TSeq x1 x2 -> do putWord8 14
                                 put x1
                                 put x2
                Qed -> putWord8 15
                ApplyTactic x1 -> do putWord8 16
                                     put x1
                Reflect x1 -> do putWord8 17
                                 put x1
                Fill x1 -> do putWord8 18
                              put x1                
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Intro x1)
                   1 -> do x1 <- get
                           return (Focus x1)
                   2 -> do x1 <- get
                           x2 <- get
                           return (Refine x1 x2)
                   3 -> do x1 <- get
                           return (Rewrite x1)
                   4 -> do x1 <- get
                           x2 <- get
                           return (LetTac x1 x2)
                   5 -> do x1 <- get
                           return (Exact x1)
                   6 -> return Compute
                   7 -> return Trivial
                   8 -> return Solve
                   9 -> return Attack
                   10 -> return ProofState
                   11 -> return ProofTerm
                   12 -> return Undo
                   13 -> do x1 <- get
                            x2 <- get
                            return (Try x1 x2)
                   14 -> do x1 <- get
                            x2 <- get
                            return (TSeq x1 x2)
                   15 -> return Qed
                   16 -> do x1 <- get
                            return (ApplyTactic x1)
                   17 -> do x1 <- get
                            return (Reflect x1)
                   18 -> do x1 <- get
                            return (Fill x1)
                   _ -> error "Corrupted binary data for PTactic'"


instance (Binary t) => Binary (PDo' t) where
        put x
          = case x of
                DoExp x1 x2 -> do putWord8 0
                                  put x1
                                  put x2
                DoBind x1 x2 x3 -> do putWord8 1
                                      put x1
                                      put x2
                                      put x3
                DoBindP x1 x2 x3 -> do putWord8 2
                                       put x1
                                       put x2
                                       put x3
                DoLet x1 x2 x3 x4 -> do putWord8 3
                                        put x1
                                        put x2
                                        put x3
                                        put x4
                DoLetP x1 x2 x3 -> do putWord8 4
                                      put x1
                                      put x2
                                      put x3
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           return (DoExp x1 x2)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (DoBind x1 x2 x3)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (DoBindP x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (DoLet x1 x2 x3 x4)
                   4 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (DoLetP x1 x2 x3)
                   _ -> error "Corrupted binary data for PDo'"


instance (Binary t) => Binary (PArg' t) where
        put x
          = case x of
                PImp x1 x2 x3 x4 x5 -> 
                                    do putWord8 0
                                       put x1
                                       put x2
                                       put x3
                                       put x4
                                       put x5
                PExp x1 x2 x3 x4 -> 
                                 do putWord8 1
                                    put x1
                                    put x2
                                    put x3
                                    put x4
                PConstraint x1 x2 x3 x4 -> 
                                        do putWord8 2
                                           put x1
                                           put x2
                                           put x3
                                           put x4
                PTacImplicit x1 x2 x3 x4 x5 x6 -> 
                                               do putWord8 3
                                                  put x1
                                                  put x2
                                                  put x3
                                                  put x4
                                                  put x5
                                                  put x6
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           return (PImp x1 x2 x3 x4 x5)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PExp x1 x2 x3 x4)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PConstraint x1 x2 x3 x4)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           return (PTacImplicit x1 x2 x3 x4 x5 x6)
                   _ -> error "Corrupted binary data for PArg'"

 
instance Binary ClassInfo where
        put (CI x1 x2 x3 x4 _)
          = do put x1
               put x2
               put x3
               put x4
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               x4 <- get
               return (CI x1 x2 x3 x4 [])

instance Binary OptInfo where
        put (Optimise x1 x2 x3)
          = do put x1
               put x2
               put x3
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               return (Optimise x1 x2 x3)

instance Binary TypeInfo where
        put (TI x1 x2 x3) = do put x1
                               put x2
                               put x3
        get = do x1 <- get
                 x2 <- get
                 x3 <- get
                 return (TI x1 x2 x3)

instance Binary SynContext where
        put x
          = case x of
                PatternSyntax -> putWord8 0
                TermSyntax -> putWord8 1
                AnySyntax -> putWord8 2
        get
          = do i <- getWord8
               case i of
                   0 -> return PatternSyntax
                   1 -> return TermSyntax
                   2 -> return AnySyntax
                   _ -> error "Corrupted binary data for SynContext"

 
instance Binary Syntax where
        put (Rule x1 x2 x3)
          = do put x1
               put x2
               put x3
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               return (Rule x1 x2 x3)

instance (Binary t) => Binary (DSL' t) where
        put (DSL x1 x2 x3 x4 x5 x6 x7 x8 x9)
          = do put x1
               put x2
               put x3
               put x4
               put x5
               put x6
               put x7
               put x8
               put x9
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               x4 <- get
               x5 <- get
               x6 <- get
               x7 <- get
               x8 <- get
               x9 <- get
               return (DSL x1 x2 x3 x4 x5 x6 x7 x8 x9)
 
instance Binary SSymbol where
        put x
          = case x of
                Keyword x1 -> do putWord8 0
                                 put x1
                Symbol x1 -> do putWord8 1
                                put x1
                Expr x1 -> do putWord8 2
                              put x1
                SimpleExpr x1 -> do putWord8 3
                                    put x1
                Binding x1 -> do putWord8 4
                                 put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Keyword x1)
                   1 -> do x1 <- get
                           return (Symbol x1)
                   2 -> do x1 <- get
                           return (Expr x1)
                   3 -> do x1 <- get
                           return (SimpleExpr x1)
                   4 -> do x1 <- get
                           return (Binding x1)
                   _ -> error "Corrupted binary data for SSymbol"

instance Binary Target where
        put x
          = case x of
                ViaC -> putWord8 0
                ViaJava -> putWord8 1
                ViaNode -> putWord8 2
                ViaJavaScript -> putWord8 3
                Bytecode -> putWord8 4
        get
          = do i <- getWord8
               case i of
                  0 -> return ViaC
                  1 -> return ViaJava
                  2 -> return ViaNode
                  3 -> return ViaJavaScript
                  4 -> return Bytecode
                  _ -> error  "Corrupted binary data for Target"


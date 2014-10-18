{-# LANGUAGE TypeSynonymInstances #-}

module Idris.IBC where

import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Core.Binary
import Idris.Core.CaseTree
import Idris.AbsSyntax
import Idris.Imports
import Idris.Error
import Idris.Delaborate
import qualified Idris.Docstrings as D
import Idris.Docstrings (Docstring)
import Idris.Output

import qualified Cheapskate.Types as CT

import Data.Binary
import Data.Vector.Binary
import Data.List
import Data.ByteString.Lazy as B hiding (length, elem, map)
import qualified Data.Text as T
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State.Strict hiding (get, put)
import qualified Control.Monad.State.Strict as ST
import System.FilePath
import System.Directory
import Codec.Compression.Zlib (compress)
import Util.Zlib (decompressEither)

ibcVersion :: Word8
ibcVersion = 83

data IBCFile = IBCFile { ver :: Word8,
                         sourcefile :: FilePath,
                         symbols :: [Name],
                         ibc_imports :: [FilePath],
                         ibc_importdirs :: [FilePath],
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
                         ibc_objs :: [(Codegen, FilePath)],
                         ibc_libs :: [(Codegen, String)],
                         ibc_cgflags :: [(Codegen, String)],
                         ibc_dynamic_libs :: [String],
                         ibc_hdrs :: [(Codegen, String)],
                         ibc_access :: [(Name, Accessibility)],
                         ibc_total :: [(Name, Totality)],
                         ibc_totcheckfail :: [(FC, String)],
                         ibc_flags :: [(Name, [FnOpt])],
                         ibc_fninfo :: [(Name, FnInfo)],
                         ibc_cg :: [(Name, CGInfo)],
                         ibc_defs :: [(Name, Def)],
                         ibc_docstrings :: [(Name, (Docstring (Maybe Term), [(Name, Docstring (Maybe Term))]))],
                         ibc_transforms :: [(Name, (Term, Term))],
                         ibc_errRev :: [(Term, Term)],
                         ibc_coercions :: [Name],
                         ibc_lineapps :: [(FilePath, Int, PTerm)],
                         ibc_namehints :: [(Name, Name)],
                         ibc_metainformation :: [(Name, MetaInformation)],
                         ibc_errorhandlers :: [Name],
                         ibc_function_errorhandlers :: [(Name, Name, Name)], -- fn, arg, handler
                         ibc_metavars :: [(Name, (Maybe Name, Int, Bool))],
                         ibc_patdefs :: [(Name, ([([Name], Term, Term)], [PTerm]))],
                         ibc_postulates :: [Name],
                         ibc_parsedSpan :: Maybe FC
                       }
   deriving Show
{-!
deriving instance Binary IBCFile
!-}

initIBC :: IBCFile
initIBC = IBCFile ibcVersion "" [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] Nothing

loadIBC :: FilePath -> Idris ()
loadIBC fp = do imps <- getImported
                when (not (fp `elem` imps)) $
                  do iLOG $ "Loading ibc " ++ fp
                     ibcf <- runIO $ (bdecode fp :: IO IBCFile)
                     process ibcf fp
                     addImported fp

bencode :: Binary a => FilePath -> a -> IO ()
bencode f d = B.writeFile f (compress (encode d))

bdecode :: Binary b => FilePath -> IO b
bdecode f = do d' <- B.readFile f
               either
                 (\(_, e) -> error $ "Invalid / corrupted zip format on " ++ show f ++ ": " ++ e)
                 (return . decode)
                 (decompressEither d')

writeIBC :: FilePath -> FilePath -> Idris ()
writeIBC src f
    = do iLOG $ "Writing ibc " ++ show f
         i <- getIState
--          case (Data.List.map fst (idris_metavars i)) \\ primDefs of
--                 (_:_) -> ifail "Can't write ibc when there are unsolved metavariables"
--                 [] -> return ()
         resetNameIdx
         ibcf <- mkIBC (ibc_write i) (initIBC { sourcefile = src })
         idrisCatch (do runIO $ createDirectoryIfMissing True (dropFileName f)
                        runIO $ bencode f ibcf
                        iLOG "Written")
            (\c -> do iLOG $ "Failed " ++ pshow i c)
         return ()

mkIBC :: [IBCWrite] -> IBCFile -> Idris IBCFile
mkIBC [] f = return f
mkIBC (i:is) f = do ist <- getIState
                    logLvl 5 $ show i ++ " " ++ show (Data.List.length is)
                    f' <- ibc ist i f
                    mkIBC is f'

ibc :: IState -> IBCWrite -> IBCFile -> Idris IBCFile
ibc i (IBCFix d) f = return f { ibc_fixes = d : ibc_fixes f }
ibc i (IBCImp n) f = case lookupCtxtExact n (idris_implicits i) of
                        Just v -> return f { ibc_implicits = (n,v): ibc_implicits f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCStatic n) f
                   = case lookupCtxtExact n (idris_statics i) of
                        Just v -> return f { ibc_statics = (n,v): ibc_statics f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCClass n) f
                   = case lookupCtxtExact n (idris_classes i) of
                        Just v -> return f { ibc_classes = (n,v): ibc_classes f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCInstance int n ins) f
                   = return f { ibc_instances = (int,n,ins): ibc_instances f     }
ibc i (IBCDSL n) f
                   = case lookupCtxtExact n (idris_dsls i) of
                        Just v -> return f { ibc_dsls = (n,v): ibc_dsls f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCData n) f
                   = case lookupCtxtExact n (idris_datatypes i) of
                        Just v -> return f { ibc_datatypes = (n,v): ibc_datatypes f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCOpt n) f = case lookupCtxtExact n (idris_optimisation i) of
                        Just v -> return f { ibc_optimise = (n,v): ibc_optimise f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCSyntax n) f = return f { ibc_syntax = n : ibc_syntax f }
ibc i (IBCKeyword n) f = return f { ibc_keywords = n : ibc_keywords f }
ibc i (IBCImport n) f = return f { ibc_imports = n : ibc_imports f }
ibc i (IBCImportDir n) f = return f { ibc_importdirs = n : ibc_importdirs f }
ibc i (IBCObj tgt n) f = return f { ibc_objs = (tgt, n) : ibc_objs f }
ibc i (IBCLib tgt n) f = return f { ibc_libs = (tgt, n) : ibc_libs f }
ibc i (IBCCGFlag tgt n) f = return f { ibc_cgflags = (tgt, n) : ibc_cgflags f }
ibc i (IBCDyLib n) f = return f {ibc_dynamic_libs = n : ibc_dynamic_libs f }
ibc i (IBCHeader tgt n) f = return f { ibc_hdrs = (tgt, n) : ibc_hdrs f }
ibc i (IBCDef n) f 
   = do f' <- case lookupDefExact n (tt_ctxt i) of
                   Just v -> do (v', (f', _)) <- runStateT (updateDef v) (f, length (symbols f))
                                return f' { ibc_defs = (n,v) : ibc_defs f'     }
                   _ -> ifail "IBC write failed"
        case lookupCtxtExact n (idris_patdefs i) of
                   Just v -> return f' { ibc_patdefs = (n,v) : ibc_patdefs f' }
                   _ -> return f' -- Not a pattern definition
  where 
    updateDef :: Def -> StateT (IBCFile, Int) Idris Def
    updateDef (CaseOp c t args o s cd)
        = do o' <- mapM updateOrig o
             cd' <- updateCD cd
             return (CaseOp c t args o' s cd')
    updateDef t = return t

    updateOrig (Left t) = do t' <- update t
                             return (Left t')
    updateOrig (Right (l,r)) = do l' <- update l
                                  r' <- update r
                                  return (Right (l', r'))

    updateCD (CaseDefs (ts, t) (cs, c) (is, i) (rs, r))
       = do c' <- updateSC c; r' <- updateSC r
            return (CaseDefs (ts, t) (cs, c') (is, i) (rs, r'))

    updateSC (Case up n alts) = do alts' <- mapM updateAlt alts
                                   return (Case up n alts')
    updateSC (ProjCase t alts) = do t' <- update t
                                    alts' <- mapM updateAlt alts
                                    return (ProjCase t' alts')
    updateSC (STerm t) = do t' <- update t
                            return (STerm t')
    updateSC t = return t

    updateAlt (ConCase n i a sc) = do sc' <- updateSC sc
                                      return (ConCase n i a sc')
    updateAlt (FnCase n a sc) = do sc' <- updateSC sc
                                   return (FnCase n a sc')
    updateAlt (ConstCase i sc) = do sc' <- updateSC sc
                                    return (ConstCase i sc')
    updateAlt (SucCase n sc) = do sc' <- updateSC sc
                                  return (SucCase n sc')
    updateAlt (DefaultCase sc) = do sc' <- updateSC sc
                                    return (DefaultCase sc')

    update (P t n@(MN _ _) ty) = return (P t n ty)
    update (P t n@(UN _) ty) = return (P t n ty)
    update (P t n ty) = do (f, len) <- ST.get
                           (i, _) <- lift (addNameIdx n)
                           when (i >= len) $
                             ST.put (f { symbols = symbols f ++ [n] }, len+1)
                           return (P t (SymRef i) ty)
    update (App f a) = do f' <- update f; a' <- update a
                          return (App f' a')
    update (Bind n b sc) = do b' <- fmapMB update b
                              sc' <- update sc
                              return (Bind n b' sc')
    update (Proj t i) = do t' <- update t
                           return (Proj t' i)
    update t = return t


ibc i (IBCDoc n) f = case lookupCtxtExact n (idris_docstrings i) of
                        Just v -> return f { ibc_docstrings = (n,v) : ibc_docstrings f }
                        _ -> ifail "IBC write failed"
ibc i (IBCCG n) f = case lookupCtxtExact n (idris_callgraph i) of
                        Just v -> return f { ibc_cg = (n,v) : ibc_cg f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCCoercion n) f = return f { ibc_coercions = n : ibc_coercions f }
ibc i (IBCAccess n a) f = return f { ibc_access = (n,a) : ibc_access f }
ibc i (IBCFlags n a) f = return f { ibc_flags = (n,a) : ibc_flags f }
ibc i (IBCFnInfo n a) f = return f { ibc_fninfo = (n,a) : ibc_fninfo f }
ibc i (IBCTotal n a) f = return f { ibc_total = (n,a) : ibc_total f }
ibc i (IBCTrans n t) f = return f { ibc_transforms = (n, t) : ibc_transforms f }
ibc i (IBCErrRev t) f = return f { ibc_errRev = t : ibc_errRev f }
ibc i (IBCLineApp fp l t) f
     = return f { ibc_lineapps = (fp,l,t) : ibc_lineapps f }
ibc i (IBCNameHint (n, ty)) f
     = return f { ibc_namehints = (n, ty) : ibc_namehints f }
ibc i (IBCMetaInformation n m) f = return f { ibc_metainformation = (n,m) : ibc_metainformation f }
ibc i (IBCErrorHandler n) f = return f { ibc_errorhandlers = n : ibc_errorhandlers f }
ibc i (IBCFunctionErrorHandler fn a n) f =
  return f { ibc_function_errorhandlers = (fn, a, n) : ibc_function_errorhandlers f }
ibc i (IBCMetavar n) f =
     case lookup n (idris_metavars i) of
          Nothing -> return f
          Just t -> return f { ibc_metavars = (n, t) : ibc_metavars f }
ibc i (IBCPostulate n) f = return f { ibc_postulates = n : ibc_postulates f }
ibc i (IBCTotCheckErr fc err) f = return f { ibc_totcheckfail = (fc, err) : ibc_totcheckfail f }
ibc i (IBCParsedRegion fc) f = return f { ibc_parsedSpan = Just fc }

process :: IBCFile -> FilePath -> Idris ()
process i fn
   | ver i /= ibcVersion = do iLOG "ibc out of date"
                              ifail "Incorrect ibc version --- please rebuild"
   | otherwise =
            do srcok <- runIO $ doesFileExist (sourcefile i)
               when srcok $ timestampOlder (sourcefile i) fn
               v <- verbose
               quiet <- getQuiet
--                when (v && srcok && not quiet) $ iputStrLn $ "Skipping " ++ sourcefile i
               pImportDirs (ibc_importdirs i)
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
               pCGFlags (ibc_cgflags i)
               pDyLibs (ibc_dynamic_libs i)
               pHdrs (ibc_hdrs i)
               pDefs (symbols i) (ibc_defs i)
               pPatdefs (ibc_patdefs i)
               pAccess (ibc_access i)
               pFlags (ibc_flags i)
               pFnInfo (ibc_fninfo i)
               pTotal (ibc_total i)
               pTotCheckErr (ibc_totcheckfail i)
               pCG (ibc_cg i)
               pDocs (ibc_docstrings i)
               pCoercions (ibc_coercions i)
               pTrans (ibc_transforms i)
               pErrRev (ibc_errRev i)
               pLineApps (ibc_lineapps i)
               pNameHints (ibc_namehints i)
               pMetaInformation (ibc_metainformation i)
               pErrorHandlers (ibc_errorhandlers i)
               pFunctionErrorHandlers (ibc_function_errorhandlers i)
               pMetavars (ibc_metavars i)
               pPostulates (ibc_postulates i)
               pParsedSpan (ibc_parsedSpan i)

timestampOlder :: FilePath -> FilePath -> Idris ()
timestampOlder src ibc = do srct <- runIO $ getModificationTime src
                            ibct <- runIO $ getModificationTime ibc
                            if (srct > ibct)
                               then ifail "Needs reloading"
                               else return ()

pPostulates :: [Name] -> Idris ()
pPostulates ns = do
    i <- getIState
    putIState i{ idris_postulates = idris_postulates i `S.union` S.fromList ns }

pParsedSpan :: Maybe FC -> Idris ()
pParsedSpan fc = do ist <- getIState
                    putIState ist { idris_parsedSpan = fc }

pImportDirs :: [FilePath] -> Idris ()
pImportDirs fs = mapM_ addImportDir fs

pImports :: [FilePath] -> Idris ()
pImports fs
  = do mapM_ (\f -> do i <- getIState
                       ibcsd <- valIBCSubDir i
                       ids <- allImportDirs
                       fp <- findImport ids ibcsd f
                       if (f `elem` imported i)
                        then iLOG $ "Already read " ++ f
                        else do putIState (i { imported = f : imported i })
                                case fp of
                                    LIDR fn -> do iLOG $ "Failed at " ++ fn
                                                  ifail "Must be an ibc"
                                    IDR fn -> do iLOG $ "Failed at " ++ fn
                                                 ifail "Must be an ibc"
                                    IBC fn src -> loadIBC fn)
             fs

pImps :: [(Name, [PArg])] -> Idris ()
pImps imps = mapM_ (\ (n, imp) ->
                        do i <- getIState
                           case lookupDefAccExact n False (tt_ctxt i) of
                              Just (n, Hidden) -> return ()
                              _ -> putIState (i { idris_implicits
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
                           -- Don't lose instances from previous IBCs, which
                           -- could have loaded in any order
                           let is = case lookupCtxtExact n (idris_classes i) of
                                      Just (CI _ _ _ _ _ ins) -> ins
                                      _ -> []
                           let c' = c { class_instances =
                                          class_instances c ++ is }
                           putIState (i { idris_classes
                                           = addDef n c' (idris_classes i) }))
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

pObjs :: [(Codegen, FilePath)] -> Idris ()
pObjs os = mapM_ (\ (cg, obj) -> do dirs <- allImportDirs
                                    o <- runIO $ findInPath dirs obj
                                    addObjectFile cg o) os

pLibs :: [(Codegen, String)] -> Idris ()
pLibs ls = mapM_ (uncurry addLib) ls

pCGFlags :: [(Codegen, String)] -> Idris ()
pCGFlags ls = mapM_ (uncurry addFlag) ls

pDyLibs :: [String] -> Idris ()
pDyLibs ls = do res <- mapM (addDyLib . return) ls
                mapM_ checkLoad res
                return ()
    where checkLoad (Left _) = return ()
          checkLoad (Right err) = ifail err

pHdrs :: [(Codegen, String)] -> Idris ()
pHdrs hs = mapM_ (uncurry addHdr) hs

pPatdefs :: [(Name, ([([Name], Term, Term)], [PTerm]))] -> Idris ()
pPatdefs ds 
   = mapM_ (\ (n, d) -> 
                do i <- getIState
                   putIState (i { idris_patdefs = addDef n d (idris_patdefs i) }))
           ds

pDefs :: [Name] -> [(Name, Def)] -> Idris ()
pDefs syms ds 
   = mapM_ (\ (n, d) ->
               do let d' = updateDef d
                  case d' of
                       TyDecl _ _ -> return () 
                       _ -> do iLOG $ "SOLVING " ++ show n
                               solveDeferred n 
                  i <- getIState
--                   logLvl 1 $ "Added " ++ show (n, d')
                  putIState (i { tt_ctxt = addCtxtDef n d' (tt_ctxt i) })) ds
  where
    updateDef (CaseOp c t args o s cd)
      = CaseOp c t args (map updateOrig o) s (updateCD cd)
    updateDef t = t

    updateOrig (Left t) = Left (update t)
    updateOrig (Right (l, r)) = Right (update l, update r)

    updateCD (CaseDefs (ts, t) (cs, c) (is, i) (rs, r))
        = CaseDefs (ts, fmap update t)
                   (cs, fmap update c)
                   (is, fmap update i)
                   (rs, fmap update r)

    update (P t (SymRef i) ty) = P t (syms!!i) ty
    update (App f a) = App (update f) (update a)
    update (Bind n b sc) = Bind n (fmap update b) (update sc)
    update (Proj t i) = Proj (update t) i
    update t = t

pDocs :: [(Name, (Docstring (Maybe Term), [(Name, Docstring (Maybe Term))]))] -> Idris ()
pDocs ds = mapM_ (\ (n, a) -> addDocStr n (fst a) (snd a)) ds

pAccess :: [(Name, Accessibility)] -> Idris ()
pAccess ds = mapM_ (\ (n, a) ->
                      do i <- getIState
                         putIState (i { tt_ctxt = setAccess n a (tt_ctxt i) }))
                   ds

pFlags :: [(Name, [FnOpt])] -> Idris ()
pFlags ds = mapM_ (\ (n, a) -> setFlags n a) ds

pFnInfo :: [(Name, FnInfo)] -> Idris ()
pFnInfo ds = mapM_ (\ (n, a) -> setFnInfo n a) ds

pTotal :: [(Name, Totality)] -> Idris ()
pTotal ds = mapM_ (\ (n, a) ->
                      do i <- getIState
                         putIState (i { tt_ctxt = setTotal n a (tt_ctxt i) }))
                   ds

pTotCheckErr :: [(FC, String)] -> Idris ()
pTotCheckErr es = do ist <- getIState
                     putIState ist { idris_totcheckfail = idris_totcheckfail ist ++ es }

pCG :: [(Name, CGInfo)] -> Idris ()
pCG ds = mapM_ (\ (n, a) -> addToCG n a) ds

pCoercions :: [Name] -> Idris ()
pCoercions ns = mapM_ (\ n -> addCoercion n) ns

pTrans :: [(Name, (Term, Term))] -> Idris ()
pTrans ts = mapM_ (\ (n, t) -> addTrans n t) ts

pErrRev :: [(Term, Term)] -> Idris ()
pErrRev ts = mapM_ addErrRev ts

pLineApps :: [(FilePath, Int, PTerm)] -> Idris ()
pLineApps ls = mapM_ (\ (f, i, t) -> addInternalApp f i t) ls

pNameHints :: [(Name, Name)] -> Idris ()
pNameHints ns = mapM_ (\ (n, ty) -> addNameHint n ty) ns

pMetaInformation :: [(Name, MetaInformation)] -> Idris ()
pMetaInformation ds = mapM_ (\ (n, m) ->
                            do i <- getIState
                               putIState (i { tt_ctxt = setMetaInformation n m (tt_ctxt i) }))
                         ds

pErrorHandlers :: [Name] -> Idris ()
pErrorHandlers ns = do i <- getIState
                       putIState $ i { idris_errorhandlers = idris_errorhandlers i ++ ns }

pFunctionErrorHandlers :: [(Name, Name, Name)] -> Idris ()
pFunctionErrorHandlers [] = return ()
pFunctionErrorHandlers ((fn, arg, handler):ns) = do addFunctionErrorHandlers fn arg [handler]
                                                    pFunctionErrorHandlers ns

pMetavars :: [(Name, (Maybe Name, Int, Bool))] -> Idris ()
pMetavars ns = do i <- getIState
                  putIState $ i { idris_metavars = Data.List.reverse ns 
                                                     ++ idris_metavars i }

----- For Cheapskate and docstrings

instance Binary a => Binary (D.Docstring a) where
  put (D.DocString opts lines) = do put opts ; put lines
  get = do opts <- get
           lines <- get
           return (D.DocString opts lines)

instance Binary CT.Options where
  put (CT.Options x1 x2 x3 x4) = do put x1 ; put x2 ; put x3 ; put x4
  get = do x1 <- get
           x2 <- get
           x3 <- get
           x4 <- get
           return (CT.Options x1 x2 x3 x4)

instance Binary a => Binary (D.Block a) where
  put (D.Para lines) = do putWord8 0 ; put lines
  put (D.Header i lines) = do putWord8 1 ; put i ; put lines
  put (D.Blockquote bs) = do putWord8 2 ; put bs
  put (D.List b t xs) = do putWord8 3 ; put b ; put t ; put xs
  put (D.CodeBlock attr txt src) = do putWord8 4 ; put attr ; put txt ; put src
  put (D.HtmlBlock txt) = do putWord8 5 ; put txt
  put D.HRule = putWord8 6
  get = do i <- getWord8
           case i of
             0 -> fmap D.Para get
             1 -> liftM2 D.Header get get
             2 -> fmap D.Blockquote get
             3 -> liftM3 D.List get get get
             4 -> liftM3 D.CodeBlock get get get
             5 -> liftM D.HtmlBlock get
             6 -> return D.HRule

instance Binary a => Binary (D.Inline a) where
  put (D.Str txt) = do putWord8 0 ; put txt
  put D.Space = putWord8 1
  put D.SoftBreak = putWord8 2
  put D.LineBreak = putWord8 3
  put (D.Emph xs) = putWord8 4 >> put xs
  put (D.Strong xs) = putWord8 5 >> put xs
  put (D.Code xs tm) = putWord8 6 >> put xs >> put tm
  put (D.Link a b c) = putWord8 7 >> put a >> put b >> put c
  put (D.Image a b c) = putWord8 8 >> put a >> put b >> put c
  put (D.Entity a) = putWord8 9 >> put a
  put (D.RawHtml x) = putWord8 10 >> put x
  get = do i <- getWord8
           case i of
             0 -> liftM D.Str get
             1 -> return D.Space
             2 -> return D.SoftBreak
             3 -> return D.LineBreak
             4 -> liftM D.Emph get
             5 -> liftM D.Strong get
             6 -> liftM2 D.Code get get
             7 -> liftM3 D.Link get get get
             8 -> liftM3 D.Image get get get
             9 -> liftM D.Entity get
             10 -> liftM D.RawHtml get

instance Binary CT.ListType where
  put (CT.Bullet c) = putWord8 0 >> put c
  put (CT.Numbered nw i) = putWord8 1 >> put nw >> put i
  get = do i <- getWord8
           case i of
             0 -> liftM CT.Bullet get
             1 -> liftM2 CT.Numbered get get

instance Binary CT.CodeAttr where
  put (CT.CodeAttr a b) = put a >> put b
  get = liftM2 CT.CodeAttr get get

instance Binary CT.NumWrapper where
  put (CT.PeriodFollowing) = putWord8 0
  put (CT.ParenFollowing) = putWord8 1
  get = do i <- getWord8
           case i of
             0 -> return CT.PeriodFollowing
             1 -> return CT.ParenFollowing

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
--                put x3 -- Already used SCG info for totality check
               put x4
               put x5
        get
          = do x1 <- get
               x2 <- get
               x4 <- get
               x5 <- get
               return (CGInfo x1 x2 [] x4 x5)

instance Binary CaseType where
        put x = case x of
                     Updatable -> putWord8 0
                     Shared -> putWord8 1
        get = do i <- getWord8
                 case i of
                     0 -> return Updatable
                     1 -> return Shared
                     _ -> error "Corrupted binary data for CaseType"

instance Binary SC where
        put x
          = case x of
                Case x1 x2 x3 -> do putWord8 0
                                    put x1
                                    put x2
                                    put x3
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
                           x3 <- get
                           return (Case x1 x2 x3)
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
                FnCase x1 x2 x3 -> do putWord8 3
                                      put x1
                                      put x2
                                      put x3
                SucCase x1 x2 -> do putWord8 4
                                    put x1
                                    put x2
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
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (FnCase x1 x2 x3)
                   4 -> do x1 <- get
                           x2 <- get
                           return (SucCase x1 x2)
                   _ -> error "Corrupted binary data for CaseAlt"

instance Binary CaseDefs where
        put (CaseDefs x1 x2 x3 x4)
          = do -- don't need totality checked or inlined versions
               put x2
               put x4
        get
          = do x2 <- get
               x4 <- get
               return (CaseDefs x2 x2 x2 x4)

instance Binary CaseInfo where
        put x@(CaseInfo x1 x2) = do put x1
                                    put x2
        get = do x1 <- get
                 x2 <- get
                 return (CaseInfo x1 x2)

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
                CaseOp x1 x2 x2a x3 x3a x4 -> do putWord8 3
                                                 put x1
                                                 put x2
                                                 put x2a
                                                 put x3
                                                 -- no x3a
                                                 put x4
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           return (Function x1 x2)
                   1 -> do x1 <- get
                           x2 <- get
                           return (TyDecl x1 x2)
                   -- Operator isn't written, don't read
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           -- x3 <- get always []
                           x5 <- get
                           return (CaseOp x1 x2 x3 x4 [] x5)
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

safeToEnum :: (Enum a, Bounded a, Integral int) => String -> int -> a
safeToEnum label x' = result
  where
    x = fromIntegral x'
    result 
        |  x < fromEnum (minBound `asTypeOf` result)
        || x > fromEnum (maxBound `asTypeOf` result)
            = error $ label ++ ": corrupted binary representation in IBC"
        | otherwise = toEnum x

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

instance Binary MetaInformation where
  put x
    = case x of
      EmptyMI   -> do putWord8 0
      DataMI x1 -> do putWord8 1
                      put x1
  get = do i <- getWord8
           case i of
             0 -> return EmptyMI
             1 -> do x1 <- get
                     return (DataMI x1)

instance Binary IBCFile where
        put x@(IBCFile x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40)
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
               put x25
               put x26
               put x27
               put x28
               put x29
               put x30
               put x31
               put x32
               put x33
               put x34
               put x35
               put x36
               put x37
               put x38
               put x39
               put x40

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
                    x25 <- get
                    x26 <- get
                    x27 <- get
                    x28 <- get
                    x29 <- get
                    x30 <- get
                    x31 <- get
                    x32 <- get
                    x33 <- get
                    x34 <- get
                    x35 <- get
                    x36 <- get
                    x37 <- get
                    x38 <- get
                    x39 <- get
                    x40 <- get
                    return (IBCFile x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40)
                  else return (initIBC { ver = x1 })

instance Binary DataOpt where
  put x = case x of
    Codata -> putWord8 0
    DefaultEliminator -> putWord8 1
    DataErrRev -> putWord8 2
    DefaultCaseFun -> putWord8 3
  get = do i <- getWord8
           case i of
            0 -> return Codata
            1 -> return DefaultEliminator
            2 -> return DataErrRev
            3 -> return DefaultCaseFun

instance Binary FnOpt where
        put x
          = case x of
                Inlinable -> putWord8 0
                TotalFn -> putWord8 1
                Dictionary -> putWord8 2
                AssertTotal -> putWord8 3
                Specialise x -> do putWord8 4
                                   put x
                Coinductive -> putWord8 5
                PartialFn -> putWord8 6
                Implicit -> putWord8 7
                Reflection -> putWord8 8
                ErrorHandler -> putWord8 9
                ErrorReverse -> putWord8 10
                CoveringFn -> putWord8 11
                NoImplicit -> putWord8 12
                Constructor -> putWord8 13
        get
          = do i <- getWord8
               case i of
                   0 -> return Inlinable
                   1 -> return TotalFn
                   2 -> return Dictionary
                   3 -> return AssertTotal
                   4 -> do x <- get
                           return (Specialise x)
                   5 -> return Coinductive
                   6 -> return PartialFn
                   7 -> return Implicit
                   8 -> return Reflection
                   9 -> return ErrorHandler
                   10 -> return ErrorReverse
                   11 -> return CoveringFn
                   12 -> return NoImplicit
                   13 -> return Constructor
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


instance Binary ArgOpt where
        put x
          = case x of
                HideDisplay -> putWord8 0
                InaccessibleArg -> putWord8 1
                AlwaysShow -> putWord8 2
        get
          = do i <- getWord8
               case i of
                   0 -> return HideDisplay
                   1 -> return InaccessibleArg
                   2 -> return AlwaysShow
                   _ -> error "Corrupted binary data for Static"

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
                Constraint x1 x2 ->
                                    do putWord8 2
                                       put x1
                                       put x2
                TacImp x1 x2 x3 ->
                                   do putWord8 3
                                      put x1
                                      put x2
                                      put x3
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
                           return (Constraint x1 x2)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (TacImp x1 x2 x3)
                   _ -> error "Corrupted binary data for Plicity"


instance (Binary t) => Binary (PDecl' t) where
        put x
          = case x of
                PFix x1 x2 x3 -> do putWord8 0
                                    put x1
                                    put x2
                                    put x3
                PTy x1 x2 x3 x4 x5 x6 x7
                                   -> do putWord8 1
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                                         put x5
                                         put x6
                                         put x7
                PClauses x1 x2 x3 x4 -> do putWord8 2
                                           put x1
                                           put x2
                                           put x3
                                           put x4
                PData x1 x2 x3 x4 x5 x6 ->
                                     do putWord8 3
                                        put x1
                                        put x2
                                        put x3
                                        put x4
                                        put x5
                                        put x6
                PParams x1 x2 x3 -> do putWord8 4
                                       put x1
                                       put x2
                                       put x3
                PNamespace x1 x2 -> do putWord8 5
                                       put x1
                                       put x2
                PRecord x1 x2 x3 x4 x5 x6 x7 x8 x9 ->
                                             do putWord8 6
                                                put x1
                                                put x2
                                                put x3
                                                put x4
                                                put x5
                                                put x6
                                                put x7
                                                put x8
                                                put x9
                PClass x1 x2 x3 x4 x5 x6 x7 x8
                                         -> do putWord8 7
                                               put x1
                                               put x2
                                               put x3
                                               put x4
                                               put x5
                                               put x6
                                               put x7
                                               put x8
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
                           x7 <- get
                           return (PTy x1 x2 x3 x4 x5 x6 x7)
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
                           x6 <- get
                           return (PData x1 x2 x3 x4 x5 x6)
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
                           x9 <- get
                           return (PRecord x1 x2 x3 x4 x5 x6 x7 x8 x9)
                   7 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           x7 <- get
                           x8 <- get
                           return (PClass x1 x2 x3 x4 x5 x6 x7 x8)
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
        put (Syn x1 x2 x3 x4 _ x5 x6 _ _ x7 _)
          = do put x1
               put x2
               put x3
               put x4
               put x5
               put x6
               put x7
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               x4 <- get
               x5 <- get
               x6 <- get
               x7 <- get
               return (Syn x1 x2 x3 x4 id x5 x6 Nothing 0 x7 0)

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

instance Binary PunInfo where
        put x
          = case x of
              TypeOrTerm -> putWord8 0
              IsType     -> putWord8 1
              IsTerm     -> putWord8 2
        get
          = do i <- getWord8
               case i of
                 0 -> return TypeOrTerm
                 1 -> return IsType
                 2 -> return IsTerm

instance Binary PTerm where
        put x
          = case x of
                PQuote x1 -> do putWord8 0
                                put x1
                PRef x1 x2 -> do putWord8 1
                                 put x1
                                 put x2
                PInferRef x1 x2 -> do putWord8 2
                                      put x1
                                      put x2
                PPatvar x1 x2 -> do putWord8 3
                                    put x1
                                    put x2
                PLam x1 x2 x3 -> do putWord8 4
                                    put x1
                                    put x2
                                    put x3
                PPi x1 x2 x3 x4 -> do putWord8 5
                                      put x1
                                      put x2
                                      put x3
                                      put x4
                PLet x1 x2 x3 x4 -> do putWord8 6
                                       put x1
                                       put x2
                                       put x3
                                       put x4
                PTyped x1 x2 -> do putWord8 7
                                   put x1
                                   put x2
                PApp x1 x2 x3 -> do putWord8 8
                                    put x1
                                    put x2
                                    put x3
                PAppBind x1 x2 x3 -> do putWord8 9
                                        put x1
                                        put x2
                                        put x3
                PMatchApp x1 x2 -> do putWord8 10
                                      put x1
                                      put x2
                PCase x1 x2 x3 -> do putWord8 11
                                     put x1
                                     put x2
                                     put x3
                PTrue x1 x2 -> do putWord8 12
                                  put x1
                                  put x2
                PRefl x1 x2 -> do putWord8 14
                                  put x1
                                  put x2
                PResolveTC x1 -> do putWord8 15
                                    put x1
                PEq x1 x2 x3 x4 x5 -> do putWord8 16
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                                         put x5
                PRewrite x1 x2 x3 x4 -> do putWord8 17
                                           put x1
                                           put x2
                                           put x3
                                           put x4
                PPair x1 x2 x3 x4 -> do putWord8 18
                                        put x1
                                        put x2
                                        put x3
                                        put x4
                PDPair x1 x2 x3 x4 x5 -> do putWord8 19
                                            put x1
                                            put x2
                                            put x3
                                            put x4
                                            put x5
                PAlternative x1 x2 -> do putWord8 20
                                         put x1
                                         put x2
                PHidden x1 -> do putWord8 21
                                 put x1
                PType -> putWord8 22
                PGoal x1 x2 x3 x4 -> do putWord8 23
                                        put x1
                                        put x2
                                        put x3
                                        put x4
                PConstant x1 -> do putWord8 24
                                   put x1
                Placeholder -> putWord8 25
                PDoBlock x1 -> do putWord8 26
                                  put x1
                PIdiom x1 x2 -> do putWord8 27
                                   put x1
                                   put x2
                PReturn x1 -> do putWord8 28
                                 put x1
                PMetavar x1 -> do putWord8 29
                                  put x1
                PProof x1 -> do putWord8 30
                                put x1
                PTactics x1 -> do putWord8 31
                                  put x1
                PImpossible -> putWord8 33
                PCoerced x1 -> do putWord8 34
                                  put x1
                PUnifyLog x1 -> do putWord8 35
                                   put x1
                PNoImplicits x1 -> do putWord8 36
                                      put x1
                PDisamb x1 x2 -> do putWord8 37
                                    put x1
                                    put x2
                PUniverse x1 -> do putWord8 38
                                   put x1

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
                           return (PInferRef x1 x2)
                   3 -> do x1 <- get
                           x2 <- get
                           return (PPatvar x1 x2)
                   4 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PLam x1 x2 x3)
                   5 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PPi x1 x2 x3 x4)
                   6 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PLet x1 x2 x3 x4)
                   7 -> do x1 <- get
                           x2 <- get
                           return (PTyped x1 x2)
                   8 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PApp x1 x2 x3)
                   9 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PAppBind x1 x2 x3)
                   10 -> do x1 <- get
                            x2 <- get
                            return (PMatchApp x1 x2)
                   11 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PCase x1 x2 x3)
                   12 -> do x1 <- get
                            x2 <- get
                            return (PTrue x1 x2)
                   14 -> do x1 <- get
                            x2 <- get
                            return (PRefl x1 x2)
                   15 -> do x1 <- get
                            return (PResolveTC x1)
                   16 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            x5 <- get
                            return (PEq x1 x2 x3 x4 x5)
                   17 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            return (PRewrite x1 x2 x3 x4)
                   18 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            return (PPair x1 x2 x3 x4)
                   19 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            x5 <- get
                            return (PDPair x1 x2 x3 x4 x5)
                   20 -> do x1 <- get
                            x2 <- get
                            return (PAlternative x1 x2)
                   21 -> do x1 <- get
                            return (PHidden x1)
                   22 -> return PType
                   23 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            return (PGoal x1 x2 x3 x4)
                   24 -> do x1 <- get
                            return (PConstant x1)
                   25 -> return Placeholder
                   26 -> do x1 <- get
                            return (PDoBlock x1)
                   27 -> do x1 <- get
                            x2 <- get
                            return (PIdiom x1 x2)
                   28 -> do x1 <- get
                            return (PReturn x1)
                   29 -> do x1 <- get
                            return (PMetavar x1)
                   30 -> do x1 <- get
                            return (PProof x1)
                   31 -> do x1 <- get
                            return (PTactics x1)
                   33 -> return PImpossible
                   34 -> do x1 <- get
                            return (PCoerced x1)
                   35 -> do x1 <- get
                            return (PUnifyLog x1)
                   36 -> do x1 <- get
                            return (PNoImplicits x1)
                   37 -> do x1 <- get
                            x2 <- get
                            return (PDisamb x1 x2)
                   38 -> do x1 <- get
                            return (PUniverse x1)
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
                Induction x1 -> do putWord8 19
                                   put x1
                ByReflection x1 -> do putWord8 20
                                      put x1
                ProofSearch x1 x2 x3 x4 x5 -> do putWord8 21
                                                 put x1
                                                 put x2
                                                 put x3
                                                 put x4
                                                 put x5
                DoUnify -> putWord8 22
                CaseTac x1 -> do putWord8 23
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
                   19 -> do x1 <- get
                            return (Induction x1)
                   20 -> do x1 <- get
                            return (ByReflection x1)
                   21 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            x5 <- get
                            return (ProofSearch x1 x2 x3 x4 x5)
                   22 -> return DoUnify
                   23 -> do x1 <- get
                            return (CaseTac x1)
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
                DoBindP x1 x2 x3 x4 -> do putWord8 2
                                          put x1
                                          put x2
                                          put x3
                                          put x4
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
                           x4 <- get
                           return (DoBindP x1 x2 x3 x4)
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
                PTacImplicit x1 x2 x3 x4 x5 ->
                                               do putWord8 3
                                                  put x1
                                                  put x2
                                                  put x3
                                                  put x4
                                                  put x5
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
                           return (PTacImplicit x1 x2 x3 x4 x5)
                   _ -> error "Corrupted binary data for PArg'"


instance Binary ClassInfo where
        put (CI x1 x2 x3 x4 x5 _)
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
               return (CI x1 x2 x3 x4 x5 [])

instance Binary OptInfo where
        put (Optimise x1 x2)
          = do put x1
               put x2
        get
          = do x1 <- get
               x2 <- get
               return (Optimise x1 x2)

instance Binary FnInfo where
        put (FnInfo x1)
          = put x1
        get
          = do x1 <- get
               return (FnInfo x1)

instance Binary TypeInfo where
        put (TI x1 x2 x3 x4 x5) = do put x1
                                     put x2
                                     put x3
                                     put x4
                                     put x5
        get = do x1 <- get
                 x2 <- get
                 x3 <- get
                 x4 <- get
                 x5 <- get
                 return (TI x1 x2 x3 x4 x5)

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
        put (DSL x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
          = do put x1
               put x2
               put x3
               put x4
               put x5
               put x6
               put x7
               put x8
               put x9
               put x10
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
               x10 <- get
               return (DSL x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)

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

instance Binary Codegen where
        put x
          = case x of
                Via str -> do putWord8 0
                              put str
                Bytecode -> putWord8 1
        get
          = do i <- getWord8
               case i of
                  0 -> do x1 <- get
                          return (Via x1)
                  1 -> return Bytecode
                  _ -> error  "Corrupted binary data for Codegen"

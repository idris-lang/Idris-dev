{-|
Module      : Idris.IBC
Description : Core representations and code to generate IBC files.

License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fwarn-unused-imports #-}

module Idris.IBC (loadIBC, loadPkgIndex,
                  writeIBC, writePkgIndex,
                  hasValidIBCVersion, IBCPhase(..),
                  getIBCHash, getImportHashes) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.DeepSeq ()
import Idris.Docstrings (Docstring)
import qualified Idris.Docstrings as D
import Idris.Error
import Idris.Imports
import Idris.Options
import Idris.Output
import IRTS.System (getIdrisLibDir)

import qualified Cheapskate.Types as CT
import Codec.Archive.Zip
import Control.DeepSeq
import Control.Monad
import Data.Binary
import Data.ByteString.Lazy as B hiding (elem, length, map)
import Data.List as L
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import System.Directory
import System.FilePath

ibcVersion :: Word16
ibcVersion = 166

-- | When IBC is being loaded - we'll load different things (and omit
-- different structures/definitions) depending on which phase we're in.
data IBCPhase = IBC_Building  -- ^ when building the module tree
              | IBC_REPL Bool -- ^ when loading modules for the REPL Bool = True for top level module
  deriving (Show, Eq)

data IBCFile = IBCFile {
    ver                        :: Word16
  , iface_hash                 :: Int
  , sourcefile                 :: FilePath
  , ibc_imports                :: ![(Bool, FilePath)]
  , ibc_importdirs             :: ![FilePath]
  , ibc_sourcedirs             :: ![FilePath]
  , ibc_implicits              :: ![(Name, [PArg])]
  , ibc_fixes                  :: ![FixDecl]
  , ibc_statics                :: ![(Name, [Bool])]
  , ibc_interfaces             :: ![(Name, InterfaceInfo)]
  , ibc_records                :: ![(Name, RecordInfo)]
  , ibc_implementations        :: ![(Bool, Bool, Name, Name)]
  , ibc_dsls                   :: ![(Name, DSL)]
  , ibc_datatypes              :: ![(Name, TypeInfo)]
  , ibc_optimise               :: ![(Name, OptInfo)]
  , ibc_syntax                 :: ![Syntax]
  , ibc_keywords               :: ![String]
  , ibc_objs                   :: ![(Codegen, FilePath)]
  , ibc_libs                   :: ![(Codegen, String)]
  , ibc_cgflags                :: ![(Codegen, String)]
  , ibc_dynamic_libs           :: ![String]
  , ibc_hdrs                   :: ![(Codegen, String)]
  , ibc_totcheckfail           :: ![(FC, String)]
  , ibc_flags                  :: ![(Name, [FnOpt])]
  , ibc_fninfo                 :: ![(Name, FnInfo)]
  , ibc_cg                     :: ![(Name, CGInfo)]
  , ibc_docstrings             :: ![(Name, (Docstring D.DocTerm, [(Name, Docstring D.DocTerm)]))]
  , ibc_moduledocs             :: ![(Name, Docstring D.DocTerm)]
  , ibc_transforms             :: ![(Name, (Term, Term))]
  , ibc_errRev                 :: ![(Term, Term)]
  , ibc_errReduce              :: ![Name]
  , ibc_coercions              :: ![Name]
  , ibc_lineapps               :: ![(FilePath, Int, PTerm)]
  , ibc_namehints              :: ![(Name, Name)]
  , ibc_metainformation        :: ![(Name, MetaInformation)]
  , ibc_errorhandlers          :: ![Name]
  , ibc_function_errorhandlers :: ![(Name, Name, Name)] -- fn, arg, handler
  , ibc_metavars               :: ![(Name, (Maybe Name, Int, [Name], Bool, Bool))]
  , ibc_patdefs                :: ![(Name, ([([(Name, Term)], Term, Term)], [PTerm]))]
  , ibc_postulates             :: ![Name]
  , ibc_externs                :: ![(Name, Int)]
  , ibc_parsedSpan             :: !(Maybe FC)
  , ibc_usage                  :: ![(Name, Int)]
  , ibc_exports                :: ![Name]
  , ibc_autohints              :: ![(Name, Name)]
  , ibc_deprecated             :: ![(Name, String)]
  , ibc_defs                   :: ![(Name, Def)]
  , ibc_total                  :: ![(Name, Totality)]
  , ibc_injective              :: ![(Name, Injectivity)]
  , ibc_access                 :: ![(Name, Accessibility)]
  , ibc_fragile                :: ![(Name, String)]
  , ibc_constraints            :: ![(FC, UConstraint)]
  , ibc_langexts               :: ![LanguageExt]
  , ibc_importhashes           :: ![(FilePath, Int)]
  }
  deriving Show
{-!
deriving instance Binary IBCFile
!-}

initIBC :: IBCFile
initIBC = IBCFile ibcVersion 0 "" [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] Nothing [] [] [] [] [] [] [] [] [] [] [] []

hasValidIBCVersion :: FilePath -> Idris Bool
hasValidIBCVersion fp = do
  archiveFile <- runIO $ B.readFile fp
  case toArchiveOrFail archiveFile of
    Left _ -> return False
    Right archive -> do ver <- getEntry 0 "ver" archive
                        return (ver == ibcVersion)


loadIBC :: Bool -- ^ True = reexport, False = make everything private
        -> IBCPhase
        -> FilePath -> Idris ()
loadIBC reexport phase fp
           = do logIBC 1 $ "loadIBC (reexport, phase, fp)" ++ show (reexport, phase, fp)
                imps <- getImported
                logIBC 3 $ "loadIBC imps" ++ show imps
                case lookup fp imps of
                    Nothing -> load True
                    Just p -> if (not p && reexport) then load False else return ()
        where
            load fullLoad = do
                    logIBC 1 $ "Loading ibc " ++ fp ++ " " ++ show reexport
                    archiveFile <- runIO $ B.readFile fp
                    case toArchiveOrFail archiveFile of
                        Left _ -> do
                            ifail $ fp  ++ " isn't loadable, it may have an old ibc format.\n"
                                        ++ "Please clean and rebuild it."
                        Right archive -> do
                            if fullLoad
                                then process reexport phase archive fp
                                else unhide phase fp archive
                            addImported reexport fp

getIBCHash :: FilePath -> Idris Int
getIBCHash fp
    = do archiveFile <- runIO $ B.readFile fp
         case toArchiveOrFail archiveFile of
              Left _ -> return 0
              Right archive -> getEntry 0 "iface_hash" archive


getImportHashes :: FilePath -> Idris [(FilePath, Int)]
getImportHashes fp
    = do archiveFile <- runIO $ B.readFile fp
         case toArchiveOrFail archiveFile of
              Left _ -> return []
              Right archive -> getEntry [] "ibc_importhashes" archive

-- | Load an entire package from its index file
loadPkgIndex :: PkgName -> Idris ()
loadPkgIndex pkg = do ddir <- runIO getIdrisLibDir
                      addImportDir (ddir </> unPkgName pkg)
                      fp <- findPkgIndex pkg
                      loadIBC True IBC_Building fp


makeEntry :: (Binary b) => String -> [b] -> Maybe Entry
makeEntry name val = if L.null val
                        then Nothing
                        else Just $ toEntry name 0 (encode val)


entries :: IBCFile -> [Entry]
entries i = catMaybes [Just $ toEntry "ver" 0 (encode $ ver i),
                       Just $ toEntry "iface_hash" 0 (encode $ iface_hash i),
                       makeEntry "sourcefile"  (sourcefile i),
                       makeEntry "ibc_imports"  (ibc_imports i),
                       makeEntry "ibc_importdirs"  (ibc_importdirs i),
                       makeEntry "ibc_sourcedirs"  (ibc_sourcedirs i),
                       makeEntry "ibc_implicits"  (ibc_implicits i),
                       makeEntry "ibc_fixes"  (ibc_fixes i),
                       makeEntry "ibc_statics"  (ibc_statics i),
                       makeEntry "ibc_interfaces"  (ibc_interfaces i),
                       makeEntry "ibc_records"  (ibc_records i),
                       makeEntry "ibc_implementations"  (ibc_implementations i),
                       makeEntry "ibc_dsls"  (ibc_dsls i),
                       makeEntry "ibc_datatypes"  (ibc_datatypes i),
                       makeEntry "ibc_optimise"  (ibc_optimise i),
                       makeEntry "ibc_syntax"  (ibc_syntax i),
                       makeEntry "ibc_keywords"  (ibc_keywords i),
                       makeEntry "ibc_objs"  (ibc_objs i),
                       makeEntry "ibc_libs"  (ibc_libs i),
                       makeEntry "ibc_cgflags"  (ibc_cgflags i),
                       makeEntry "ibc_dynamic_libs"  (ibc_dynamic_libs i),
                       makeEntry "ibc_hdrs"  (ibc_hdrs i),
                       makeEntry "ibc_totcheckfail"  (ibc_totcheckfail i),
                       makeEntry "ibc_flags"  (ibc_flags i),
                       makeEntry "ibc_fninfo"  (ibc_fninfo i),
                       makeEntry "ibc_cg"  (ibc_cg i),
                       makeEntry "ibc_docstrings"  (ibc_docstrings i),
                       makeEntry "ibc_moduledocs"  (ibc_moduledocs i),
                       makeEntry "ibc_transforms"  (ibc_transforms i),
                       makeEntry "ibc_errRev"  (ibc_errRev i),
                       makeEntry "ibc_errReduce"  (ibc_errReduce i),
                       makeEntry "ibc_coercions"  (ibc_coercions i),
                       makeEntry "ibc_lineapps"  (ibc_lineapps i),
                       makeEntry "ibc_namehints"  (ibc_namehints i),
                       makeEntry "ibc_metainformation"  (ibc_metainformation i),
                       makeEntry "ibc_errorhandlers"  (ibc_errorhandlers i),
                       makeEntry "ibc_function_errorhandlers"  (ibc_function_errorhandlers i),
                       makeEntry "ibc_metavars"  (ibc_metavars i),
                       makeEntry "ibc_patdefs"  (ibc_patdefs i),
                       makeEntry "ibc_postulates"  (ibc_postulates i),
                       makeEntry "ibc_externs"  (ibc_externs i),
                       toEntry "ibc_parsedSpan" 0 . encode <$> ibc_parsedSpan i,
                       makeEntry "ibc_usage"  (ibc_usage i),
                       makeEntry "ibc_exports"  (ibc_exports i),
                       makeEntry "ibc_autohints"  (ibc_autohints i),
                       makeEntry "ibc_deprecated"  (ibc_deprecated i),
                       makeEntry "ibc_defs"  (ibc_defs i),
                       makeEntry "ibc_total"  (ibc_total i),
                       makeEntry "ibc_injective"  (ibc_injective i),
                       makeEntry "ibc_access"  (ibc_access i),
                       makeEntry "ibc_fragile" (ibc_fragile i),
                       makeEntry "ibc_langexts" (ibc_langexts i),
                       makeEntry "ibc_importhashes" (ibc_importhashes i)]
-- TODO: Put this back in shortly after minimising/pruning constraints
--                        makeEntry "ibc_constraints" (ibc_constraints i)]

writeArchive :: FilePath -> IBCFile -> Idris ()
writeArchive fp i = do let a = L.foldl (\x y -> addEntryToArchive y x) emptyArchive (entries i)
                       runIO $ B.writeFile fp (fromArchive a)

writeIBC :: FilePath -> FilePath -> Idris ()
writeIBC src f
    = do
         logIBC  2 $ "Writing IBC for: " ++ show f
         iReport 2 $ "Writing IBC for: " ++ show f
         i <- getIState
         resetNameIdx
         ibc_data <- mkIBC (ibc_write i) (initIBC { sourcefile = src,
                                                    ibc_langexts = idris_language_extensions i })
         let ibcf = ibc_data { iface_hash = calculateHash i ibc_data }
         logIBC 5 $ "Hash for " ++ show f ++ " = " ++ show (iface_hash ibcf)
         idrisCatch (do runIO $ createDirectoryIfMissing True (dropFileName f)
                        writeArchive f ibcf
                        logIBC 2 "Written")
            (\c -> do logIBC 2 $ "Failed " ++ pshow i c)
         return ()

qhash :: Int -> String -> Int
qhash hash [] = abs hash `mod` 0xffffffff
qhash hash (x:xs) = qhash (hash * 33 + fromIntegral (fromEnum x)) xs

hashTerm :: Int -> Term -> Int
hashTerm i t = qhash (i * 5381) (show t)

hashName :: Int -> Name -> Int
hashName i n = qhash (i * 5381) (show n)

calculateHash :: IState -> IBCFile -> Int
calculateHash ist f
    = let acc = L.filter exported (ibc_access f) in
          mkHashFrom (map fst acc) (getDefs acc)
  where
    mkHashFrom :: [Name] -> [Term] -> Int
    mkHashFrom ns tms = sum (L.zipWith hashName [1..] ns) + 
                        sum (L.zipWith hashTerm [1..] tms)

    exported (_, Public) = True
    exported (_, Frozen) = True
    exported _ = False

    findTms :: [(a, Term, Term)] -> [Term]
    findTms = L.concatMap (\ (_, x, y) -> [x, y])

    patDef :: Name -> [Term]
    patDef n
        = case lookupCtxtExact n (idris_patdefs ist) of
               Nothing -> []
               Just (tms, _) -> findTms tms

    getDefs :: [(Name, Accessibility)] -> [Term]
    getDefs [] = []
    getDefs ((n, Public) : ns)
        = let ts = getDefs ns in
              case lookupTyExact n (tt_ctxt ist) of
                   Nothing -> ts
                   Just ty -> ty : patDef n ++ ts
    getDefs ((n, Frozen) : ns)
        = let ts = getDefs ns in
              case lookupTyExact n (tt_ctxt ist) of
                   Nothing -> ts
                   Just ty -> ty : ts
    getDefs (_ : ns) = getDefs ns

-- | Write a package index containing all the imports in the current
-- IState Used for ':search' of an entire package, to ensure
-- everything is loaded.
writePkgIndex :: FilePath -> Idris ()
writePkgIndex f
    = do i <- getIState
         let imps = map (\ (x, y) -> (True, x)) $ idris_imported i
         logIBC 2 $ "Writing package index " ++ show f ++ " including\n" ++
                show (map snd imps)
         resetNameIdx
         let ibcf = initIBC { ibc_imports = imps,
                              ibc_langexts = idris_language_extensions i }
         idrisCatch (do runIO $ createDirectoryIfMissing True (dropFileName f)
                        writeArchive f ibcf
                        logIBC 2 "Written")
            (\c -> do logIBC 2 $ "Failed " ++ pshow i c)
         return ()

mkIBC :: [IBCWrite] -> IBCFile -> Idris IBCFile
mkIBC [] f = return f
mkIBC (i:is) f = do ist <- getIState
                    logIBC 5 $ show i ++ " " ++ show (L.length is)
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
ibc i (IBCInterface n) f
                   = case lookupCtxtExact n (idris_interfaces i) of
                        Just v -> return f { ibc_interfaces = (n,v): ibc_interfaces f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCRecord n) f
                   = case lookupCtxtExact n (idris_records i) of
                        Just v -> return f { ibc_records = (n,v): ibc_records f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCImplementation int res n ins) f
                   = return f { ibc_implementations = (int, res, n, ins) : ibc_implementations f }
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
ibc i (IBCSourceDir n) f = return f { ibc_sourcedirs = n : ibc_sourcedirs f }
ibc i (IBCObj tgt n) f = return f { ibc_objs = (tgt, n) : ibc_objs f }
ibc i (IBCLib tgt n) f = return f { ibc_libs = (tgt, n) : ibc_libs f }
ibc i (IBCCGFlag tgt n) f = return f { ibc_cgflags = (tgt, n) : ibc_cgflags f }
ibc i (IBCDyLib n) f = return f {ibc_dynamic_libs = n : ibc_dynamic_libs f }
ibc i (IBCHeader tgt n) f = return f { ibc_hdrs = (tgt, n) : ibc_hdrs f }
ibc i (IBCDef n) f
   = do f' <- case lookupDefExact n (tt_ctxt i) of
                   Just v -> return f { ibc_defs = (n,v) : ibc_defs f }
                   _ -> ifail "IBC write failed"
        case lookupCtxtExact n (idris_patdefs i) of
                   Just v -> return f' { ibc_patdefs = (n,v) : ibc_patdefs f }
                   _ -> return f' -- Not a pattern definition

ibc i (IBCDoc n) f = case lookupCtxtExact n (idris_docstrings i) of
                        Just v -> return f { ibc_docstrings = (n,v) : ibc_docstrings f }
                        _ -> ifail "IBC write failed"
ibc i (IBCCG n) f = case lookupCtxtExact n (idris_callgraph i) of
                        Just v -> return f { ibc_cg = (n,v) : ibc_cg f     }
                        _ -> ifail "IBC write failed"
ibc i (IBCCoercion n) f = return f { ibc_coercions = n : ibc_coercions f }
ibc i (IBCAccess n a) f = return f { ibc_access = (n,a) : ibc_access f }
ibc i (IBCFlags n) f
    = case lookupCtxtExact n (idris_flags i) of
           Just a -> return f { ibc_flags = (n,a): ibc_flags f }
           _ -> ifail "IBC write failed"
ibc i (IBCFnInfo n a) f = return f { ibc_fninfo = (n,a) : ibc_fninfo f }
ibc i (IBCTotal n a) f = return f { ibc_total = (n,a) : ibc_total f }
ibc i (IBCInjective n a) f = return f { ibc_injective = (n,a) : ibc_injective f }
ibc i (IBCTrans n t) f = return f { ibc_transforms = (n, t) : ibc_transforms f }
ibc i (IBCErrRev t) f = return f { ibc_errRev = t : ibc_errRev f }
ibc i (IBCErrReduce t) f = return f { ibc_errReduce = t : ibc_errReduce f }
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
ibc i (IBCExtern n) f = return f { ibc_externs = n : ibc_externs f }
ibc i (IBCTotCheckErr fc err) f = return f { ibc_totcheckfail = (fc, err) : ibc_totcheckfail f }
ibc i (IBCParsedRegion fc) f = return f { ibc_parsedSpan = Just fc }
ibc i (IBCModDocs n) f = case lookupCtxtExact n (idris_moduledocs i) of
                           Just v -> return f { ibc_moduledocs = (n,v) : ibc_moduledocs f }
                           _ -> ifail "IBC write failed"
ibc i (IBCUsage n) f = return f { ibc_usage = n : ibc_usage f }
ibc i (IBCExport n) f = return f { ibc_exports = n : ibc_exports f }
ibc i (IBCAutoHint n h) f = return f { ibc_autohints = (n, h) : ibc_autohints f }
ibc i (IBCDeprecate n r) f = return f { ibc_deprecated = (n, r) : ibc_deprecated f }
ibc i (IBCFragile n r)   f = return f { ibc_fragile    = (n,r)  : ibc_fragile f }
ibc i (IBCConstraint fc u)  f = return f { ibc_constraints = (fc, u) : ibc_constraints f }
ibc i (IBCImportHash fn h) f = return f { ibc_importhashes = (fn, h) : ibc_importhashes f }

getEntry :: (Binary b, NFData b) => b -> FilePath -> Archive -> Idris b
getEntry alt f a = case findEntryByPath f a of
                Nothing -> return alt
                Just e -> return $! (force . decode . fromEntry) e

unhide :: IBCPhase -> FilePath -> Archive -> Idris ()
unhide phase fp ar = do
    processImports True phase fp ar
    processAccess True phase ar

process :: Bool -- ^ Reexporting
           -> IBCPhase
           -> Archive -> FilePath -> Idris ()
process reexp phase archive fn = do
                ver <- getEntry 0 "ver" archive
                when (ver /= ibcVersion) $ do
                                    logIBC 2 "ibc out of date"
                                    let e = if ver < ibcVersion
                                            then "an earlier" else "a later"
                                    ldir <- runIO $ getIdrisLibDir
                                    let start = if ldir `L.isPrefixOf` fn
                                                  then "This external module"
                                                  else "This module"
                                    let end = case L.stripPrefix ldir fn of
                                                Nothing -> "Please clean and rebuild."

                                                Just ploc -> unwords ["Please reinstall:", L.head $ splitDirectories ploc]
                                    ifail $ unlines [ unwords ["Incompatible ibc version for:", show fn]
                                                    , unwords [start
                                                              , "was built with"
                                                              , e
                                                              , "version of Idris."]
                                                    , end
                                                    ]
                source <- getEntry "" "sourcefile" archive
                srcok <- runIO $ doesFileExist source
                when srcok $ timestampOlder source fn
                processImportDirs archive
                processSourceDirs archive
                processImports reexp phase fn archive
                processImplicits archive
                processInfix archive
                processStatics archive
                processInterfaces archive
                processRecords archive
                processImplementations archive
                processDSLs archive
                processDatatypes  archive
                processOptimise  archive
                processSyntax archive
                processKeywords archive
                processObjectFiles fn archive
                processLibs archive
                processCodegenFlags archive
                processDynamicLibs archive
                processHeaders archive
                processPatternDefs archive
                processFlags archive
                processFnInfo archive
                processTotalityCheckError archive
                processCallgraph archive
                processDocs archive
                processModuleDocs archive
                processCoercions archive
                processTransforms archive
                processErrRev archive
                processErrReduce archive
                processLineApps archive
                processNameHints archive
                processMetaInformation archive
                processErrorHandlers archive
                processFunctionErrorHandlers archive
                processMetaVars archive
                processPostulates archive
                processExterns archive
                processParsedSpan archive
                processUsage archive
                processExports archive
                processAutoHints archive
                processDeprecate archive
                processDefs archive
                processTotal archive
                processInjective archive
                processAccess reexp phase archive
                processFragile archive
                processConstraints archive
                processLangExts phase archive

timestampOlder :: FilePath -> FilePath -> Idris ()
timestampOlder src ibc = do
  srct <- runIO $ getModificationTime src
  ibct <- runIO $ getModificationTime ibc
  if (srct > ibct)
    then ifail $ unlines [ "Module needs reloading:"
                         , unwords ["\tSRC :", show src]
                         , unwords ["\tModified at:", show srct]
                         , unwords ["\tIBC :", show ibc]
                         , unwords ["\tModified at:", show ibct]
                         ]
    else return ()

processPostulates :: Archive -> Idris ()
processPostulates ar = do
    ns <- getEntry [] "ibc_postulates" ar
    updateIState (\i -> i { idris_postulates = idris_postulates i `S.union` S.fromList ns })

processExterns :: Archive -> Idris ()
processExterns ar = do
    ns <-  getEntry [] "ibc_externs" ar
    updateIState (\i -> i{ idris_externs = idris_externs i `S.union` S.fromList ns })

processParsedSpan :: Archive -> Idris ()
processParsedSpan ar = do
    fc <- getEntry Nothing "ibc_parsedSpan" ar
    updateIState (\i -> i { idris_parsedSpan = fc })

processUsage :: Archive -> Idris ()
processUsage ar = do
    ns <- getEntry [] "ibc_usage" ar
    updateIState (\i -> i { idris_erasureUsed = ns ++ idris_erasureUsed i })

processExports :: Archive -> Idris ()
processExports ar = do
    ns <- getEntry [] "ibc_exports" ar
    updateIState (\i -> i { idris_exports = ns ++ idris_exports i })

processAutoHints :: Archive -> Idris ()
processAutoHints ar = do
    ns <- getEntry [] "ibc_autohints" ar
    mapM_ (\(n,h) -> addAutoHint n h) ns

processDeprecate :: Archive -> Idris ()
processDeprecate ar = do
    ns <-  getEntry [] "ibc_deprecated" ar
    mapM_ (\(n,reason) -> addDeprecated n reason) ns

processFragile :: Archive -> Idris ()
processFragile ar = do
    ns <- getEntry [] "ibc_fragile" ar
    mapM_ (\(n,reason) -> addFragile n reason) ns

processConstraints :: Archive -> Idris ()
processConstraints ar = do
    cs <- getEntry [] "ibc_constraints" ar
    mapM_ (\ (fc, c) -> addConstraints fc (0, [c])) cs

processImportDirs :: Archive -> Idris ()
processImportDirs ar = do
    fs <- getEntry [] "ibc_importdirs" ar
    mapM_ addImportDir fs

processSourceDirs :: Archive -> Idris ()
processSourceDirs ar = do
    fs <- getEntry [] "ibc_sourcedirs" ar
    mapM_ addSourceDir fs

processImports :: Bool -> IBCPhase -> FilePath -> Archive -> Idris ()
processImports reexp phase fname ar = do
    fs <- getEntry [] "ibc_imports" ar
    mapM_ (\(re, f) -> do
        i <- getIState
        ibcsd <- valIBCSubDir i
        ids <- rankedImportDirs fname
        putIState (i { imported = f : imported i })
        let (phase', reexp') =
              case phase of
                IBC_REPL True -> (IBC_REPL False, reexp)
                IBC_REPL False -> (IBC_Building, reexp && re)
                p -> (p, reexp && re)
        fp <- findIBC ids ibcsd f
        logIBC 4 $ "processImports (fp, phase')" ++ show (fp, phase')
        case fp of
            Nothing -> do logIBC 2 $ "Failed to load ibc " ++ f
            Just fn -> do loadIBC reexp' phase' fn) fs

processImplicits :: Archive -> Idris ()
processImplicits ar = do
    imps <- getEntry [] "ibc_implicits" ar
    mapM_ (\ (n, imp) -> do
        i <- getIState
        case lookupDefAccExact n False (tt_ctxt i) of
            Just (n, Hidden) -> return ()
            Just (n, Private) -> return ()
            _ -> putIState (i { idris_implicits = addDef n imp (idris_implicits i) })) imps

processInfix :: Archive -> Idris ()
processInfix ar = do
    f <- getEntry [] "ibc_fixes" ar
    updateIState (\i -> i { idris_infixes = sort $ f ++ idris_infixes i })

processStatics :: Archive -> Idris ()
processStatics ar = do
    ss <- getEntry [] "ibc_statics" ar
    mapM_ (\ (n, s) ->
        updateIState (\i -> i { idris_statics = addDef n s (idris_statics i) })) ss

processInterfaces :: Archive -> Idris ()
processInterfaces ar = do
    cs <- getEntry [] "ibc_interfaces" ar
    mapM_ (\ (n, c) -> do
        i <- getIState
        -- Don't lose implementations from previous IBCs, which
        -- could have loaded in any order
        let is = case lookupCtxtExact n (idris_interfaces i) of
                    Just ci -> interface_implementations ci
                    _ -> []
        let c' = c { interface_implementations = interface_implementations c ++ is }
        putIState (i { idris_interfaces = addDef n c' (idris_interfaces i) })) cs

processRecords :: Archive -> Idris ()
processRecords ar = do
    rs <- getEntry [] "ibc_records" ar
    mapM_ (\ (n, r) ->
        updateIState (\i -> i { idris_records = addDef n r (idris_records i) })) rs

processImplementations :: Archive -> Idris ()
processImplementations ar = do
    cs <- getEntry [] "ibc_implementations" ar
    mapM_ (\ (i, res, n, ins) -> addImplementation i res n ins) cs

processDSLs :: Archive -> Idris ()
processDSLs ar = do
    cs <- getEntry [] "ibc_dsls" ar
    mapM_ (\ (n, c) -> updateIState (\i ->
                        i { idris_dsls = addDef n c (idris_dsls i) })) cs

processDatatypes :: Archive -> Idris ()
processDatatypes ar = do
    cs <- getEntry [] "ibc_datatypes" ar
    mapM_ (\ (n, c) -> updateIState (\i ->
                        i { idris_datatypes = addDef n c (idris_datatypes i) })) cs

processOptimise :: Archive -> Idris ()
processOptimise ar = do
    cs <- getEntry [] "ibc_optimise" ar
    mapM_ (\ (n, c) -> updateIState (\i ->
                        i { idris_optimisation = addDef n c (idris_optimisation i) })) cs

processSyntax :: Archive -> Idris ()
processSyntax ar = do
    s <- getEntry [] "ibc_syntax" ar
    updateIState (\i -> i { syntax_rules = updateSyntaxRules s (syntax_rules i) })

processKeywords :: Archive -> Idris ()
processKeywords ar = do
    k <- getEntry [] "ibc_keywords" ar
    updateIState (\i -> i { syntax_keywords = k ++ syntax_keywords i })

processObjectFiles :: FilePath -> Archive -> Idris ()
processObjectFiles fn ar = do
    os <- getEntry [] "ibc_objs" ar
    mapM_ (\ (cg, obj) -> do
        dirs <- rankedImportDirs fn
        o <- runIO $ findInPath dirs obj
        addObjectFile cg o) os

processLibs :: Archive -> Idris ()
processLibs ar = do
    ls <- getEntry [] "ibc_libs" ar
    mapM_ (uncurry addLib) ls

processCodegenFlags :: Archive -> Idris ()
processCodegenFlags ar = do
    ls <- getEntry [] "ibc_cgflags" ar
    mapM_ (uncurry addFlag) ls

processDynamicLibs :: Archive -> Idris ()
processDynamicLibs ar = do
        ls <- getEntry [] "ibc_dynamic_libs" ar
        res <- mapM (addDyLib . return) ls
        mapM_ checkLoad res
    where
        checkLoad (Left _) = return ()
        checkLoad (Right err) = ifail err

processHeaders :: Archive -> Idris ()
processHeaders ar = do
    hs <- getEntry [] "ibc_hdrs" ar
    mapM_ (uncurry addHdr) hs

processPatternDefs :: Archive -> Idris ()
processPatternDefs ar = do
    ds <- getEntry [] "ibc_patdefs" ar
    mapM_ (\ (n, d) -> updateIState (\i ->
            i { idris_patdefs = addDef n (force d) (idris_patdefs i) })) ds

processDefs :: Archive -> Idris ()
processDefs ar = do
        ds <- getEntry [] "ibc_defs" ar
        logIBC 4 $ "processDefs ds" ++ show ds
        mapM_ (\ (n, d) -> do
            d' <- updateDef d
            case d' of
                TyDecl _ _ -> return ()
                _ -> do
                    logIBC 2 $ "SOLVING " ++ show n
                    solveDeferred emptyFC n
            updateIState (\i -> i { tt_ctxt = addCtxtDef n d' (tt_ctxt i) })) ds
    where
        updateDef (CaseOp c t args o s cd) = do
            o' <- mapM updateOrig o
            cd' <- updateCD cd
            return $ CaseOp c t args o' s cd'
        updateDef t = return t

        updateOrig (Left t) = liftM Left (update t)
        updateOrig (Right (l, r)) = do
            l' <- update l
            r' <- update r
            return $ Right (l', r')

        updateCD (CaseDefs (cs, c) (rs, r)) = do
            c' <- updateSC c
            r' <- updateSC r
            return $ CaseDefs (cs, c') (rs, r')

        updateSC (Case t n alts) = do
            alts' <- mapM updateAlt alts
            return (Case t n alts')
        updateSC (ProjCase t alts) = do
            alts' <- mapM updateAlt alts
            return (ProjCase t alts')
        updateSC (STerm t) = do
            t' <- update t
            return (STerm t')
        updateSC c = return c

        updateAlt (ConCase n i ns t) = do
            t' <- updateSC t
            return (ConCase n i ns t')
        updateAlt (FnCase n ns t) = do
            t' <- updateSC t
            return (FnCase n ns t')
        updateAlt (ConstCase c t) = do
            t' <- updateSC t
            return (ConstCase c t')
        updateAlt (SucCase n t) = do
            t' <- updateSC t
            return (SucCase n t')
        updateAlt (DefaultCase t) = do
            t' <- updateSC t
            return (DefaultCase t')

        -- We get a lot of repetition in sub terms and can save a fair chunk
        -- of memory if we make sure they're shared. addTT looks for a term
        -- and returns it if it exists already, while also keeping stats of
        -- how many times a subterm is repeated.
        update t = do
            tm <- addTT t
            case tm of
                Nothing -> update' t
                Just t' -> return t'

        update' (P t n ty) = do
            n' <- getSymbol n
            return $ P t n' ty
        update' (App s f a) = liftM2 (App s) (update' f) (update' a)
        update' (Bind n b sc) = do
            b' <- updateB b
            sc' <- update sc
            return $ Bind n b' sc'
                where
                    updateB (Let rig t v) = liftM2 (Let rig) (update' t) (update' v)
                    updateB b = do
                        ty' <- update' (binderTy b)
                        return (b { binderTy = ty' })
        update' (Proj t i) = do
                  t' <- update' t
                  return $ Proj t' i
        update' t = return t

processDocs :: Archive -> Idris ()
processDocs ar = do
    ds <- getEntry [] "ibc_docstrings" ar
    mapM_ (\(n, a) -> addDocStr n (fst a) (snd a)) ds

processModuleDocs :: Archive -> Idris ()
processModuleDocs ar = do
    ds <- getEntry [] "ibc_moduledocs" ar
    mapM_  (\ (n, d) -> updateIState (\i ->
            i { idris_moduledocs = addDef n d (idris_moduledocs i) })) ds

processAccess :: Bool -- ^ Reexporting?
           -> IBCPhase
           -> Archive -> Idris ()
processAccess reexp phase ar = do
    logIBC 3 $ "processAccess (reexp, phase)" ++ show (reexp, phase)
    ds <- getEntry [] "ibc_access" ar
    logIBC 3 $ "processAccess ds" ++ show ds
    mapM_ (\ (n, a_in) -> do

        let a = if reexp then a_in else Hidden
        logIBC 3 $ "Setting " ++ show (a, n) ++ " to " ++ show a
        updateIState (\i -> i { tt_ctxt = setAccess n a (tt_ctxt i) })

        if (not reexp)
            then do
                logIBC 2 $ "Not exporting " ++ show n
                setAccessibility n Hidden
            else
                logIBC 2 $ "Exporting " ++ show n

        -- Everything should be available at the REPL from
        -- things imported publicly.
        when (phase == IBC_REPL True) $ do
            logIBC 2 $ "Top level, exporting " ++ show n
            setAccessibility n Public
      ) ds

processFlags :: Archive -> Idris ()
processFlags ar = do
    ds <- getEntry [] "ibc_flags" ar
    mapM_ (\ (n, a) -> setFlags n a) ds

processFnInfo :: Archive -> Idris ()
processFnInfo ar = do
    ds <- getEntry [] "ibc_fninfo" ar
    mapM_ (\ (n, a) -> setFnInfo n a) ds

processTotal :: Archive -> Idris ()
processTotal ar = do
    ds <- getEntry [] "ibc_total" ar
    mapM_ (\ (n, a) -> updateIState (\i -> i { tt_ctxt = setTotal n a (tt_ctxt i) })) ds

processInjective :: Archive -> Idris ()
processInjective ar = do
    ds <- getEntry [] "ibc_injective" ar
    mapM_ (\ (n, a) -> updateIState (\i -> i { tt_ctxt = setInjective n a (tt_ctxt i) })) ds

processTotalityCheckError :: Archive -> Idris ()
processTotalityCheckError ar = do
    es <- getEntry [] "ibc_totcheckfail" ar
    updateIState (\i -> i { idris_totcheckfail = idris_totcheckfail i ++ es })

processCallgraph :: Archive -> Idris ()
processCallgraph ar = do
    ds <- getEntry [] "ibc_cg" ar
    mapM_ (\ (n, a) -> addToCG n a) ds

processCoercions :: Archive -> Idris ()
processCoercions ar = do
    ns <- getEntry [] "ibc_coercions" ar
    mapM_ (\ n -> addCoercion n) ns

processTransforms :: Archive -> Idris ()
processTransforms ar = do
    ts <- getEntry [] "ibc_transforms" ar
    mapM_ (\ (n, t) -> addTrans n t) ts

processErrRev :: Archive -> Idris ()
processErrRev ar = do
    ts <- getEntry [] "ibc_errRev" ar
    mapM_ addErrRev ts

processErrReduce :: Archive -> Idris ()
processErrReduce ar = do
    ts <- getEntry [] "ibc_errReduce" ar
    mapM_ addErrReduce ts

processLineApps :: Archive -> Idris ()
processLineApps ar = do
    ls <- getEntry [] "ibc_lineapps" ar
    mapM_ (\ (f, i, t) -> addInternalApp f i t) ls

processNameHints :: Archive -> Idris ()
processNameHints ar = do
    ns <- getEntry [] "ibc_namehints" ar
    mapM_ (\ (n, ty) -> addNameHint n ty) ns

processMetaInformation :: Archive -> Idris ()
processMetaInformation ar = do
    ds <- getEntry [] "ibc_metainformation" ar
    mapM_ (\ (n, m) -> updateIState (\i ->
                               i { tt_ctxt = setMetaInformation n m (tt_ctxt i) })) ds

processErrorHandlers :: Archive -> Idris ()
processErrorHandlers ar = do
    ns <- getEntry [] "ibc_errorhandlers" ar
    updateIState (\i -> i { idris_errorhandlers = idris_errorhandlers i ++ ns })

processFunctionErrorHandlers :: Archive -> Idris ()
processFunctionErrorHandlers ar = do
    ns <- getEntry [] "ibc_function_errorhandlers" ar
    mapM_ (\ (fn,arg,handler) -> addFunctionErrorHandlers fn arg [handler]) ns

processMetaVars :: Archive -> Idris ()
processMetaVars ar = do
    ns <- getEntry [] "ibc_metavars" ar
    updateIState (\i -> i { idris_metavars = L.reverse ns ++ idris_metavars i })

-- We only want the language extensions when reading the top level thing
processLangExts :: IBCPhase -> Archive -> Idris ()
processLangExts (IBC_REPL True) ar
    = do ds <- getEntry [] "ibc_langexts" ar
         mapM_ addLangExt ds
processLangExts _ _ = return ()

----- For Cheapskate and docstrings

instance Binary a => Binary (D.Docstring a)
instance Binary CT.Options
instance Binary D.DocTerm
instance Binary a => Binary (D.Block a)
instance Binary a => Binary (D.Inline a)
instance Binary CT.ListType
instance Binary CT.CodeAttr
instance Binary CT.NumWrapper

----- Generated by 'derive'

instance Binary SizeChange
instance Binary CGInfo where
        put (CGInfo x1 x2 x3 x4)
          = do put x1
--                put x3 -- Already used SCG info for totality check
               put x2
               put x4
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               return (CGInfo x1 x2 [] x3)

instance Binary CaseType
instance Binary SC
instance Binary CaseAlt
instance Binary CaseDefs
instance Binary CaseInfo
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
                -- no need to add/load original patterns, because they're not
                -- used again after totality checking
                CaseOp x1 x2 x3 _ _ x4 -> do putWord8 3
                                             put x1
                                             put x2
                                             put x3
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
--                            x4 <- get
                           -- x3 <- get always []
                           x5 <- get
                           return (CaseOp x1 x2 x3 [] [] x5)
                   _ -> error "Corrupted binary data for Def"

instance Binary Accessibility
instance Binary PReason
instance Binary Totality
instance Binary MetaInformation
instance Binary DataOpt
instance Binary FnOpt
instance Binary Fixity
instance Binary FixDecl
instance Binary ArgOpt
instance Binary Static
instance Binary Plicity where
        put x
          = case x of
                Imp x1 x2 x3 x4 _ x5 ->
                             do putWord8 0
                                put x1
                                put x2
                                put x3
                                put x4
                                put x5
                Exp x1 x2 x3 x4 ->
                             do putWord8 1
                                put x1
                                put x2
                                put x3
                                put x4
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
                           x4 <- get
                           x5 <- get
                           return (Imp x1 x2 x3 x4 False x5)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (Exp x1 x2 x3 x4)
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

instance Binary DefaultTotality
instance Binary LanguageExt
instance Binary Directive
instance (Binary t) => Binary (PDecl' t)
instance Binary t => Binary (ProvideWhat' t)
instance Binary Using
instance Binary SyntaxInfo where
        put (Syn x1 x2 x3 x4 _ _ x5 x6 x7 _ _ x8 _ _ _)
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
               return (Syn x1 x2 x3 x4 [] id x5 x6 x7 Nothing 0 x8 0 True True)

instance (Binary t) => Binary (PClause' t)
instance (Binary t) => Binary (PData' t)
instance Binary PunInfo
instance Binary PTerm
instance Binary PAltType
instance (Binary t) => Binary (PTactic' t)
instance (Binary t) => Binary (PDo' t)
instance (Binary t) => Binary (PArg' t)
instance Binary InterfaceInfo where
        put (CI x1 x2 x3 x4 x5 x6 x7 _ x8)
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
               return (CI x1 x2 x3 x4 x5 x6 x7 [] x8)

instance Binary RecordInfo
instance Binary OptInfo
instance Binary FnInfo
instance Binary TypeInfo
instance Binary SynContext
instance Binary Syntax
instance (Binary t) => Binary (DSL' t)
instance Binary SSymbol
instance Binary Codegen
instance Binary IRFormat

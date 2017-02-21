{-|
Module      : Idris.IBC
Description : Core representations and code to generate IBC files.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.IBC (loadIBC, loadPkgIndex,
                  writeIBC, writePkgIndex,
                  hasValidIBCVersion, IBCPhase(..)) where

import Idris.AbsSyntax
import Idris.Core.Binary
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.DeepSeq
import Idris.Delaborate
import Idris.Docstrings (Docstring)
import qualified Idris.Docstrings as D
import Idris.Error
import Idris.Imports
import Idris.Output
import IRTS.System (getIdrisLibDir)

import Paths_idris

import qualified Cheapskate.Types as CT
import Codec.Archive.Zip
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict hiding (get, put)
import qualified Control.Monad.State.Strict as ST
import Data.Binary
import Data.ByteString.Lazy as B hiding (elem, length, map)
import Data.Functor
import Data.List as L
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Vector.Binary
import Debug.Trace
import System.Directory
import System.FilePath

ibcVersion :: Word16
ibcVersion = 160

-- | When IBC is being loaded - we'll load different things (and omit
-- different structures/definitions) depending on which phase we're in.
data IBCPhase = IBC_Building  -- ^ when building the module tree
              | IBC_REPL Bool -- ^ when loading modules for the REPL Bool = True for top level module
  deriving (Show, Eq)

data IBCFile = IBCFile {
    ver                        :: Word16
  , sourcefile                 :: FilePath
  , ibc_reachablenames         :: ![Name]
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
  }
  deriving Show
{-!
deriving instance Binary IBCFile
!-}

initIBC :: IBCFile
initIBC = IBCFile ibcVersion "" [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] Nothing [] [] [] [] [] [] [] [] [] []

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
           = do imps <- getImported
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
                                else unhide phase archive
                            addImported reexport fp

-- | Load an entire package from its index file
loadPkgIndex :: String -> Idris ()
loadPkgIndex pkg = do ddir <- runIO getIdrisLibDir
                      addImportDir (ddir </> pkg)
                      fp <- findPkgIndex pkg
                      loadIBC True IBC_Building fp


makeEntry :: (Binary b) => String -> [b] -> Maybe Entry
makeEntry name val = if L.null val
                        then Nothing
                        else Just $ toEntry name 0 (encode val)


entries :: IBCFile -> [Entry]
entries i = catMaybes [Just $ toEntry "ver" 0 (encode $ ver i),
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
                       makeEntry "ibc_fragile" (ibc_fragile i)]
-- TODO: Put this back in shortly after minimising/pruning constraints
--                        makeEntry "ibc_constraints" (ibc_constraints i)]

writeArchive :: FilePath -> IBCFile -> Idris ()
writeArchive fp i = do let a = L.foldl (\x y -> addEntryToArchive y x) emptyArchive (entries i)
                       runIO $ B.writeFile fp (fromArchive a)

writeIBC :: FilePath -> FilePath -> Idris ()
writeIBC src f
    = do
         logIBC  1 $ "Writing IBC for: " ++ show f
         iReport 2 $ "Writing IBC for: " ++ show f
         i <- getIState
--          case (Data.List.map fst (idris_metavars i)) \\ primDefs of
--                 (_:_) -> ifail "Can't write ibc when there are unsolved metavariables"
--                 [] -> return ()
         resetNameIdx
         ibcf <- mkIBC (ibc_write i) (initIBC { sourcefile = src })
         idrisCatch (do runIO $ createDirectoryIfMissing True (dropFileName f)
                        writeArchive f ibcf
                        logIBC 1 "Written")
            (\c -> do logIBC 1 $ "Failed " ++ pshow i c)
         return ()

-- | Write a package index containing all the imports in the current
-- IState Used for ':search' of an entire package, to ensure
-- everything is loaded.
writePkgIndex :: FilePath -> Idris ()
writePkgIndex f
    = do i <- getIState
         let imps = map (\ (x, y) -> (True, x)) $ idris_imported i
         logIBC 1 $ "Writing package index " ++ show f ++ " including\n" ++
                show (map snd imps)
         resetNameIdx
         let ibcf = initIBC { ibc_imports = imps }
         idrisCatch (do runIO $ createDirectoryIfMissing True (dropFileName f)
                        writeArchive f ibcf
                        logIBC 1 "Written")
            (\c -> do logIBC 1 $ "Failed " ++ pshow i c)
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

getEntry :: (Binary b, NFData b) => b -> FilePath -> Archive -> Idris b
getEntry alt f a = case findEntryByPath f a of
                Nothing -> return alt
                Just e -> return $! (force . decode . fromEntry) e

unhide :: IBCPhase -> Archive -> Idris ()
unhide phase ar = do
    processImports True phase ar
    processAccess True phase ar

process :: Bool -- ^ Reexporting
           -> IBCPhase
           -> Archive -> FilePath -> Idris ()
process reexp phase archive fn = do
                ver <- getEntry 0 "ver" archive
                when (ver /= ibcVersion) $ do
                                    logIBC 1 "ibc out of date"
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
                processImports reexp phase archive
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
                processObjectFiles archive
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

processImports :: Bool -> IBCPhase -> Archive -> Idris ()
processImports reexp phase ar = do
    fs <- getEntry [] "ibc_imports" ar
    mapM_ (\(re, f) -> do
        i <- getIState
        ibcsd <- valIBCSubDir i
        ids <- allImportDirs
        fp <- findImport ids ibcsd f
--                        if (f `elem` imported i)
--                         then logLvl 1 $ "Already read " ++ f
        putIState (i { imported = f : imported i })
        let phase' = case phase of
                         IBC_REPL _ -> IBC_REPL False
                         p -> p
        case fp of
            LIDR fn -> do
                logIBC 1 $ "Failed at " ++ fn
                ifail "Must be an ibc"
            IDR fn -> do
                logIBC 1 $ "Failed at " ++ fn
                ifail "Must be an ibc"
            IBC fn src -> loadIBC (reexp && re) phase' fn) fs

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

processObjectFiles :: Archive -> Idris ()
processObjectFiles ar = do
    os <- getEntry [] "ibc_objs" ar
    mapM_ (\ (cg, obj) -> do
        dirs <- allImportDirs
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
        mapM_ (\ (n, d) -> do
            d' <- updateDef d
            case d' of
                TyDecl _ _ -> return ()
                _ -> do
                    logIBC 1 $ "SOLVING " ++ show n
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
                    updateB (Let t v) = liftM2 Let (update' t) (update' v)
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
    ds <- getEntry [] "ibc_access" ar
    mapM_ (\ (n, a_in) -> do
        let a = if reexp then a_in else Hidden
        logIBC 3 $ "Setting " ++ show (a, n) ++ " to " ++ show a
        updateIState (\i -> i { tt_ctxt = setAccess n a (tt_ctxt i) })

        if (not reexp)
            then do
                logIBC 1 $ "Not exporting " ++ show n
                setAccessibility n Hidden
            else logIBC 1 $ "Exporting " ++ show n
        -- Everything should be available at the REPL from
        -- things imported publicly
        when (phase == IBC_REPL True) $ setAccessibility n Public) ds

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

instance Binary D.DocTerm where
  put D.Unchecked = putWord8 0
  put (D.Checked t) = putWord8 1 >> put t
  put (D.Example t) = putWord8 2 >> put t
  put (D.Failing e) = putWord8 3 >> put e

  get = do i <- getWord8
           case i of
             0 -> return D.Unchecked
             1 -> fmap D.Checked get
             2 -> fmap D.Example get
             3 -> fmap D.Failing get
             _ -> error "Corrupted binary data for DocTerm"

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
             _ -> error "Corrupted binary data for Block"

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
             _ -> error "Corrupted binary data for Inline"

instance Binary CT.ListType where
  put (CT.Bullet c) = putWord8 0 >> put c
  put (CT.Numbered nw i) = putWord8 1 >> put nw >> put i
  get = do i <- getWord8
           case i of
             0 -> liftM CT.Bullet get
             1 -> liftM2 CT.Numbered get get
             _ -> error "Corrupted binary data for ListType"

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
             _ -> error "Corrupted binary data for NumWrapper"

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
        put (CaseDefs x1 x2)
          = do put x1
               put x2
        get
          = do x1 <- get
               x2 <- get
               return (CaseDefs x1 x2)

instance Binary CaseInfo where
        put x@(CaseInfo x1 x2 x3) = do put x1
                                       put x2
                                       put x3
        get = do x1 <- get
                 x2 <- get
                 x3 <- get
                 return (CaseInfo x1 x2 x3)

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

instance Binary Accessibility where
        put x
          = case x of
                Public -> putWord8 0
                Frozen -> putWord8 1
                Private -> putWord8 2
                Hidden -> putWord8 3
        get
          = do i <- getWord8
               case i of
                   0 -> return Public
                   1 -> return Frozen
                   2 -> return Private
                   3 -> return Hidden
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
                UseUndef x1 -> do putWord8 7
                                  put x1
                ExternalIO -> putWord8 8
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
                   7 -> do x1 <- get
                           return (UseUndef x1)
                   8 -> return ExternalIO
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
                Generated -> do putWord8 4
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Total x1)
                   1 -> do x1 <- get
                           return (Partial x1)
                   2 -> return Unchecked
                   3 -> return Productive
                   4 -> return Generated
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
             _ -> error "Corrupted binary data for MetaInformation"

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
            _ -> error "Corrupted binary data for DataOpt"

instance Binary FnOpt where
        put x
          = case x of
                Inlinable -> putWord8 0
                TotalFn -> putWord8 1
                Dictionary -> putWord8 2
                AssertTotal -> putWord8 3
                Specialise x -> do putWord8 4
                                   put x
                AllGuarded -> putWord8 5
                PartialFn -> putWord8 6
                Implicit -> putWord8 7
                Reflection -> putWord8 8
                ErrorHandler -> putWord8 9
                ErrorReverse -> putWord8 10
                CoveringFn -> putWord8 11
                NoImplicit -> putWord8 12
                Constructor -> putWord8 13
                CExport x1 -> do putWord8 14
                                 put x1
                AutoHint -> putWord8 15
                PEGenerated -> putWord8 16
                StaticFn -> putWord8 17
                OverlappingDictionary -> putWord8 18
                ErrorReduce -> putWord8 20
        get
          = do i <- getWord8
               case i of
                   0 -> return Inlinable
                   1 -> return TotalFn
                   2 -> return Dictionary
                   3 -> return AssertTotal
                   4 -> do x <- get
                           return (Specialise x)
                   5 -> return AllGuarded
                   6 -> return PartialFn
                   7 -> return Implicit
                   8 -> return Reflection
                   9 -> return ErrorHandler
                   10 -> return ErrorReverse
                   11 -> return CoveringFn
                   12 -> return NoImplicit
                   13 -> return Constructor
                   14 -> do x1 <- get
                            return $ CExport x1
                   15 -> return AutoHint
                   16 -> return PEGenerated
                   17 -> return StaticFn
                   18 -> return OverlappingDictionary
                   20 -> return ErrorReduce
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
                UnknownImp -> putWord8 3
        get
          = do i <- getWord8
               case i of
                   0 -> return HideDisplay
                   1 -> return InaccessibleArg
                   2 -> return AlwaysShow
                   3 -> return UnknownImp
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


instance (Binary t) => Binary (PDecl' t) where
        put x
          = case x of
                PFix x1 x2 x3 -> do putWord8 0
                                    put x1
                                    put x2
                                    put x3
                PTy x1 x2 x3 x4 x5 x6 x7 x8
                                   -> do putWord8 1
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                                         put x5
                                         put x6
                                         put x7
                                         put x8
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
                PNamespace x1 x2 x3 -> do putWord8 5
                                          put x1
                                          put x2
                                          put x3
                PRecord x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ->
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
                                                put x10
                                                put x11
                                                put x12
                PInterface x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
                                         -> do putWord8 7
                                               put x1
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
                PImplementation x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 ->
                  do putWord8 8
                     put x1
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
                PPostulate x1 x2 x3 x4 x5 x6 x7 x8
                                   -> do putWord8 12
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                                         put x5
                                         put x6
                                         put x7
                                         put x8
                PSyntax x1 x2 -> do putWord8 13
                                    put x1
                                    put x2
                PDirective x1 -> error "Cannot serialize PDirective"
                PProvider x1 x2 x3 x4 x5 x6 ->
                  do putWord8 15
                     put x1
                     put x2
                     put x3
                     put x4
                     put x5
                     put x6
                PTransform x1 x2 x3 x4 -> do putWord8 16
                                             put x1
                                             put x2
                                             put x3
                                             put x4
                PRunElabDecl x1 x2 x3 -> do putWord8 17
                                            put x1
                                            put x2
                                            put x3
                POpenInterfaces x1 x2 x3 -> do putWord8 18
                                               put x1
                                               put x2
                                               put x3
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
                           x8 <- get
                           return (PTy x1 x2 x3 x4 x5 x6 x7 x8)
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
                           x3 <- get
                           return (PNamespace x1 x2 x3)
                   6 -> do x1 <- get
                           x2 <- get
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
                           return (PRecord x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
                   7 -> do x1 <- get
                           x2 <- get
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
                           return (PInterface x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
                   8 -> do x1 <- get
                           x2 <- get
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
                           return (PImplementation x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
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
                            x7 <- get
                            x8 <- get
                            return (PPostulate x1 x2 x3 x4 x5 x6 x7 x8)
                   13 -> do x1 <- get
                            x2 <- get
                            return (PSyntax x1 x2)
                   14 -> do error "Cannot deserialize PDirective"
                   15 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            x5 <- get
                            x6 <- get
                            return (PProvider x1 x2 x3 x4 x5 x6)
                   16 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            return (PTransform x1 x2 x3 x4)
                   17 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PRunElabDecl x1 x2 x3)
                   18 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (POpenInterfaces x1 x2 x3)
                   _ -> error "Corrupted binary data for PDecl'"

instance Binary t => Binary (ProvideWhat' t) where
  put (ProvTerm x1 x2) = do putWord8 0
                            put x1
                            put x2
  put (ProvPostulate x1) = do putWord8 1
                              put x1
  get = do y <- getWord8
           case y of
             0 -> do x1 <- get
                     x2 <- get
                     return (ProvTerm x1 x2)
             1 -> do x1 <- get
                     return (ProvPostulate x1)
             _ -> error "Corrupted binary data for ProvideWhat"

instance Binary Using where
        put (UImplicit x1 x2) = do putWord8 0; put x1; put x2
        put (UConstraint x1 x2) = do putWord8 1; put x1; put x2

        get = do i <- getWord8
                 case i of
                    0 -> do x1 <- get; x2 <- get; return (UImplicit x1 x2)
                    1 -> do x1 <- get; x2 <- get; return (UConstraint x1 x2)
                    _ -> error "Corrupted binary data for Using"

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
                PWith x1 x2 x3 x4 x5 x6 x7 -> do putWord8 1
                                                 put x1
                                                 put x2
                                                 put x3
                                                 put x4
                                                 put x5
                                                 put x6
                                                 put x7
                PClauseR x1 x2 x3 x4 -> do putWord8 2
                                           put x1
                                           put x2
                                           put x3
                                           put x4
                PWithR x1 x2 x3 x4 x5 -> do putWord8 3
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
                           x6 <- get
                           return (PClause x1 x2 x3 x4 x5 x6)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           x7 <- get
                           return (PWith x1 x2 x3 x4 x5 x6 x7)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PClauseR x1 x2 x3 x4)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           return (PWithR x1 x2 x3 x4 x5)
                   _ -> error "Corrupted binary data for PClause'"

instance (Binary t) => Binary (PData' t) where
        put x
          = case x of
                PDatadecl x1 x2 x3 x4 -> do putWord8 0
                                            put x1
                                            put x2
                                            put x3
                                            put x4
                PLaterdecl x1 x2 x3 -> do putWord8 1
                                          put x1
                                          put x2
                                          put x3
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PDatadecl x1 x2 x3 x4)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PLaterdecl x1 x2 x3)
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
                 _ -> error "Corrupted binary data for PunInfo"

instance Binary PTerm where
        put x
          = case x of
                PQuote x1 -> do putWord8 0
                                put x1
                PRef x1 x2 x3 -> do putWord8 1
                                    put x1
                                    put x2
                                    put x3
                PInferRef x1 x2 x3 -> do putWord8 2
                                         put x1
                                         put x2
                                         put x3
                PPatvar x1 x2 -> do putWord8 3
                                    put x1
                                    put x2
                PLam x1 x2 x3 x4 x5 -> do putWord8 4
                                          put x1
                                          put x2
                                          put x3
                                          put x4
                                          put x5
                PPi x1 x2 x3 x4 x5 -> do putWord8 5
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                                         put x5
                PLet x1 x2 x3 x4 x5 x6 -> do putWord8 6
                                             put x1
                                             put x2
                                             put x3
                                             put x4
                                             put x5
                                             put x6
                PTyped x1 x2 -> do putWord8 7
                                   put x1
                                   put x2
                PAppImpl x1 x2 -> error "PAppImpl in final term"
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
                PResolveTC x1 -> do putWord8 15
                                    put x1
                PRewrite x1 x2 x3 x4 x5 -> do putWord8 17
                                              put x1
                                              put x2
                                              put x3
                                              put x4
                                              put x5
                PPair x1 x2 x3 x4 x5 -> do putWord8 18
                                           put x1
                                           put x2
                                           put x3
                                           put x4
                                           put x5
                PDPair x1 x2 x3 x4 x5 x6 -> do putWord8 19
                                               put x1
                                               put x2
                                               put x3
                                               put x4
                                               put x5
                                               put x6
                PAlternative x1 x2 x3 -> do putWord8 20
                                            put x1
                                            put x2
                                            put x3
                PHidden x1 -> do putWord8 21
                                 put x1
                PType x1 -> do putWord8 22
                               put x1
                PGoal x1 x2 x3 x4 -> do putWord8 23
                                        put x1
                                        put x2
                                        put x3
                                        put x4
                PConstant x1 x2 -> do putWord8 24
                                      put x1
                                      put x2
                Placeholder -> putWord8 25
                PDoBlock x1 -> do putWord8 26
                                  put x1
                PIdiom x1 x2 -> do putWord8 27
                                   put x1
                                   put x2
                PMetavar x1 x2 -> do putWord8 29
                                     put x1
                                     put x2
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
                PUniverse x1 x2 -> do putWord8 38
                                      put x1
                                      put x2
                PRunElab x1 x2 x3 -> do putWord8 39
                                        put x1
                                        put x2
                                        put x3
                PAs x1 x2 x3 -> do putWord8 40
                                   put x1
                                   put x2
                                   put x3
                PElabError x1 -> do putWord8 41
                                    put x1
                PQuasiquote x1 x2 -> do putWord8 42
                                        put x1
                                        put x2
                PUnquote x1 -> do putWord8 43
                                  put x1
                PQuoteName x1 x2 x3 -> do putWord8 44
                                          put x1
                                          put x2
                                          put x3
                PIfThenElse x1 x2 x3 x4 -> do putWord8 45
                                              put x1
                                              put x2
                                              put x3
                                              put x4
                PConstSugar x1 x2 -> do putWord8 46
                                        put x1
                                        put x2
                PWithApp x1 x2 x3 -> do putWord8 47
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
                           x3 <- get
                           return (PRef x1 x2 x3)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PInferRef x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           return (PPatvar x1 x2)
                   4 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           return (PLam x1 x2 x3 x4 x5)
                   5 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           return (PPi x1 x2 x3 x4 x5)
                   6 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           x6 <- get
                           return (PLet x1 x2 x3 x4 x5 x6)
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
                   15 -> do x1 <- get
                            return (PResolveTC x1)
                   17 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            x5 <- get
                            return (PRewrite x1 x2 x3 x4 x5)
                   18 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            x5 <- get
                            return (PPair x1 x2 x3 x4 x5)
                   19 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            x5 <- get
                            x6 <- get
                            return (PDPair x1 x2 x3 x4 x5 x6)
                   20 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PAlternative x1 x2 x3)
                   21 -> do x1 <- get
                            return (PHidden x1)
                   22 -> do x1 <- get
                            return (PType x1)
                   23 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            return (PGoal x1 x2 x3 x4)
                   24 -> do x1 <- get
                            x2 <- get
                            return (PConstant x1 x2)
                   25 -> return Placeholder
                   26 -> do x1 <- get
                            return (PDoBlock x1)
                   27 -> do x1 <- get
                            x2 <- get
                            return (PIdiom x1 x2)
                   29 -> do x1 <- get
                            x2 <- get
                            return (PMetavar x1 x2)
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
                            x2 <- get
                            return (PUniverse x1 x2)
                   39 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PRunElab x1 x2 x3)
                   40 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PAs x1 x2 x3)
                   41 -> do x1 <- get
                            return (PElabError x1)
                   42 -> do x1 <- get
                            x2 <- get
                            return (PQuasiquote x1 x2)
                   43 -> do x1 <- get
                            return (PUnquote x1)
                   44 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PQuoteName x1 x2 x3)
                   45 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            return (PIfThenElse x1 x2 x3 x4)
                   46 -> do x1 <- get
                            x2 <- get
                            return (PConstSugar x1 x2)
                   47 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PWithApp x1 x2 x3)
                   _ -> error "Corrupted binary data for PTerm"

instance Binary PAltType where
        put x
          = case x of
                ExactlyOne x1 -> do putWord8 0
                                    put x1
                FirstSuccess -> putWord8 1
                TryImplicit -> putWord8 2
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (ExactlyOne x1)
                   1 -> return FirstSuccess
                   2 -> return TryImplicit
                   _ -> error "Corrupted binary data for PAltType"


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
                ProofSearch x1 x2 x3 x4 x5 x6 -> do putWord8 21
                                                    put x1
                                                    put x2
                                                    put x3
                                                    put x4
                                                    put x5
                                                    put x6
                DoUnify -> putWord8 22
                CaseTac x1 -> do putWord8 23
                                 put x1
                SourceFC -> putWord8 24
                Intros -> putWord8 25
                Equiv x1 -> do putWord8 26
                               put x1
                Claim x1 x2 -> do putWord8 27
                                  put x1
                                  put x2
                Unfocus -> putWord8 28
                MatchRefine x1 -> do putWord8 29
                                     put x1
                LetTacTy x1 x2 x3 -> do putWord8 30
                                        put x1
                                        put x2
                                        put x3
                TCImplementation -> putWord8 31
                GoalType x1 x2 -> do putWord8 32
                                     put x1
                                     put x2
                TCheck x1 -> do putWord8 33
                                put x1
                TEval x1 -> do putWord8 34
                               put x1
                TDocStr x1 -> do putWord8 35
                                 put x1
                TSearch x1 -> do putWord8 36
                                 put x1
                Skip -> putWord8 37
                TFail x1 -> do putWord8 38
                               put x1
                Abandon -> putWord8 39
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
                            x6 <- get
                            return (ProofSearch x1 x2 x3 x4 x5 x6)
                   22 -> return DoUnify
                   23 -> do x1 <- get
                            return (CaseTac x1)
                   24 -> return SourceFC
                   25 -> return Intros
                   26 -> do x1 <- get
                            return (Equiv x1)
                   27 -> do x1 <- get
                            x2 <- get
                            return (Claim x1 x2)
                   28 -> return Unfocus
                   29 -> do x1 <- get
                            return (MatchRefine x1)
                   30 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (LetTacTy x1 x2 x3)
                   31 -> return TCImplementation
                   32 -> do x1 <- get
                            x2 <- get
                            return (GoalType x1 x2)
                   33 -> do x1 <- get
                            return (TCheck x1)
                   34 -> do x1 <- get
                            return (TEval x1)
                   35 -> do x1 <- get
                            return (TDocStr x1)
                   36 -> do x1 <- get
                            return (TSearch x1)
                   37 -> return Skip
                   38 -> do x1 <- get
                            return (TFail x1)
                   39 -> return Abandon
                   _ -> error "Corrupted binary data for PTactic'"


instance (Binary t) => Binary (PDo' t) where
        put x
          = case x of
                DoExp x1 x2 -> do putWord8 0
                                  put x1
                                  put x2
                DoBind x1 x2 x3 x4 -> do putWord8 1
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                DoBindP x1 x2 x3 x4 -> do putWord8 2
                                          put x1
                                          put x2
                                          put x3
                                          put x4
                DoLet x1 x2 x3 x4 x5 -> do putWord8 3
                                           put x1
                                           put x2
                                           put x3
                                           put x4
                                           put x5
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
                           x4 <- get
                           return (DoBind x1 x2 x3 x4)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (DoBindP x1 x2 x3 x4)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           return (DoLet x1 x2 x3 x4 x5)
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

instance Binary RecordInfo where
        put (RI x1 x2 x3)
          = do put x1
               put x2
               put x3
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               return (RI x1 x2 x3)

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

instance Binary FnInfo where
        put (FnInfo x1)
          = put x1
        get
          = do x1 <- get
               return (FnInfo x1)

instance Binary TypeInfo where
        put (TI x1 x2 x3 x4 x5 x6) = do put x1
                                        put x2
                                        put x3
                                        put x4
                                        put x5
                                        put x6
        get = do x1 <- get
                 x2 <- get
                 x3 <- get
                 x4 <- get
                 x5 <- get
                 x6 <- get
                 return (TI x1 x2 x3 x4 x5 x6)

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
          = do putWord8 0
               put x1
               put x2
               put x3
        put (DeclRule x1 x2)
          = do putWord8 1
               put x1
               put x2
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Rule x1 x2 x3)
                   1 -> do x1 <- get
                           x2 <- get
                           return (DeclRule x1 x2)
                   _ -> error "Corrupted binary data for Syntax"

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

instance Binary Codegen where
        put x
          = case x of
                Via ir str -> do putWord8 0
                                 put ir
                                 put str
                Bytecode -> putWord8 1
        get
          = do i <- getWord8
               case i of
                  0 -> do x1 <- get
                          x2 <- get
                          return (Via x1 x2)
                  1 -> return Bytecode
                  _ -> error  "Corrupted binary data for Codegen"

instance Binary IRFormat where
    put x = case x of
                IBCFormat -> putWord8 0
                JSONFormat -> putWord8 1
    get = do i <- getWord8
             case i of
                0 -> return IBCFormat
                1 -> return JSONFormat
                _ -> error  "Corrupted binary data for IRFormat"

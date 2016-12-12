{-# LANGUAGE CPP #-}

import Control.Monad
import Data.IORef
import Control.Exception (SomeException, catch)

import Distribution.Simple
import Distribution.Simple.BuildPaths (autogenModulesDir)
import Distribution.Simple.InstallDirs as I
import Distribution.Simple.LocalBuildInfo as L
import qualified Distribution.Simple.Setup as S
import qualified Distribution.Simple.Program as P
import Distribution.Simple.Utils (createDirectoryIfMissingVerbose, rewriteFile, notice, installOrdinaryFiles)
import Distribution.Compiler
import Distribution.PackageDescription
import Distribution.Text

import System.Environment
import System.Exit
import System.FilePath ((</>), splitDirectories,isAbsolute)
import System.Directory
import qualified System.FilePath.Posix as Px
import System.Process

-- After Idris is built, we need to check and install the prelude and other libs

-- -----------------------------------------------------------------------------
-- Idris Command Path

-- make on mingw32 exepects unix style separators
#ifdef mingw32_HOST_OS
(<//>) = (Px.</>)
idrisCmd local = Px.joinPath $ splitDirectories $ ".." <//> ".." <//> buildDir local <//> "idris" <//> "idris"
#else
idrisCmd local = ".." </> ".." </>  buildDir local </>  "idris" </>  "idris"
#endif

-- -----------------------------------------------------------------------------
-- Make Commands

-- use GNU make on FreeBSD
#if defined(freebsd_HOST_OS) || defined(dragonfly_HOST_OS)\
    || defined(openbsd_HOST_OS) || defined(netbsd_HOST_OS)
mymake = "gmake"
#else
mymake = "make"
#endif
make verbosity =
   P.runProgramInvocation verbosity . P.simpleProgramInvocation mymake

#ifdef mingw32_HOST_OS
windres verbosity = P.runProgramInvocation verbosity . P.simpleProgramInvocation "windres"
#endif

-- -----------------------------------------------------------------------------
-- Flags

execOnly :: S.ConfigFlags -> Bool
execOnly flags =
  case lookup (FlagName "execonly") (S.configConfigurationsFlags flags) of
    Just True -> True
    Just False -> False
    Nothing -> False

isFreestanding :: S.ConfigFlags -> Bool
isFreestanding flags =
  case lookup (FlagName "freestanding") (S.configConfigurationsFlags flags) of
    Just True -> True
    Just False -> False
    Nothing -> False

flagDef :: String -> FlagAssignment -> Bool
flagDef flag flags =
  case lookup (FlagName flag) flags of
    Just True  -> True
    Just False -> False
    Nothing    -> False

-- -----------------------------------------------------------------------------
-- Clean

idrisClean _ flags _ _ = cleanStdLib
   where
      verbosity = S.fromFlag $ S.cleanVerbosity flags

      cleanStdLib = makeClean "libs"

      makeClean dir = make verbosity [ "-C", dir, "clean", "IDRIS=idris" ]

-- -----------------------------------------------------------------------------
-- Configure

-- Generate a module that contains the lib path for a freestanding Idris
generateTargetModule verbosity dir targetDir = do
    let absPath = isAbsolute targetDir
    let targetModulePath = dir </> "Target_idris" Px.<.> "hs"
    putStrLn $ "Generating " ++ targetModulePath
    createDirectoryIfMissingVerbose verbosity True dir
    rewriteFile targetModulePath (versionModuleContents absPath targetDir)
            where versionModuleContents absolute td = "module Target_idris where\n\n" ++
                                    "import System.FilePath\n" ++
                                    "import System.Environment\n" ++
                                    "getDataDir :: IO String\n" ++
                                    if absolute
                                        then "getDataDir = return \"" ++ td ++ "\"\n"
                                        else "getDataDir = do \n" ++
                                             "   expath <- getExecutablePath\n" ++
                                             "   execDir <- return $ dropFileName expath\n" ++
                                             "   return $ execDir ++ \"" ++ td ++ "\"\n"

-- a module that has info about existence and location of a bundled toolchain
generateToolchainModule verbosity srcDir toolDir = do
    let commonContent = "module Tools_idris where\n\n"
    let toolContent = case toolDir of
                        Just dir -> "hasBundledToolchain = True\n" ++
                                    "getToolchainDir = \"" ++ dir ++ "\"\n"
                        Nothing -> "hasBundledToolchain = False\n" ++
                                   "getToolchainDir = \"\""
    let toolPath = srcDir </> "Tools_idris" Px.<.> "hs"
    createDirectoryIfMissingVerbose verbosity True srcDir
    rewriteFile toolPath (commonContent ++ toolContent)

-- Generates a module that initializes the IRTS.System environment (paths, flags, etc)
-- and registers all 3rd party bundled packages (codegens, etc).
-- initIdrisEnvironment should be called once, somewhere close to the start of main.
generateEnvironmentModule verbosity srcDir fs = do
  let header = "module Environment_idris where\n\n"
            ++ "import qualified IRTS.System as S\n"
            ++ "import System.FilePath ((</>))\n\n"
            ++ if flagDef "freestanding" fs
               then "import Paths_idris (version)\n\n"
                 ++ "import Target_idris\n"
               else "import Paths_idris\n\n"
  let regfn = "\ninitIdrisEnvironment = do\n"
           ++ "  dir <- getDataDir\n"
           ++ "  let libs     = dir </> \"libs\"\n"
           ++ "  let docs     = dir </> \"docs\"\n"
           ++ "  let idrisdoc = dir </> \"idrisdoc\"\n"
           ++ "  S.registerDataPaths libs docs idrisdoc\n"
  let plugins = []
        ++ (if flagDef "codegen_c" fs
            then [("IRTS.CodegenC", "register")] else [])
        ++ (if flagDef "codegen_javascript" fs
            then [("IRTS.CodegenJavaScript", "register")] else [])
  let imps = fst . foldl (\(acc, n) s ->
                    (acc ++ "import qualified " ++ s ++ " as P" ++ show n ++ "\n", n + 1))
                    ("", 1)
           . map fst $ plugins
  let regs = fst . foldl (\(acc, n) s ->
                    (acc ++ "  P" ++ show n ++ "." ++ s ++ "\n", n + 1))
                    ("", 1)
           . map snd $ plugins
#if defined(freebsd_HOST_OS) || defined(dragonfly_HOST_OS)\
    || defined(openbsd_HOST_OS) || defined(netbsd_HOST_OS)
  let flags = "  S.registerLibFlag \"-L/usr/local/lib\" 90\n"
           ++ "  S.registerIncFlag \"-I/usr/local/include\" 90\n"
#else
  let flags = ""
#endif
  createDirectoryIfMissingVerbose verbosity True srcDir
  let path = srcDir </> "Environment_idris" Px.<.> "hs"
  rewriteFile path $ header ++ imps ++ regfn ++ flags ++ regs

idrisConfigure _ flags _ local = do
    generateEnvironmentModule verbosity (autogenModulesDir local)
                                        (S.configConfigurationsFlags $ configFlags local)
    if isFreestanding $ configFlags local
        then do
                toolDir <- lookupEnv "IDRIS_TOOLCHAIN_DIR"
                generateToolchainModule verbosity (autogenModulesDir local) toolDir
                targetDir <- lookupEnv "IDRIS_LIB_DIR"
                case targetDir of
                     Just d -> generateTargetModule verbosity (autogenModulesDir local) d
                     Nothing -> error $ "Trying to build freestanding without a target directory."
                                  ++ " Set it by defining IDRIS_LIB_DIR."
        else
                generateToolchainModule verbosity (autogenModulesDir local) Nothing
    where
      verbosity = S.fromFlag $ S.configVerbosity flags

idrisPreSDist args flags = do
  let dir = S.fromFlag (S.sDistDirectory flags)
  let verb = S.fromFlag (S.sDistVerbosity flags)
  generateTargetModule verb "src" "./libs"
  generateToolchainModule verb "src" Nothing
  preSDist simpleUserHooks args flags

idrisSDist sdist pkgDesc bi hooks flags = do
  pkgDesc' <- addGitFiles pkgDesc
  sdist pkgDesc' bi hooks flags
    where
      addGitFiles :: PackageDescription -> IO PackageDescription
      addGitFiles pkgDesc = do
        files <- gitFiles
        return $ pkgDesc { extraSrcFiles = extraSrcFiles pkgDesc ++ files}
      gitFiles :: IO [FilePath]
      gitFiles = liftM lines (readProcess "git" ["ls-files"] "")

idrisPostSDist args flags desc lbi = do
  Control.Exception.catch (do let targetFile = "src" </> "Target_idris" Px.<.> "hs"
                              putStrLn $ "Removing generated modules:\n "
                                        ++ targetFile
                              removeFile targetFile)
             (\e -> let e' = (e :: SomeException) in return ())
  postSDist simpleUserHooks args flags desc lbi

-- -----------------------------------------------------------------------------
-- Build

{-getVersion :: Args -> S.BuildFlags -> IO HookedBuildInfo
getVersion args flags = do
      hash <- gitHash
      let buildinfo = (emptyBuildInfo { cppOptions = ["-DVERSION="++hash] }) :: BuildInfo
      return (Just buildinfo, [])
-}

idrisPreBuild args flags = do
#ifdef mingw32_HOST_OS
        createDirectoryIfMissingVerbose verbosity True dir
        windres verbosity ["icons/idris_icon.rc","-o", dir++"/idris_icon.o"]
        return (Nothing, [("idris", emptyBuildInfo { ldOptions = [dir ++ "/idris_icon.o"] })])
     where
        verbosity = S.fromFlag $ S.buildVerbosity flags
        dir = S.fromFlagOrDefault "dist" $ S.buildDistPref flags
#else
        return (Nothing, [])
#endif

idrisBuild _ flags _ local = do
     unless (execOnly (configFlags local)) buildStdLib
   where
      verbosity = S.fromFlag $ S.buildVerbosity flags

      buildStdLib = do
            putStrLn "Building libraries..."
            makeBuild "libs"
         where
            makeBuild dir = make verbosity [ "-C", dir, "build" , "IDRIS=" ++ idrisCmd local]

-- -----------------------------------------------------------------------------
-- Copy/Install

idrisInstall verbosity copy pkg local = unless (execOnly (configFlags local)) $ do
      installStdLib
      installManPage
   where
      target = datadir $ L.absoluteInstallDirs pkg local copy

      installStdLib = do
        let target' = target -- </> "libs"
        putStrLn $ "Installing libraries in " ++ target'
        makeInstall "libs" target'

      installManPage = do
         let mandest = mandir (L.absoluteInstallDirs pkg local copy) ++ "/man1"
         notice verbosity $ unwords ["Copying man page to", mandest]
         installOrdinaryFiles verbosity mandest [("man", "idris.1")]

      makeInstall src target =
         make verbosity [ "-C", src, "install" , "TARGET=" ++ target, "IDRIS=" ++ idrisCmd local]

-- -----------------------------------------------------------------------------
-- Test

-- FIXME: We use the __GLASGOW_HASKELL__ macro because MIN_VERSION_cabal seems
-- to be broken !

-- There are two "dataDir" in cabal, and they don't relate to each other.
-- When fetching modules, idris uses the second path (in the pkg record),
-- which by default is the root folder of the project.
-- We want it to be the install directory where we put the idris libraries.
fixPkg pkg target = pkg { dataDir = target }

-- The "Args" argument of the testHooks has been added in cabal 1.22.0,
-- and should therefore be ignored for prior versions.
#if __GLASGOW_HASKELL__ < 710
originalTestHook _ = testHook simpleUserHooks
#else
originalTestHook = testHook simpleUserHooks
#endif

idrisTestHook args pkg local hooks flags = do
  let target = datadir $ L.absoluteInstallDirs pkg local NoCopyDest
  originalTestHook args (fixPkg pkg target) local hooks flags

-- -----------------------------------------------------------------------------
-- Main

-- Install libraries during both copy and install
-- See https://github.com/haskell/cabal/issues/709
main = defaultMainWithHooks $ simpleUserHooks
   { postClean = idrisClean
   , postConf  = idrisConfigure
   , preBuild = idrisPreBuild
   , postBuild = idrisBuild
   , postCopy = \_ flags pkg local ->
                  idrisInstall (S.fromFlag $ S.copyVerbosity flags)
                               (S.fromFlag $ S.copyDest flags) pkg local
   , postInst = \_ flags pkg local ->
                  idrisInstall (S.fromFlag $ S.installVerbosity flags)
                               NoCopyDest pkg local
   , preSDist = idrisPreSDist
   , sDistHook = idrisSDist (sDistHook simpleUserHooks)
   , postSDist = idrisPostSDist
#if __GLASGOW_HASKELL__ < 710
   , testHook = idrisTestHook ()
#else
   , testHook = idrisTestHook
#endif
   }

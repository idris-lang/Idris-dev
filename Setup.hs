{-# LANGUAGE CPP #-}

#if !defined(MIN_VERSION_Cabal)
# define MIN_VERSION_Cabal(x,y,z) 0
#endif

import Control.Monad
import Data.IORef
import Data.Maybe (fromMaybe)
import Data.List (nub, isInfixOf)
import Control.Exception (SomeException, catch)

import Distribution.Simple
import Distribution.Simple.BuildPaths
import Distribution.Simple.InstallDirs as I
import Distribution.Simple.LocalBuildInfo as L
import qualified Distribution.Simple.Setup as S
import qualified Distribution.Simple.Program as P
import Distribution.Simple.Utils
import Distribution.Compiler
import Distribution.PackageDescription
import Distribution.Text
import Distribution.Verbosity

import System.Environment
import System.Exit
import System.FilePath ((</>), splitDirectories,isAbsolute)
import System.Directory
import qualified System.FilePath.Posix as Px
import System.Process

#if (MIN_VERSION_Cabal(2,0,0))
import Distribution.Types.UnqualComponentName
#endif


-- After Idris is built, we need to check and install the prelude and other libs

-- -----------------------------------------------------------------------------
-- Idris Command Path
idrisCmd local = Px.joinPath $ splitDirectories $ ".." </> ".." </> buildDir local </> "idris" </> "idris"


shinvoke verbosity cmd = P.runProgramInvocation verbosity . P.simpleProgramInvocation cmd


-- -----------------------------------------------------------------------------
-- Make Commands

-- use GNU make on FreeBSD
#if defined(freebsd_HOST_OS) || defined(dragonfly_HOST_OS)\
    || defined(openbsd_HOST_OS) || defined(netbsd_HOST_OS)
mymake = "gmake"
#else
mymake = "make"
#endif
make verbosity = shinvoke verbosity mymake

#ifdef mingw32_HOST_OS
windres verbosity = P.runProgramInvocation verbosity . P.simpleProgramInvocation "windres"
#endif
-- -----------------------------------------------------------------------------
-- Flags


flag nm flags = case lookupFlagAssignment (mkFlagName nm) (S.configConfigurationsFlags flags) of
    Just True -> True
    Just False -> False
    Nothing -> False


usesGMP :: S.ConfigFlags -> Bool
usesGMP = flag "gmp"

execOnly :: S.ConfigFlags -> Bool
execOnly = flag "execonly"

isRelease :: S.ConfigFlags -> Bool
isRelease = flag "release"

isFreestanding :: S.ConfigFlags -> Bool
isFreestanding = flag "freestanding"

#if !(MIN_VERSION_Cabal(2,0,0))
mkFlagName :: String -> FlagName
mkFlagName = FlagName

unUnqualComponentName = id
#endif

#if !(MIN_VERSION_Cabal(2,2,0))
lookupFlagAssignment :: FlagName -> FlagAssignment -> Maybe Bool
lookupFlagAssignment = lookup
#endif


-- -----------------------------------------------------------------------------
-- Clean

idrisClean _ flags _ _ = cleanStdLib >> cleanRts
   where
      verbosity = S.fromFlag $ S.cleanVerbosity flags

      cleanStdLib = make verbosity ["lib_clean"]
      cleanRts = make verbosity ["rts_clean"]

-- -----------------------------------------------------------------------------
-- Configure

gitHash :: IO String
gitHash = do h <- Control.Exception.catch (readProcess "git" ["rev-parse", "--short", "HEAD"] "")
                  (\e -> let e' = (e :: SomeException) in return "PRE")
             return $ takeWhile (/= '\n') h

-- Generate a module that contains extra library directories passed
-- via command-line to cabal
generateBuildFlagsModule :: Verbosity -> FilePath -> [String] -> IO ()
generateBuildFlagsModule verbosity dir libdirs = do
    let buildFlagsModulePath = dir </> "BuildFlags_idris" Px.<.> "hs"
    putStrLn $ "Generating " ++ buildFlagsModulePath
    createDirectoryIfMissingVerbose verbosity True dir
    rewriteFileEx verbosity buildFlagsModulePath contents
  where contents = "module BuildFlags_idris where \n\n" ++
                   "extraLibDirs :: [String]\n" ++
                   "extraLibDirs = " ++ show libdirs

-- Put the Git hash into a module for use in the program
-- For release builds, just put the empty string in the module
generateVersionModule verbosity dir release = do
    hash <- gitHash
    let versionModulePath = dir </> "Version_idris" Px.<.> "hs"
    putStrLn $ "Generating " ++ versionModulePath ++
             if release then " for release" else " for prerelease " ++ hash
    createDirectoryIfMissingVerbose verbosity True dir
    rewriteFileEx verbosity versionModulePath (versionModuleContents hash)

  where versionModuleContents h = "module Version_idris where\n\n" ++
                                  "gitHash :: String\n" ++
                                  if release
                                    then "gitHash = \"\"\n"
                                    else "gitHash = \"git:" ++ h ++ "\"\n"

-- Generate a module that contains the lib path for a freestanding Idris
generateTargetModule verbosity dir targetDir = do
    let absPath = isAbsolute targetDir
    let targetModulePath = dir </> "Target_idris" Px.<.> "hs"
    putStrLn $ "Generating " ++ targetModulePath
    createDirectoryIfMissingVerbose verbosity True dir
    rewriteFileEx verbosity targetModulePath (versionModuleContents absPath targetDir)
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
                                    ++ "getDataFileName :: FilePath -> IO FilePath\n"
                                    ++ "getDataFileName name = do\n"
                                    ++ "   dir <- getDataDir\n"
                                    ++ "   return (dir ++ \"/\" ++ name)"

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
    rewriteFileEx verbosity toolPath (commonContent ++ toolContent)

idrisPostConf _ flags pkgdesc local = do
    nixLDFLAGS <- lookupEnv "NIX_LDFLAGS"
    configureRTS
    withLibLBI pkgdesc local $ \lib libcfg -> do
      let libAutogenDir = autogenComponentModulesDir local libcfg
      let libDirs = extraLibDirs $ libBuildInfo lib
      let nixLibDirs = map (drop 2)
            $ filter ("-gmp-" `Data.List.isInfixOf`)
            $ words $ fromMaybe "" nixLDFLAGS
      generateBuildFlagsModule verbosity libAutogenDir (nub $ libDirs ++ nixLibDirs)
      generateVersionModule verbosity libAutogenDir (isRelease (configFlags local))
      if isFreestanding $ configFlags local
          then do
                  toolDir <- lookupEnv "IDRIS_TOOLCHAIN_DIR"
                  generateToolchainModule verbosity libAutogenDir toolDir
                  targetDir <- lookupEnv "IDRIS_LIB_DIR"
                  case targetDir of
                       Just d -> generateTargetModule verbosity libAutogenDir d
                       Nothing -> error $ "Trying to build freestanding without a target directory."
                                    ++ " Set it by defining IDRIS_LIB_DIR."
          else
                  generateToolchainModule verbosity libAutogenDir Nothing
    where
      verbosity = S.fromFlag $ S.configVerbosity flags
      version   = pkgVersion . package $ localPkgDescr local

      -- This is a hack. I don't know how to tell cabal that a data file needs
      -- installing but shouldn't be in the distribution. And it won't make the
      -- distribution if it's not there, so instead I just delete
      -- the file after configure.
      configureRTS = make verbosity ["rts_clean"]

#if !(MIN_VERSION_Cabal(2,0,0))
      autogenComponentModulesDir lbi _ = autogenModulesDir lbi
#endif

idrisPreSDist args flags = do
  let dir = S.fromFlag (S.sDistDirectory flags)
  let verb = S.fromFlag (S.sDistVerbosity flags)
  generateVersionModule verb "src" True
  generateBuildFlagsModule verb "src" []
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
  Control.Exception.catch (do let file = "src" </> "Version_idris" Px.<.> "hs"
                              let targetFile = "src" </> "Target_idris" Px.<.> "hs"
                              putStrLn $ "Removing generated modules:\n "
                                        ++ file ++ "\n" ++ targetFile
                              removeFile file
                              removeFile targetFile)
             (\e -> let e' = (e :: SomeException) in return ())
  postSDist simpleUserHooks args flags desc lbi

#if !(MIN_VERSION_Cabal(2,0,0))
rewriteFileEx :: Verbosity -> FilePath -> String -> IO ()
rewriteFileEx _ = rewriteFile
#endif

-- -----------------------------------------------------------------------------
-- Build

getVersion :: Args -> S.BuildFlags -> IO HookedBuildInfo
getVersion args flags = do
      hash <- gitHash
      let buildinfo = (emptyBuildInfo { cppOptions = ["-DVERSION="++hash] }) :: BuildInfo
      return (Just buildinfo, [])


#if !(MIN_VERSION_Cabal(2,0,0))
mkUnqualComponentName = id
#endif

idrisPreBuild args flags = do
#ifdef mingw32_HOST_OS
        createDirectoryIfMissingVerbose verbosity True dir
        windres verbosity ["icons/idris_icon.rc","-o", dir++"/idris_icon.o"]
        return (Nothing, [(mkUnqualComponentName "idris", emptyBuildInfo { ldOptions = [dir ++ "/idris_icon.o"] })])
     where
        verbosity = S.fromFlag $ S.buildVerbosity flags
        dir = S.fromFlagOrDefault "dist" $ S.buildDistPref flags
#else
        preBuild simpleUserHooks args flags
#endif

idrisBuildHook pd lbi hooks flags = do
   let exe = ("exe:" ++) . unUnqualComponentName . exeName
       exes = map exe (executables pd)
       nflags = case S.buildArgs flags of
         orig@["regression-and-feature-tests"] ->
           flags { S.buildArgs = exes ++ orig }
         _ -> flags
   buildHook simpleUserHooks pd lbi hooks nflags


idrisPostBuild _ flags _ local
   = if (execOnly (configFlags local)) then buildRTS
        else do buildStdLib
                buildRTS
   where
      verbosity = S.fromFlag $ S.buildVerbosity flags
      buildStdLib = do
        putStrLn "Building libraries..."
        make verbosity [ "-j8", "lib", "IDRIS=" ++ idrisCmd local]
      buildRTS = do
        putStrLn "Building runtime..."
        make verbosity $ ["rts"] ++ gmp
      gmpflag False = []
      gmpflag True = ["GMP=-DIDRIS_GMP"]
      gmp = gmpflag (usesGMP (configFlags local))

-- -----------------------------------------------------------------------------
-- Copy/Install

idrisInstall verbosity copy pkg local
   = if (execOnly (configFlags local)) then installRTS
        else do installStdLib
                installRTS
                installManPage
   where
      target = datadir $ L.absoluteInstallDirs pkg local copy

      installStdLib = do
         let target' = target -- </> "libs"
         putStrLn $ "Installing libraries in " ++ target'
         make' "lib_install" target'

      installRTS = do
         let target' = target </> "rts"
         putStrLn $ "Installing run time system in " ++ target'
         make' "rts_install" target'

      installManPage = do
         let mandest = mandir (L.absoluteInstallDirs pkg local copy) ++ "/man1"
         notice verbosity $ unwords ["Copying man page to", mandest]
         installOrdinaryFiles verbosity mandest [("man", "idris.1")]

      make' x target =
         make verbosity [ x, "TARGET=" ++ target, "IDRIS=" ++ idrisCmd local]

-- -----------------------------------------------------------------------------
-- Test

-- There are two "dataDir" in cabal, and they don't relate to each other.
-- When fetching modules, idris uses the second path (in the pkg record),
-- which by default is the root folder of the project.
-- We want it to be the install directory where we put the idris libraries.
fixPkg pkg target = pkg { dataDir = target }

idrisTestHook args pkg local hooks flags = do
  let target = datadir $ L.absoluteInstallDirs pkg local NoCopyDest
  idris <- canonicalizePath (buildDir local </> "idris" </> "idris")
  setEnv "IDRIS" idris
--  testHook simpleUserHooks args (fixPkg pkg target) local hooks flags
  testHook simpleUserHooks args pkg local hooks flags

-- -----------------------------------------------------------------------------
-- Main

-- Install libraries during both copy and install
-- See https://github.com/haskell/cabal/issues/709
main = defaultMainWithHooks $ simpleUserHooks
   { postClean = idrisClean
   , postConf  = idrisPostConf
   , preBuild = idrisPreBuild
   , buildHook = idrisBuildHook
   , postBuild = idrisPostBuild
   , postCopy = \_ flags pkg local ->
                  idrisInstall (S.fromFlag $ S.copyVerbosity flags)
                               (S.fromFlag $ S.copyDest flags) pkg local
   , postInst = \_ flags pkg local ->
                  idrisInstall (S.fromFlag $ S.installVerbosity flags)
                               NoCopyDest pkg local
   , preSDist = idrisPreSDist
   , sDistHook = idrisSDist (sDistHook simpleUserHooks)
   , postSDist = idrisPostSDist
   , testHook = idrisTestHook
   }

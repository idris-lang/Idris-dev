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
import Distribution.Simple.Utils (createDirectoryIfMissingVerbose, rewriteFile)
import Distribution.PackageDescription
import Distribution.Text

import System.Exit
import System.FilePath ((</>), splitDirectories)
import System.Directory
import qualified System.FilePath.Posix as Px
import System.Process
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

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
#ifdef freebsd_HOST_OS
mymake = "gmake"
#else
mymake = "make"
#endif
make verbosity =
   P.runProgramInvocation verbosity . P.simpleProgramInvocation mymake

-- -----------------------------------------------------------------------------
-- Flags

usesLLVM :: S.ConfigFlags -> Bool
usesLLVM flags =
  case lookup (FlagName "llvm") (S.configConfigurationsFlags flags) of
    Just True -> True
    Just False -> False
    Nothing -> True

usesGMP :: S.ConfigFlags -> Bool
usesGMP flags =
  case lookup (FlagName "gmp") (S.configConfigurationsFlags flags) of
    Just True -> True
    Just False -> False
    Nothing -> True

isRelease :: S.ConfigFlags -> Bool
isRelease flags =
    case lookup (FlagName "release") (S.configConfigurationsFlags flags) of
      Just True -> True
      Just False -> False
      Nothing -> False

-- -----------------------------------------------------------------------------
-- Clean

idrisClean _ flags _ _ = do
      cleanStdLib
      cleanLLVM
   where
      verbosity = S.fromFlag $ S.cleanVerbosity flags

      cleanStdLib = do
         makeClean "libs"

      cleanLLVM = makeClean "llvm"

      makeClean dir = make verbosity [ "-C", dir, "clean", "IDRIS=idris" ]


-- -----------------------------------------------------------------------------
-- Configure

idrisConfigure _ flags _ local = do
      configureRTS
      generateVersionModule
   where
      verbosity = S.fromFlag $ S.configVerbosity flags
      version   = pkgVersion . package $ localPkgDescr local

      -- This is a hack. I don't know how to tell cabal that a data file needs
      -- installing but shouldn't be in the distribution. And it won't make the
      -- distribution if it's not there, so instead I just delete
      -- the file after configure.
      configureRTS = make verbosity ["-C", "rts", "clean"]

      -- Put the Git hash into a module for use in the program
      -- For release builds, just put the empty string in the module
      generateVersionModule = do
        gitHash <- Control.Exception.catch (readProcess "git" ["rev-parse", "--short", "HEAD"] "")
                         (\e -> let e' = (e :: SomeException) in return "PRE")
        let hash = takeWhile (/= '\n') gitHash
        let versionModulePath = autogenModulesDir local </> "Version_idris" Px.<.> "hs"
        createDirectoryIfMissingVerbose verbosity True (autogenModulesDir local)
        rewriteFile versionModulePath (versionModuleContents hash)

      versionModuleContents h = "module Version_idris where\n\n" ++
                                "gitHash :: String\n" ++
                                if isRelease (configFlags local)
                                  then "gitHash = \"\"\n"
                                  else "gitHash = \"-git:" ++ h ++ "\"\n"


-- -----------------------------------------------------------------------------
-- Build

idrisBuild _ flags _ local = do
      buildStdLib
      buildRTS
      when (usesLLVM $ configFlags local) buildLLVM
   where
      verbosity = S.fromFlag $ S.buildVerbosity flags

      buildStdLib = do
            putStrLn "Building libraries..."
            makeBuild "libs"
         where
            makeBuild dir = make verbosity [ "-C", dir, "build" , "IDRIS=" ++ idrisCmd local]

      buildRTS = make verbosity (["-C", "rts", "build"] ++ 
                                   gmpflag (usesGMP (configFlags local)))

      buildLLVM = make verbosity ["-C", "llvm", "build"]

      gmpflag False = []
      gmpflag True = ["GMP=-DIDRIS_GMP"]

-- -----------------------------------------------------------------------------
-- Copy/Install

idrisInstall verbosity copy pkg local = do
      installStdLib
      installRTS
      when (usesLLVM $ configFlags local) installLLVM
   where
      target = datadir $ L.absoluteInstallDirs pkg local copy

      installStdLib = do
            putStrLn $ "Installing libraries in " ++ target
            makeInstall "libs" target

      installRTS = do
         let target' = target </> "rts"
         putStrLn $ "Installing run time system in " ++ target'
         makeInstall "rts" target'

      installLLVM = do
         let target' = target </> "llvm"
         putStrLn $ "Installing LLVM library in " ++ target
         makeInstall "llvm" target'

      makeInstall src target =
         make verbosity [ "-C", src, "install" , "TARGET=" ++ target, "IDRIS=" ++ idrisCmd local]

-- -----------------------------------------------------------------------------
-- Main

-- Install libraries during both copy and install
-- See http://hackage.haskell.org/trac/hackage/ticket/718
main = defaultMainWithHooks $ simpleUserHooks
   { postClean = idrisClean
   , postConf  = idrisConfigure
   , postBuild = idrisBuild
   , postCopy = \_ flags pkg local ->
                  idrisInstall (S.fromFlag $ S.copyVerbosity flags)
                               (S.fromFlag $ S.copyDest flags) pkg local
   , postInst = \_ flags pkg local ->
                  idrisInstall (S.fromFlag $ S.installVerbosity flags)
                               NoCopyDest pkg local
   }

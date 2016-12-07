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

-- -----------------------------------------------------------------------------
-- Flags

usesGMP :: S.ConfigFlags -> Bool
usesGMP flags =
  case lookup (FlagName "gmp") (S.configConfigurationsFlags flags) of
    Just True -> True
    Just False -> False
    Nothing -> False

-- -----------------------------------------------------------------------------
-- Configure

idrisConfigure _ flags _ local = do
    -- This is a hack. I don't know how to tell cabal that a data file needs
    -- installing but shouldn't be in the distribution. And it won't make the
    -- distribution if it's not there, so instead I just delete
    -- the file after configure.
    make verbosity ["-C", "rts", "clean"]
    where
      verbosity = S.fromFlag $ S.configVerbosity flags
      version   = pkgVersion . package $ localPkgDescr local

-- -----------------------------------------------------------------------------
-- Build

idrisBuild _ flags _ local = do
      make verbosity (["-C", "rts", "build"] ++
                        gmpflag (usesGMP (configFlags local)))
   where
      verbosity = S.fromFlag $ S.buildVerbosity flags

      gmpflag False = []
      gmpflag True = ["GMP=-DIDRIS_GMP"]

-- -----------------------------------------------------------------------------
-- Copy/Install

idrisInstall verbosity copy pkg local = do
      let target' = target </> "rts"
      putStrLn $ "Installing run time system in " ++ target'
      makeInstall "rts" target'
   where
      target = datadir $ L.absoluteInstallDirs pkg local copy

      makeInstall src target =
         make verbosity [ "-C", src, "install" , "TARGET=" ++ target, "IDRIS=" ++ idrisCmd local]

-- -----------------------------------------------------------------------------
-- Main

main = defaultMainWithHooks $ simpleUserHooks
   { postConf  = idrisConfigure
   , postBuild = idrisBuild
   , postCopy = \_ flags pkg local ->
                  idrisInstall (S.fromFlag $ S.copyVerbosity flags)
                               (S.fromFlag $ S.copyDest flags) pkg local
   , postInst = \_ flags pkg local ->
                  idrisInstall (S.fromFlag $ S.installVerbosity flags)
                               NoCopyDest pkg local
   }

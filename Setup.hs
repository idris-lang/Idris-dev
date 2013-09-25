{-# LANGUAGE CPP #-}
import Control.Monad
import Data.IORef

import Distribution.Simple
import Distribution.Simple.InstallDirs as I
import Distribution.Simple.LocalBuildInfo as L
import qualified Distribution.Simple.Setup as S
import qualified Distribution.Simple.Program as P
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
idrisCmd local = Px.joinPath $ splitDirectories $ ".." <//> buildDir local <//> "idris" <//> "idris"
#else
idrisCmd local = ".." </>  buildDir local </>  "idris" </>  "idris"
#endif

-- -----------------------------------------------------------------------------
-- Make Commands

make verbosity =
   P.runProgramInvocation verbosity . P.simpleProgramInvocation "make"

-- -----------------------------------------------------------------------------
-- Flags

usesLLVM :: S.ConfigFlags -> Bool
usesLLVM flags =
  case lookup (FlagName "llvm") (S.configConfigurationsFlags flags) of
    Just True -> True
    Just False -> False
    Nothing -> True

usesEffects :: S.ConfigFlags -> Bool
usesEffects flags =
   case lookup (FlagName "effects") (S.configConfigurationsFlags flags) of
      Just True -> True
      Just False -> False
      Nothing -> True

-- -----------------------------------------------------------------------------
-- Clean

idrisClean _ flags _ _ = do
      cleanStdLib
      cleanLLVM
   where
      verbosity = S.fromFlag $ S.cleanVerbosity flags

      cleanStdLib = do
         makeClean "lib"
         makeClean "effects"
         makeClean "javascript"

      cleanLLVM = makeClean "llvm"

      makeClean dir = make verbosity [ "-C", dir, "clean", "IDRIS=idris" ]


-- -----------------------------------------------------------------------------
-- Configure

idrisConfigure _ flags _ local = do
      configureRTS
   where
      verbosity = S.fromFlag $ S.configVerbosity flags
      version   = pkgVersion . package $ localPkgDescr local

      -- This is a hack. I don't know how to tell cabal that a data file needs
      -- installing but shouldn't be in the distribution. And it won't make the
      -- distribution if it's not there, so instead I just delete
      -- the file after configure.
      configureRTS = make verbosity ["-C", "rts", "clean"]

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
            makeBuild "lib"
            when (usesEffects $ configFlags local) $ makeBuild "effects"
            makeBuild "javascript"
         where
            makeBuild dir = make verbosity [ "-C", dir, "build" , "IDRIS=" ++ idrisCmd local]

      buildRTS = make verbosity ["-C", "rts", "build"]

      buildLLVM = make verbosity ["-C", "llvm", "build"]

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
            makeInstall "lib" target
            when (usesEffects $ configFlags local) $ makeInstall "effects" target
            makeInstall "javascript" target

      installRTS = do
         let target' = target </> "rts"
         putStrLn $ "Installing run time system in " ++ target'
         makeInstall "rts" target'

      installLLVM = do
         let target' = target </> "llvm"
         putStrLn $ "Installing LLVM library in " ++ target
         makeInstall "llvm" target

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

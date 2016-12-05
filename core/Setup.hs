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

-- -----------------------------------------------------------------------------
-- Flags

isRelease :: S.ConfigFlags -> Bool
isRelease flags =
    case lookup (FlagName "release") (S.configConfigurationsFlags flags) of
      Just True -> True
      Just False -> False
      Nothing -> False

gitHash :: IO String
gitHash = do h <- Control.Exception.catch (readProcess "git" ["rev-parse", "--short", "HEAD"] "")
                  (\e -> let e' = (e :: SomeException) in return "PRE")
             return $ takeWhile (/= '\n') h

-- Put the Git hash into a module for use in the program
-- For release builds, just put the empty string in the module
generateVersionModule verbosity dir release = do
    hash <- gitHash
    let versionModulePath = dir </> "Version_idris_core" Px.<.> "hs"
    putStrLn $ "Generating " ++ versionModulePath ++
             if release then " for release" else " for prerelease " ++ hash
    createDirectoryIfMissingVerbose verbosity True dir
    rewriteFile versionModulePath (versionModuleContents hash)

  where versionModuleContents h = "module Version_idris_core where\n\n" ++
                                  "gitHash :: String\n" ++
                                  if release
                                    then "gitHash = \"\"\n"
                                    else "gitHash = \"git:" ++ h ++ "\"\n"

idrisConfigure _ flags _ local = do
    generateVersionModule verbosity (autogenModulesDir local) (isRelease (configFlags local))
    where
      verbosity = S.fromFlag $ S.configVerbosity flags

idrisPreSDist args flags = do
  let verb = S.fromFlag (S.sDistVerbosity flags)
  generateVersionModule verb "src" True
  preSDist simpleUserHooks args flags

idrisPostSDist args flags desc lbi = do
  Control.Exception.catch (do let file = "src" </> "Version_idris_core" Px.<.> "hs"
                              putStrLn $ "Removing generated modules:\n "
                                        ++ file
                              removeFile file)
             (\e -> let e' = (e :: SomeException) in return ())
  postSDist simpleUserHooks args flags desc lbi

main = defaultMainWithHooks $ simpleUserHooks
   { postConf  = idrisConfigure
   , preSDist  = idrisPreSDist
   , postSDist = idrisPostSDist
   }

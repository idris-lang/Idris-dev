{-# LANGUAGE CPP #-}
import Distribution.Simple
import Distribution.Simple.InstallDirs as I
import Distribution.Simple.LocalBuildInfo as L
import qualified Distribution.Simple.Setup as S
import qualified Distribution.Simple.Program as P
import Distribution.PackageDescription

import System.Exit
import System.FilePath ((</>))
import System.Process

-- After Idris is built, we need to check and install the prelude and other libs

make verbosity = P.runProgramInvocation verbosity . P.simpleProgramInvocation "make"

#ifdef mingw32_HOST_OS
-- make on mingw32 exepects unix style separators
idrisCmd local = "../dist/build/idris/idris"
#else
idrisCmd local = ".." </> buildDir local </> "idris" </> "idris"
#endif

cleanStdLib verbosity
    = make verbosity [ "-C", "lib", "clean" ]

installStdLib pkg local verbosity copy
    = do let dirs = L.absoluteInstallDirs pkg local copy
         let idir = datadir dirs
         let icmd = idrisCmd local
         putStrLn $ "Installing libraries in " ++ idir
         make verbosity
               [ "-C", "lib", "install"
               , "TARGET=" ++ idir
               , "IDRIS=" ++ icmd
               ]
         let idirRts = idir </> "rts"
         putStrLn $ "Installing run time system in " ++ idirRts
         make verbosity
               [ "-C", "rts", "install"
               , "TARGET=" ++ idirRts
               , "IDRIS=" ++ icmd
               ]

-- This is a hack. I don't know how to tell cabal that a data file needs
-- installing but shouldn't be in the distribution. And it won't make the
-- distribution if it's not there, so instead I just delete
-- the file after configure.

removeLibIdris local verbosity
    = do let icmd = idrisCmd local
         make verbosity
               [ "-C", "rts", "clean"
               , "IDRIS=" ++ icmd
               ]

checkStdLib local verbosity
    = do let icmd = idrisCmd local
         putStrLn $ "Building libraries..."
         make verbosity
               [ "-C", "lib", "check"
               , "IDRIS=" ++ icmd
               ]
         make verbosity
               [ "-C", "rts", "check"
               , "IDRIS=" ++ icmd
               ]

-- Install libraries during both copy and install
-- See http://hackage.haskell.org/trac/hackage/ticket/718
main = defaultMainWithHooks $ simpleUserHooks
        { postCopy = \ _ flags pkg lbi -> do
              installStdLib pkg lbi (S.fromFlag $ S.copyVerbosity flags)
                                    (S.fromFlag $ S.copyDest flags)
        , postInst = \ _ flags pkg lbi -> do
              installStdLib pkg lbi (S.fromFlag $ S.installVerbosity flags)
                                    NoCopyDest
        , postConf  = \ _ flags _ lbi -> do
              removeLibIdris lbi (S.fromFlag $ S.configVerbosity flags)
        , postClean = \ _ flags _ _ -> do
              cleanStdLib (S.fromFlag $ S.cleanVerbosity flags)
        , postBuild = \ _ flags _ lbi -> do
              checkStdLib lbi (S.fromFlag $ S.buildVerbosity flags)
        }

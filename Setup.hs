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

cleanStdLib verbosity
    = make verbosity [ "-C", "lib", "clean" ]

installStdLib pkg local verbosity copy
    = do let dirs = L.absoluteInstallDirs pkg local copy
         let idir = datadir dirs
         let icmd = ".." </> buildDir local </> "idris" </> "idris"
         putStrLn $ "Installing libraries in " ++ idir
         make verbosity
               [ "-C", "lib", "install"
               , "TARGET=" ++ idir
               , "IDRIS=" ++ icmd
               ]

checkStdLib local verbosity
    = do let icmd = ".." </> buildDir local </> "idris" </> "idris"
         putStrLn $ "Building libraries..."
         make verbosity
               [ "-C", "lib", "check"
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
        , postClean = \ _ flags _ _ -> do
              cleanStdLib (S.fromFlag $ S.cleanVerbosity flags)
        , postBuild = \ _ flags _ lbi -> do
              checkStdLib lbi (S.fromFlag $ S.buildVerbosity flags)
        }



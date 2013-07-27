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

make verbosity = P.runProgramInvocation verbosity . P.simpleProgramInvocation "make"

#ifdef mingw32_HOST_OS
-- make on mingw32 exepects unix style separators
(<//>) = (Px.</>)
idrisCmd local = Px.joinPath $ splitDirectories $
                 ".." <//> buildDir local <//> "idris" <//> "idris"
rtsDir local = Px.joinPath $ splitDirectories $
               ".." <//> buildDir local <//> "rts" <//> "libidris_rts"
#else
idrisCmd local = ".." </>  buildDir local </>  "idris" </>  "idris"
rtsDir local = ".." </> buildDir local </> "rts" </> "libidris_rts"
#endif

cleanStdLib verbosity
    = do make verbosity [ "-C", "lib", "clean", "IDRIS=idris" ]
         make verbosity [ "-C", "effects", "clean", "IDRIS=idris" ]
         make verbosity [ "-C", "javascript", "clean", "IDRIS=idris" ]

cleanJavaPom verbosity 
  = do execPomExists <- doesFileExist ("java" </> "executable_pom.xml")
       when execPomExists $ removeFile ("java" </> "executable_pom.xml")

cleanLLVMLib verbosity = make verbosity ["-C", "llvm", "clean"]

installStdLib pkg local withoutEffects verbosity copy
    = do let dirs = L.absoluteInstallDirs pkg local copy
         let idir = datadir dirs
         let icmd = idrisCmd local
         putStrLn $ "Installing libraries in " ++ idir
         make verbosity
               [ "-C", "lib", "install"
               , "TARGET=" ++ idir
               , "IDRIS=" ++ icmd
               ]
         unless withoutEffects $
           make verbosity
                 [ "-C", "effects", "install"
                 , "TARGET=" ++ idir
                 , "IDRIS=" ++ icmd
                 ]
         make verbosity
               [ "-C", "javascript", "install"
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

installLLVMLib verbosity pkg local copy =
    let idir = datadir $ L.absoluteInstallDirs pkg local copy in
    make verbosity ["-C", "llvm", "install", "TARGET=" ++ idir </> "llvm"]

installJavaPom pkg local verbosity copy version = do
  putStrLn $ "Installing java pom template" 
  let dir = datadir $ L.absoluteInstallDirs pkg local copy
  copyFile ("java" </> "executable_pom.xml") (dir </> "executable_pom.xml")

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

checkStdLib local withoutEffects verbosity
    = do let icmd = idrisCmd local
         putStrLn $ "Building libraries..."
         make verbosity
               [ "-C", "lib", "check"
               , "IDRIS=" ++ icmd
               ]
         unless withoutEffects $
           make verbosity
               [ "-C", "effects", "check"
               , "IDRIS=" ++ icmd
               ]
         make verbosity
               [ "-C", "javascript", "check"
               , "IDRIS=" ++ icmd
               ]
         make verbosity
               [ "-C", "rts", "check"
               , "IDRIS=" ++ icmd
               ]

llvmFlag flags = 
  case lookup (FlagName "LLVM") (S.configConfigurationsFlags flags) of
    Just True -> True
    Just False -> False
    Nothing -> True

noEffectsFlag flags =
   case lookup (FlagName "noeffects") (S.configConfigurationsFlags flags) of
      Just True -> True
      Just False -> False
      Nothing -> False

preparePoms version
    = do execPomTemplate <- TIO.readFile ("java" </> "executable_pom_template.xml")
         TIO.writeFile ("java" </> "executable_pom.xml") (insertVersion execPomTemplate)
    where
      insertVersion template = 
        T.replace (T.pack "$RTS-VERSION$") (T.pack $ display version) template

-- Install libraries during both copy and install
-- See http://hackage.haskell.org/trac/hackage/ticket/718
main = do
  defaultMainWithHooks $ simpleUserHooks
        { postCopy = \ _ flags pkg lbi -> do
              let verb = S.fromFlag $ S.copyVerbosity flags
              let withoutEffects = noEffectsFlag $ configFlags lbi
              installStdLib pkg lbi withoutEffects verb
                                    (S.fromFlag $ S.copyDest flags)
              installJavaPom pkg lbi verb 
                                   (S.fromFlag $ S.copyDest flags)
                                   (pkgVersion . package $ localPkgDescr lbi)
              when (llvmFlag $ configFlags lbi)  
                   (installLLVMLib verb pkg lbi (S.fromFlag $ S.copyDest flags))
       , postInst = \ _ flags pkg lbi -> do
              let verb = (S.fromFlag $ S.installVerbosity flags)
              let withoutEffects = noEffectsFlag $ configFlags lbi
              installStdLib pkg lbi withoutEffects verb
                                    NoCopyDest
              installJavaPom pkg lbi verb 
                                   NoCopyDest 
                                   (pkgVersion . package $ localPkgDescr lbi)
              when (llvmFlag $ configFlags lbi)  
                   (installLLVMLib verb pkg lbi NoCopyDest)
        , postConf  = \ _ flags _ lbi -> do
              removeLibIdris lbi (S.fromFlag $ S.configVerbosity flags)
              preparePoms . pkgVersion . package $ localPkgDescr lbi
        , postClean = \ _ flags _ _ -> do
              let verb = S.fromFlag $ S.cleanVerbosity flags
              cleanStdLib verb
              cleanLLVMLib verb
              cleanJavaPom verb
        , postBuild = \ _ flags _ lbi -> do
              let verb = S.fromFlag $ S.buildVerbosity flags
              let withoutEffects = noEffectsFlag $ configFlags lbi
              checkStdLib lbi withoutEffects verb
        }

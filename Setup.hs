import Distribution.Simple
import Distribution.Simple.InstallDirs as I
import Distribution.Simple.LocalBuildInfo as L
import Distribution.PackageDescription

import System.Exit
import System.Process

-- After Idris is built, we need to check and install the prelude and other libs

system' cmd = do 
    exit <- system cmd
    case exit of
      ExitSuccess -> return ()
      ExitFailure _ -> exitWith exit

postCleanLib args flags desc _
    = system' "make -C lib clean"

addPrefix pfx var c = "export " ++ var ++ "=" ++ show pfx ++ "/" ++ c ++ ":$" ++ var

postInstLib args flags desc local
    = do let pkg = localPkgDescr local
         let penv = packageTemplateEnv (package pkg)
         let cenv = compilerTemplateEnv (compilerId (compiler local))
         let dirs_pkg = substituteInstallDirTemplates penv (installDirTemplates local)
         let dirs = substituteInstallDirTemplates cenv dirs_pkg
         let datad = datadir dirs
         let datasubd = datasubdir dirs
         let idir = fromPathTemplate (datadir dirs) ++ "/" ++ 
                    fromPathTemplate (datasubdir dirs)
         putStrLn $ "Installing libraries in " ++ idir
         system' $ "make -C lib install TARGET=" ++ idir

main = defaultMainWithHooks (simpleUserHooks { postInst = postInstLib,
                                               postClean = postCleanLib })



{-# LANGUAGE CPP #-}
module Pkg.Package where

import System.Process
import System.Directory
import System.Exit
import System.IO
import System.FilePath ((</>), addTrailingPathSeparator, takeFileName)
import System.Directory (createDirectoryIfMissing, copyFile)

import Util.System

import Control.Monad
import Data.List
import Data.List.Split(splitOn)

import Idris.Core.TT
import Idris.REPL
import Idris.AbsSyntax

import IRTS.System

import Pkg.PParser

import Paths_idris (getDataDir)

-- To build a package:
-- * read the package description
-- * check all the library dependencies exist
-- * invoke the makefile if there is one
-- * invoke idris on each module, with idris_opts
-- * install everything into datadir/pname, if install flag is set

-- | Run the package through the idris compiler.
buildPkg :: Bool -> (Bool, FilePath) -> IO ()
buildPkg warnonly (install, fp)
     = do pkgdesc <- parseDesc fp
          ok <- mapM (testLib warnonly (pkgname pkgdesc)) (libdeps pkgdesc)
          when (and ok) $
            do dir <- getCurrentDirectory
               setCurrentDirectory $ dir </> sourcedir pkgdesc
               make (makefile pkgdesc)
               m_ist <- case (execout pkgdesc) of
                   Nothing -> buildMods (NoREPL : Verbose : idris_opts pkgdesc)
                                    (modules pkgdesc)
                   Just o -> do let exec = dir </> o
                                buildMods
                                    (NoREPL : Verbose : Output exec : idris_opts pkgdesc)
                                    [idris_main pkgdesc]
               setCurrentDirectory dir
               case m_ist of
                    Nothing -> exitWith (ExitFailure 1)
                    Just ist -> do
                       -- Quit with error code if there was a problem
                       case errLine ist of
                            Just _ -> exitWith (ExitFailure 1)
                            _ -> return ()
                       -- Also give up if there are metavariables to solve
                       case (map fst (idris_metavars ist) \\ primDefs) of
                            _ -> when install $ installPkg pkgdesc
--                             ms -> do if install 
--                                         then putStrLn "Can't install: there are undefined metavariables:"
--                                         else putStrLn "There are undefined metavariables:"
--                                      putStrLn $ "\t" ++ show ms 
--                                      exitWith (ExitFailure 1)

-- | Type check packages only
--
-- This differs from build in that executables are not built, if the
-- package contains an executable.
checkPkg :: Bool         -- ^ Show Warnings
            -> Bool      -- ^ quit on failure
            -> FilePath  -- ^ Path to ipkg file.
            -> IO ()
checkPkg warnonly quit fpath
  = do pkgdesc <-parseDesc fpath
       ok <- mapM (testLib warnonly (pkgname pkgdesc)) (libdeps pkgdesc)
       when (and ok) $
         do dir <- getCurrentDirectory
            setCurrentDirectory $ dir </> sourcedir pkgdesc
            make (makefile pkgdesc)
            res <- buildMods (NoREPL : Verbose : idris_opts pkgdesc)
                             (modules pkgdesc)
            setCurrentDirectory dir
            when quit $ case res of
                          Nothing -> exitWith (ExitFailure 1)
                          Just res' -> do
                            case errLine res' of
                              Just _ -> exitWith (ExitFailure 1)
                              _ -> return ()

-- | Check a package and start a REPL
replPkg :: FilePath -> Idris ()
replPkg fp = do orig <- getIState
                runIO $ checkPkg False False fp
                pkgdesc <- runIO $ parseDesc fp -- bzzt, repetition!
                let opts = idris_opts pkgdesc
                let mod = idris_main pkgdesc
                let f = toPath (showCG mod)
                putIState orig
                dir <- runIO $ getCurrentDirectory
                runIO $ setCurrentDirectory $ dir </> sourcedir pkgdesc

                if (f /= "")
                   then idrisMain ((Filename f) : opts) 
                   else iputStrLn "Can't start REPL: no main module given"
                runIO $ setCurrentDirectory dir

    where toPath n = foldl1' (</>) $ splitOn "." n

-- | Clean Package build files
cleanPkg :: FilePath -- ^ Path to ipkg file.
         -> IO ()
cleanPkg fp
     = do pkgdesc <- parseDesc fp
          dir <- getCurrentDirectory
          setCurrentDirectory $ dir </> sourcedir pkgdesc
          clean (makefile pkgdesc)
          mapM_ rmIBC (modules pkgdesc)
          case execout pkgdesc of
               Nothing -> return ()
               Just s -> rmFile $ dir </> s

-- | Install package
installPkg :: PkgDesc -> IO ()
installPkg pkgdesc
     = do dir <- getCurrentDirectory
          setCurrentDirectory $ dir </> sourcedir pkgdesc
          case (execout pkgdesc) of
              Nothing -> mapM_ (installIBC (pkgname pkgdesc)) (modules pkgdesc)
              Just o -> return () -- do nothing, keep executable locally, for noe
          mapM_ (installObj (pkgname pkgdesc)) (objs pkgdesc)


-- ---------------------------------------------------------- [ Helper Methods ]
-- Methods for building, testing, installing, and removal of idris
-- packages.

buildMods :: [Opt] -> [Name] -> IO (Maybe IState)
buildMods opts ns = do let f = map (toPath . showCG) ns
--                        putStrLn $ "MODULE: " ++ show f
                       idris (map Filename f ++ opts)
    where toPath n = foldl1' (</>) $ splitOn "." n

testLib :: Bool -> String -> String -> IO Bool
testLib warn p f
    = do d <- getDataDir
         gcc <- getCC
         (tmpf, tmph) <- tempfile
         hClose tmph
         let libtest = d </> "rts" </> "libtest.c"
         e <- system $ gcc ++ " " ++ libtest ++ " -l" ++ f ++ " -o " ++ tmpf
         case e of
            ExitSuccess -> return True
            _ -> do if warn
                       then do putStrLn $ "Not building " ++ p ++
                                          " due to missing library " ++ f
                               return False
                       else fail $ "Missing library " ++ f

rmIBC :: Name -> IO ()
rmIBC m = rmFile $ toIBCFile m

toIBCFile (UN n) = str n ++ ".ibc"
toIBCFile (NS n ns) = foldl1' (</>) (reverse (toIBCFile n : map str ns))

installIBC :: String -> Name -> IO ()
installIBC p m = do let f = toIBCFile m
                    d <- getTargetDir
                    let destdir = d </> p </> getDest m
                    putStrLn $ "Installing " ++ f ++ " to " ++ destdir
                    createDirectoryIfMissing True destdir
                    copyFile f (destdir </> takeFileName f)
                    return ()
    where getDest (UN n) = ""
          getDest (NS n ns) = foldl1' (</>) (reverse (getDest n : map str ns))


installObj :: String -> String -> IO ()
installObj p o = do d <- getTargetDir
                    let destdir = addTrailingPathSeparator (d </> p)
                    putStrLn $ "Installing " ++ o ++ " to " ++ destdir
                    createDirectoryIfMissing True destdir
                    copyFile o (destdir </> takeFileName o)
                    return ()

#ifdef mingw32_HOST_OS
mkDirCmd = "mkdir "
#else
mkDirCmd = "mkdir -p "
#endif

-- ------------------------------------------------------- [ Makefile Commands ]
-- | Invoke a Makefile's default target.
make :: Maybe String -> IO ()
make Nothing = return ()
make (Just s) = do system $ "make -f " ++ s
                   return ()

-- | Invoke a Makefile's clean target.
clean :: Maybe String -> IO ()
clean Nothing = return ()
clean (Just s) = do system $ "make -f " ++ s ++ " clean"
                    return ()

-- --------------------------------------------------------------------- [ EOF ]

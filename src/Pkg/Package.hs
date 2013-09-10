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

import Core.TT
import Idris.REPL
import Idris.AbsSyntax

import Pkg.PParser

import Paths_idris

-- To build a package:
-- * read the package description
-- * check all the library dependencies exist
-- * invoke the makefile if there is one
-- * invoke idris on each module, with idris_opts
-- * install everything into datadir/pname, if install flag is set

buildPkg :: Bool -> (Bool, FilePath) -> IO ()
buildPkg warnonly (install, fp) 
     = do pkgdesc <- parseDesc fp
          ok <- mapM (testLib warnonly (pkgname pkgdesc)) (libdeps pkgdesc)
          when (and ok) $
            do dir <- getCurrentDirectory
               setCurrentDirectory $ dir </> sourcedir pkgdesc
               make (makefile pkgdesc)
               case (execout pkgdesc) of
                   Nothing -> buildMods (NoREPL : Verbose : idris_opts pkgdesc)
                                    (modules pkgdesc)
                   Just o -> do let exec = dir </> o
                                buildMods
                                    (NoREPL : Verbose : Output exec : idris_opts pkgdesc) 
                                    [idris_main pkgdesc]
               setCurrentDirectory dir
               when install $ installPkg pkgdesc

cleanPkg :: FilePath -> IO ()
cleanPkg fp 
     = do pkgdesc <- parseDesc fp
          dir <- getCurrentDirectory
          setCurrentDirectory $ dir </> sourcedir pkgdesc
          clean (makefile pkgdesc) 
          mapM_ rmIBC (modules pkgdesc)
          case execout pkgdesc of
               Nothing -> return ()
               Just s -> rmFile $ dir </> s

installPkg :: PkgDesc -> IO ()
installPkg pkgdesc
     = do dir <- getCurrentDirectory
          setCurrentDirectory $ dir </> sourcedir pkgdesc
          case (execout pkgdesc) of
              Nothing -> mapM_ (installIBC (pkgname pkgdesc)) (modules pkgdesc)
              Just o -> return () -- do nothing, keep executable locally, for noe
          mapM_ (installObj (pkgname pkgdesc)) (objs pkgdesc)

buildMods :: [Opt] -> [Name] -> IO ()
buildMods opts ns = do let f = map (toPath . show) ns
--                        putStrLn $ "MODULE: " ++ show f
                       idris (map Filename f ++ opts) 
                       return ()
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
             
toIBCFile (UN n) = n ++ ".ibc"
toIBCFile (NS n ns) = foldl1' (</>) (reverse (toIBCFile n : ns))

installIBC :: String -> Name -> IO ()
installIBC p m = do let f = toIBCFile m
                    target <- environment "TARGET"
                    d <- maybe getDataDir return target
                    let destdir = d </> p </> getDest m
                    putStrLn $ "Installing " ++ f ++ " to " ++ destdir
                    createDirectoryIfMissing True destdir
                    copyFile f (destdir </> takeFileName f)
                    return ()
    where getDest (UN n) = ""
          getDest (NS n ns) = foldl1' (</>) (reverse (getDest n : ns))

installObj :: String -> String -> IO ()
installObj p o = do d <- getDataDir
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

make :: Maybe String -> IO ()
make Nothing = return ()
make (Just s) = do system $ "make -f " ++ s
                   return ()

clean :: Maybe String -> IO ()
clean Nothing = return ()
clean (Just s) = do system $ "make -f " ++ s ++ " clean"
                    return ()

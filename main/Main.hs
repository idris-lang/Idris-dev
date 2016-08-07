module Main where

import System.Exit ( exitSuccess )

import Control.Monad ( when )

import Idris.AbsSyntax
import Idris.REPL
-- import Idris.Imports
import Idris.Error
import Idris.CmdOptions
import Idris.Info
import Idris.Package



import Util.System ( setupBundledCC )



-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

main :: IO ()
main = do opts <- runArgParser
          runMain (runIdris opts)

runIdris :: [Opt] -> Idris ()
runIdris opts = do
    runIO setupBundledCC
    when (ShowLoggingCats `elem` opts)  $ runIO showLoggingCats
    when (ShowIncs `elem` opts)         $ runIO showIncs
    when (ShowLibs `elem` opts)         $ runIO showLibs
    when (ShowLibdir `elem` opts)       $ runIO showLibdir
    when (ShowPkgs `elem` opts)         $ runIO showPkgs
    case opt getClient opts of
       []    -> return ()
       (c:_) -> do setVerbose False
                   setQuiet True
                   runIO $ runClient (getPort opts) c
                   runIO exitSuccess
    case opt getPkgCheck opts of
       [] -> return ()
       fs -> do runIO $ mapM_ (checkPkg opts (WarnOnly `elem` opts) True) fs
                runIO exitSuccess
    case opt getPkgClean opts of
       [] -> return ()
       fs -> do runIO $ mapM_ (cleanPkg opts) fs
                runIO exitSuccess
    case opt getPkgMkDoc opts of                -- IdrisDoc
       [] -> return ()
       fs -> do runIO $ mapM_ (documentPkg opts) fs
                runIO exitSuccess
    case opt getPkgTest opts of
       [] -> return ()
       fs -> do runIO $ mapM_ (testPkg opts) fs
                runIO exitSuccess
    case opt getPkg opts of
       [] -> case opt getPkgREPL opts of
                  [] -> idrisMain opts
                  [f] -> replPkg opts f
                  _ -> ifail "Too many packages"
       fs -> runIO $ mapM_ (buildPkg opts (WarnOnly `elem` opts)) fs

showLibs :: IO b
showLibs = do libFlags <- getIdrisFlagsLib
              putStrLn $ unwords libFlags
              exitSuccess

showLibdir :: IO b
showLibdir = do putStrLn =<< getIdrisLibDir
                exitSuccess

showIncs :: IO b
showIncs = do incFlags <- getIdrisFlagsInc
              putStrLn $ unwords incFlags
              exitSuccess

-- | List idris packages installed
showPkgs :: IO b
showPkgs = do mapM_ putStrLn =<< getIdrisInstalledPackages
              exitSuccess

showLoggingCats :: IO b
showLoggingCats = do
    mapM_ putStrLn =<< getIdrisLoggingCategories
    exitSuccess

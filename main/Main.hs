module Main where

import System.Exit ( exitSuccess )

import Control.Monad ( when )

import Idris.AbsSyntax
import Idris.Error
import Idris.CmdOptions
import Idris.Info
import Idris.Info.Show
import Idris.Package
import Idris.Main

import Util.System ( setupBundledCC )



-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

main :: IO ()
main = do opts <- runArgParser
          runMain (runIdris opts)

-- | The main function for the Idris executable.
runIdris :: [Opt] -> Idris ()
runIdris opts = do
    runIO setupBundledCC
    -- Show information then quit.
    when (ShowAll `elem` opts)          $ runIO showExitIdrisInfo
    when (ShowLoggingCats `elem` opts)  $ runIO showExitIdrisLoggingCategories
    when (ShowIncs `elem` opts)         $ runIO showExitIdrisFlagsInc
    when (ShowLibs `elem` opts)         $ runIO showExitIdrisFlagsLibs
    when (ShowLibdir `elem` opts)       $ runIO showExitIdrisLibDir
    when (ShowPkgs `elem` opts)         $ runIO showExitIdrisInstalledPackages

    -- Be a client to an IDE Mode server.
    case opt getClient opts of
       []    -> return ()
       (c:_) -> do setVerbose False
                   setQuiet True
                   runIO $ runClient (getPort opts) c
                   runIO exitSuccess

    -- Work with Idris packages.                   
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

    -- Either launch one of the interaction modes, or install a
    -- package.
    case opt getPkg opts of
       [] -> case opt getPkgREPL opts of
                  [] -> idrisMain opts
                  [f] -> replPkg opts f
                  _ -> ifail "Too many packages"
       fs -> runIO $ mapM_ (buildPkg opts (WarnOnly `elem` opts)) fs


module Main where

import System.Console.Haskeline
import System.IO
import System.Environment
import System.Exit
import System.FilePath ((</>), addTrailingPathSeparator)

import Data.Maybe
import Data.Version
import Control.Monad.Trans.Error ( ErrorT(..) )
import Control.Monad.Trans.State.Strict ( execStateT, get, put )
import Control.Monad ( when )

import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Core.Evaluate
import Idris.Core.Constraints

import Idris.AbsSyntax
import Idris.Parser
import Idris.REPL
import Idris.ElabDecls
import Idris.Primitives
import Idris.Imports
import Idris.Error

import IRTS.System ( getLibFlags, getIdrisLibDir, getIncFlags )

import Util.DynamicLinker

import Pkg.Package

import Paths_idris

-- Main program reads command line options, parses the main program, and gets
-- on with the REPL.

main = do xs <- getArgs
          let opts = parseArgs xs
          result <- runErrorT $ execStateT (runIdris opts) idrisInit
          case result of
            Left err -> putStrLn $ "Uncaught error: " ++ show err
            Right _ -> return ()

runIdris :: [Opt] -> Idris ()
runIdris [Client c] = do setVerbose False
                         setQuiet True
                         runIO $ runClient c
runIdris opts = do
       when (Ver `elem` opts) $ runIO showver
       when (Usage `elem` opts) $ runIO usage
       when (ShowIncs `elem` opts) $ runIO showIncs
       when (ShowLibs `elem` opts) $ runIO showLibs
       when (ShowLibdir `elem` opts) $ runIO showLibdir
       case opt getPkgCheck opts of
           [] -> return ()
           fs -> do runIO $ mapM_ (checkPkg (WarnOnly `elem` opts)) fs
                    runIO $ exitWith ExitSuccess
       case opt getPkgClean opts of
           [] -> return ()
           fs -> do runIO $ mapM_ cleanPkg fs
                    runIO $ exitWith ExitSuccess
       case opt getPkg opts of
           [] -> idrisMain opts -- in Idris.REPL
           fs -> runIO $ mapM_ (buildPkg (WarnOnly `elem` opts)) fs

usage = do putStrLn usagemsg
           exitWith ExitSuccess

showver = do putStrLn $ "Idris version " ++ ver
             exitWith ExitSuccess

showLibs = do libFlags <- getLibFlags
              putStrLn libFlags
              exitWith ExitSuccess

showLibdir = do dir <- getIdrisLibDir
                putStrLn dir
                exitWith ExitSuccess

showIncs = do incFlags <- getIncFlags
              putStrLn incFlags
              exitWith ExitSuccess

usagemsghdr = "Idris version " ++ ver ++ ", (C) The Idris Community 2014"

usagemsg = usagemsghdr ++ "\n" ++ 
           map (\x -> '-') usagemsghdr ++ "\n" ++  
           "idris [OPTIONS] [FILE]\n\n" ++
           "Common flags:\n" ++
           "\t    --install=IPKG          Install package\n" ++
           "\t    --clean=IPKG            Clean package\n" ++
           "\t    --build=IPKG            Build package\n" ++
           "\t    --exec=EXPR             Execute as idris\n" ++
           "\t    --libdir                Display library directory\n" ++
           "\t    --link                  Display link directory\n" ++
           "\t    --include               Display the includes directory\n" ++
           "\t    --nobanner              Suppress the banner\n" ++
           "\t    --color, --colour       Force coloured output\n" ++
           "\t    --nocolor, --nocolour   Disable coloured output\n" ++
           "\t    --errorcontent          Undocumented\n" ++
           "\t    --nocoverage            Undocumented\n" ++
           "\t -o --output=FILE           Specify output file\n" ++
           "\t    --check                 Undocumented\n" ++
           "\t    --total                 Require functions to be total by default\n" ++
           "\t    --partial               Undocumented\n" ++
           "\t    --warnpartial           Warn about undeclared partial functions.\n" ++
           "\t    --warn                  Undocumented\n" ++
           "\t    --typecase              Undocumented\n" ++
           "\t    --typeintype            Undocumented\n" ++
           "\t    --nobasepkgs            Undocumented\n" ++
           "\t    --noprelude             Undocumented\n" ++
           "\t    --nobuiltins            Undocumented\n" ++
           "\t -O --level=LEVEL           Undocumented\n" ++
           "\t -i --idrispath=DIR         Add directory to the list of import paths\n" ++
           "\t    --package=ITEM          Undocumented\n" ++
           "\t    --ibcsubdir=FILE        Write IBC files into sub directory\n" ++
           "\t    --codegen=TARGET        Select code generator: C, Java, bytecode,\n" ++
           "\t                            javascript, node, or llvm\n" ++
           "\t    --mvn                   Create a maven project (for Java codegen)\n" ++
           "\t    --cpu=CPU               Select tartget CPU e.g. corei7 or cortex-m3\n" ++
           "\t                            (for LLVM codegen)\n" ++
           "\t    --target=TRIPLE         Select target triple (for llvm codegen)\n" ++
           "\t -S --codegenonly           Do no further compilation of code generator output\n" ++
           "\t -c --compileonly           Compile to object files rather than an executable\n" ++
           "\t -X --extension=ITEM        Undocumented\n" ++
           "\t    --dumpdefuns            Undocumented\n" ++
           "\t    --dumpcases             Undocumented\n" ++
           "\t    --log=LEVEL --loglevel  Debugging log level\n" ++
           "\t    --ideslave              Undocumented\n" ++
           "\t    --client                Undocumented\n" ++
           "\t -h --help                  Display help message\n" ++
           "\t -v --version               Print version information\n" ++
           "\t -V --verbose               Loud verbosity\n" ++
           "\t -q --quiet                 Quiet verbosity\n"


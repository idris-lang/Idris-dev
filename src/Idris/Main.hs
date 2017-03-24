{-|
Module      : Idris.REPL
Description : Main function to decide Idris' mode of use.
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Main
  ( idrisMain
  , idris
  , runMain
  , runClient -- taken from Idris.REPL.
  , loadInputs -- taken from Idris.ModeCommon
  ) where

import Idris.AbsSyntax
import Idris.Core.Execute (execute)
import Idris.Core.TT
import Idris.Elab.Term
import Idris.Elab.Value
import Idris.ElabDecls
import Idris.Error
import Idris.IBC
import Idris.Info
import Idris.ModeCommon
import Idris.Output
import Idris.Parser hiding (indent)
import Idris.REPL
import Idris.REPL.Commands
import Idris.REPL.Parser
import IRTS.CodegenCommon

import Util.System

import Control.Category
import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.State.Strict (execStateT)
import Data.List
import Data.Maybe
import Prelude hiding (id, (.), (<$>))
import System.Console.Haskeline as H
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.IO.CodePage (withCP65001)
import Text.Trifecta.Result (ErrInfo(..), Result(..))

-- | How to run Idris programs.
runMain :: Idris () -> IO ()
runMain prog = withCP65001 $ do
               -- Run in codepage 65001 on Windows so that UTF-8 characters can
               -- be displayed properly. See #3000.
  res <- runExceptT $ execStateT prog idrisInit
  case res of
       Left err -> do
         putStrLn $ "Uncaught error: " ++ show err
         exitFailure
       Right _ -> return ()

-- | The main function of Idris that when given a set of Options will
-- launch Idris into the desired interaction mode either: REPL;
-- Compiler; Script execution; or IDE Mode.
idrisMain :: [Opt] -> Idris ()
idrisMain opts =
  do   mapM_ setWidth (opt getConsoleWidth opts)
       let inputs = opt getFile opts
       let quiet = Quiet `elem` opts
       let nobanner = NoBanner `elem` opts
       let idesl = Idemode `elem` opts || IdemodeSocket `elem` opts
       let runrepl = not (NoREPL `elem` opts)
       let output = opt getOutput opts
       let ibcsubdir = opt getIBCSubDir opts
       let importdirs = opt getImportDir opts
       let sourcedirs = opt getSourceDir opts
       setSourceDirs sourcedirs
       let bcs = opt getBC opts
       let pkgdirs = opt getPkgDir opts
       -- Set default optimisations
       let optimise = case opt getOptLevel opts of
                        [] -> 1
                        xs -> last xs

       setOptLevel optimise
       let outty = case opt getOutputTy opts of
                     [] -> if Interface `elem` opts then
                              Object else Executable
                     xs -> last xs
       let cgn = case opt getCodegen opts of
                   [] -> Via IBCFormat "c"
                   xs -> last xs
       let cgFlags = opt getCodegenArgs opts

       -- Now set/unset specifically chosen optimisations
       let os = opt getOptimisation opts

       mapM_ processOptimisation os

       script <- case opt getExecScript opts of
                   []     -> return Nothing
                   x:y:xs -> do iputStrLn "More than one interpreter expression found."
                                runIO $ exitWith (ExitFailure 1)
                   [expr] -> return (Just expr)
       let immediate = opt getEvalExpr opts
       let port = case getPort opts of
                    Nothing -> ListenPort defaultPort
                    Just p  -> p

       when (DefaultTotal `elem` opts) $ do i <- getIState
                                            putIState (i { default_total = DefaultCheckingTotal })
       tty <- runIO isATTY
       setColourise $ not quiet && last (tty : opt getColour opts)



       mapM_ addLangExt (opt getLanguageExt opts)
       setREPL runrepl
       setQuiet (quiet || isJust script || not (null immediate))

       setCmdLine opts
       setOutputTy outty
       setNoBanner nobanner
       setCodegen cgn
       mapM_ (addFlag cgn) cgFlags
       mapM_ makeOption opts
       vlevel <- verbose
       when (runrepl && vlevel == 0) $ setVerbose 1

       -- if we have the --bytecode flag, drop into the bytecode assembler
       case bcs of
         [] -> return ()
         xs -> return () -- runIO $ mapM_ bcAsm xs
       case ibcsubdir of
         [] -> setIBCSubDir ""
         (d:_) -> setIBCSubDir d
       setImportDirs importdirs

       setNoBanner nobanner

       -- Check if listed packages are actually installed

       idrisCatch (do ipkgs <- runIO $ getIdrisInstalledPackages
                      let diff_pkgs = (\\) pkgdirs ipkgs

                      when (not $ null diff_pkgs) $ do
                        iputStrLn "The following packages were specified but cannot be found:"
                        iputStr $ unlines $ map (\x -> unwords ["-", x]) diff_pkgs
                        runIO $ exitWith (ExitFailure 1))
                  (\e -> return ())

       when (not (NoBasePkgs `elem` opts)) $ do
           addPkgDir "prelude"
           addPkgDir "base"

       mapM_ addPkgDir pkgdirs
       elabPrims
       when (not (NoBuiltins `elem` opts)) $ do x <- loadModule "Builtins" (IBC_REPL True)
                                                addAutoImport "Builtins"
                                                return ()
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule "Prelude" (IBC_REPL True)
                                               addAutoImport "Prelude"
                                               return ()
       when (runrepl && not idesl) initScript

       nobanner <- getNoBanner

       when (runrepl &&
             not quiet &&
             not idesl &&
             not (isJust script) &&
             not nobanner &&
             null immediate) $
         iputStrLn banner

       orig <- getIState

       mods <- if idesl then return [] else loadInputs inputs Nothing
       let efile = case inputs of
                        [] -> ""
                        (f:_) -> f

       runIO $ hSetBuffering stdout LineBuffering

       ok <- noErrors
       when ok $ case output of
                    [] -> return ()
                    (o:_) -> idrisCatch (process "" (Compile cgn o))
                               (\e -> do ist <- getIState ; iputStrLn $ pshow ist e)

       case immediate of
         [] -> return ()
         exprs -> do setWidth InfinitelyWide
                     mapM_ (\str -> do ist <- getIState
                                       c <- colourise
                                       case parseExpr ist str of
                                         Failure (ErrInfo err _) -> do iputStrLn $ show (fixColour c err)
                                                                       runIO $ exitWith (ExitFailure 1)
                                         Success e -> process "" (Eval e))
                           exprs
                     runIO exitSuccess


       case script of
         Nothing -> return ()
         Just expr -> execScript expr

       -- Create Idris data dir + repl history and config dir
       idrisCatch (do dir <- runIO $ getIdrisUserDataDir
                      exists <- runIO $ doesDirectoryExist dir
                      unless exists $ logLvl 1 ("Creating " ++ dir)
                      runIO $ createDirectoryIfMissing True (dir </> "repl"))
         (\e -> return ())

       historyFile <- runIO $ getIdrisHistoryFile

       when ok $ case opt getPkgIndex opts of
                      (f : _) -> writePkgIndex f
                      _ -> return ()

       when (runrepl && not idesl) $ do
--          clearOrigPats
         case port of
           DontListen -> return ()
           ListenPort port' -> startServer port' orig mods
         runInputT (replSettings (Just historyFile)) $ repl (force orig) mods efile
       let idesock = IdemodeSocket `elem` opts
       when (idesl) $ idemodeStart idesock orig inputs
       ok <- noErrors
       when (not ok) $ runIO (exitWith (ExitFailure 1))
  where
    makeOption (OLogging i)     = setLogLevel i
    makeOption (OLogCats cs)    = setLogCats cs
    makeOption (Verbose v)      = setVerbose v
    makeOption TypeCase         = setTypeCase True
    makeOption TypeInType       = setTypeInType True
    makeOption NoCoverage       = setCoverage False
    makeOption ErrContext       = setErrContext True
    makeOption (IndentWith n)   = setIndentWith n
    makeOption (IndentClause n) = setIndentClause n
    makeOption _                = return ()

    processOptimisation :: (Bool,Optimisation) -> Idris ()
    processOptimisation (True,  p) = addOptimise p
    processOptimisation (False, p) = removeOptimise p

    addPkgDir :: String -> Idris ()
    addPkgDir p = do ddir <- runIO getIdrisLibDir
                     addImportDir (ddir </> p)
                     addIBC (IBCImportDir (ddir </> p))



-- | Invoke as if from command line. It is an error if there are
-- unresolved totality problems.
idris :: [Opt] -> IO (Maybe IState)
idris opts = do res <- runExceptT $ execStateT totalMain idrisInit
                case res of
                  Left err -> do putStrLn $ pshow idrisInit err
                                 return Nothing
                  Right ist -> return (Just ist)
    where totalMain = do idrisMain opts
                         ist <- getIState
                         case idris_totcheckfail ist of
                           ((fc, msg):_) -> ierror . At fc . Msg $ "Could not build: "++  msg
                           [] -> return ()


-- | Execute the provided Idris expression.
execScript :: String -> Idris ()
execScript expr = do i <- getIState
                     c <- colourise
                     case parseExpr i expr of
                          Failure (ErrInfo err _) -> do iputStrLn $ show (fixColour c err)
                                                        runIO $ exitWith (ExitFailure 1)
                          Success term -> do ctxt <- getContext
                                             (tm, _) <- elabVal (recinfo (fileFC "toplevel")) ERHS term
                                             res <- execute tm
                                             runIO $ exitSuccess

-- | Run the initialisation script
initScript :: Idris ()
initScript = do script <- runIO $ getIdrisInitScript
                idrisCatch (do go <- runIO $ doesFileExist script
                               when go $ do
                                 h <- runIO $ openFile script ReadMode
                                 runInit h
                                 runIO $ hClose h)
                           (\e -> iPrintError $ "Error reading init file: " ++ show e)
    where runInit :: Handle -> Idris ()
          runInit h = do eof <- lift . lift $ hIsEOF h
                         ist <- getIState
                         unless eof $ do
                           line <- runIO $ hGetLine h
                           script <- runIO $ getIdrisInitScript
                           c <- colourise
                           processLine ist line script c
                           runInit h
          processLine i cmd input clr =
              case parseCmd i input cmd of
                   Failure (ErrInfo err _) -> runIO $ print (fixColour clr err)
                   Success (Right Reload) -> iPrintError "Init scripts cannot reload the file"
                   Success (Right (Load f _)) -> iPrintError "Init scripts cannot load files"
                   Success (Right (ModImport f)) -> iPrintError "Init scripts cannot import modules"
                   Success (Right Edit) -> iPrintError "Init scripts cannot invoke the editor"
                   Success (Right Proofs) -> proofs i
                   Success (Right Quit) -> iPrintError "Init scripts cannot quit Idris"
                   Success (Right cmd ) -> process [] cmd
                   Success (Left err) -> runIO $ print err

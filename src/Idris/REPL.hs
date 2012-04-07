{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Idris.REPL where

import Idris.AbsSyntax
import Idris.REPLParser
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Error
import Idris.Delaborate
import Idris.Compiler
import Idris.Prover
import Idris.Parser
import Idris.Coverage
import Paths_idris

import Core.Evaluate
import Core.ProofShell
import Core.TT
import Core.Constraints

import System.Console.Haskeline as H
import System.FilePath
import System.Environment
import System.Process
import System.Directory
import System.IO
import Control.Monad
import Control.Monad.State
import Data.List
import Data.Char
import Data.Version

repl :: IState -> [FilePath] -> Idris ()
repl orig mods
   = H.catch
      (do let prompt = mkPrompt mods
          x <- lift $ getInputLine (prompt ++ "> ")
          case x of
              Nothing -> do iputStrLn "Bye bye"
                            return ()
              Just input -> H.catch 
                              (do ms <- processInput input orig mods
                                  case ms of
                                      Just mods -> repl orig mods
                                      Nothing -> return ())
                              ctrlC)
      ctrlC
   where ctrlC :: SomeException -> Idris ()
         ctrlC e = do iputStrLn (show e)
                      repl orig mods

mkPrompt [] = "Idris"
mkPrompt [x] = "*" ++ dropExtension x
mkPrompt (x:xs) = "*" ++ dropExtension x ++ " " ++ mkPrompt xs

lit f = case splitExtension f of
            (_, ".lidr") -> True
            _ -> False

processInput :: String -> IState -> [FilePath] -> Idris (Maybe [FilePath])
processInput cmd orig inputs
    = do i <- get
         let fn = case inputs of
                        (f:_) -> f
                        _ -> ""
         case parseCmd i cmd of
                Left err ->   do liftIO $ print err
                                 return (Just inputs)
                Right Reload -> do put (orig { idris_options = idris_options i })
                                   clearErr
                                   mods <- mapM loadModule inputs  
                                   return (Just inputs)
                Right Edit -> do edit fn orig
                                 return (Just inputs)
                Right AddProof -> do idrisCatch (addProof fn orig)
                                                (\e -> iputStrLn (show e))
                                     return (Just inputs)
                Right Quit -> do iputStrLn "Bye bye"
                                 return Nothing
                Right cmd  -> do idrisCatch (process fn cmd)
                                            (\e -> iputStrLn (show e))
                                 return (Just inputs)

edit :: FilePath -> IState -> Idris ()
edit "" orig = iputStrLn "Nothing to edit"
edit f orig
    = do i <- get
         env <- liftIO $ getEnvironment
         let editor = getEditor env
         let line = case errLine i of
                        Just l -> " +" ++ show l ++ " "
                        Nothing -> " "
         let cmd = editor ++ line ++ f
         liftIO $ system cmd
         clearErr
         put (orig { idris_options = idris_options i })
         loadModule f
         iucheck
         return ()
   where getEditor env | Just ed <- lookup "EDITOR" env = ed
                       | Just ed <- lookup "VISUAL" env = ed
                       | otherwise = "vi"

addProof :: FilePath -> IState -> Idris ()
addProof "" orig = iputStrLn "Nothing to add to"
addProof f orig
    = do let fb = f ++ "~"
         liftIO $ copyFile f fb -- make a backup in case something goes wrong!
         prog <- liftIO $ readFile fb
         i <- get
         case last_proof i of
            Nothing -> iputStrLn "No proof to add"
            Just (n, p) -> do let prog' = insertScript (showProof (lit f) n p) (lines prog)
                              liftIO $ writeFile f (unlines prog')
                              iputStrLn $ "Added proof " ++ show n
                              put (i { last_proof = Nothing })
                              -- lift $ removeFile fb -- uncomment when less scared :)

insertScript :: String -> [String] -> [String]
insertScript prf [] = "\n---------- Proofs ----------" : "" : [prf]
insertScript prf (p@"---------- Proofs ----------" : "" : xs) 
    = p : "" : prf : xs
insertScript prf (x : xs) = x : insertScript prf xs

process :: FilePath -> Command -> Idris ()
process fn Help = iputStrLn displayHelp
process fn (Eval t) 
                 = do (tm, ty) <- elabVal toplevel False t
                      ctxt <- getContext
                      ist <- get 
                      let tm' = normaliseAll ctxt [] tm
                      let ty' = normaliseAll ctxt [] ty
                      logLvl 3 $ "Raw: " ++ show (tm', ty')
                      imp <- impShow
                      iputStrLn (showImp imp (delab ist tm') ++ " : " ++ 
                                 showImp imp (delab ist ty'))
process fn (ExecVal t) 
                    = do (tm, ty) <- elabVal toplevel False t 
--                                         (PApp fc (PRef fc (NS (UN "print") ["prelude"]))
--                                                           [pexp t])
                         (tmpn, tmph) <- liftIO tempfile
                         liftIO $ hClose tmph
                         compile tmpn tm
                         liftIO $ system tmpn
                         return ()
    where fc = FC "(input)" 0 
process fn (Check (PRef _ n))
                  = do ctxt <- getContext
                       ist <- get
                       imp <- impShow
                       case lookupTy Nothing n ctxt of
                        ts@(_:_) -> mapM_ (\t -> iputStrLn $ show n ++ " : " ++
                                                       showImp imp (delab ist t)) ts
                        [] -> iputStrLn $ "No such variable " ++ show n
process fn (Check t) = do (tm, ty) <- elabVal toplevel False t
                          ctxt <- getContext
                          ist <- get 
                          imp <- impShow
                          let ty' = normaliseC ctxt [] ty
                          iputStrLn (showImp imp (delab ist tm) ++ " : " ++ 
                                    showImp imp (delab ist ty))
process fn Universes = do i <- get
                          let cs = idris_constraints i
--                        iputStrLn $ showSep "\n" (map show cs)
                          liftIO $ print (map fst cs)
                          let n = length cs
                          iputStrLn $ "(" ++ show n ++ " constraints)"
                          case ucheck cs of
                            Error e -> iputStrLn $ pshow i e
                            OK _ -> iputStrLn "Universes OK"
process fn (Defn n) = do i <- get
                         iputStrLn "Compiled patterns:\n"
                         liftIO $ print (lookupDef Nothing n (tt_ctxt i))
                         case lookupCtxt Nothing n (idris_patdefs i) of
                            [] -> return ()
                            [d] -> do iputStrLn "Original definiton:\n"
                                      mapM_ (printCase i) d
                         case lookupTotal n (tt_ctxt i) of
                            [t] -> iputStrLn (showTotal t i)
                            _ -> return ()
    where printCase i (lhs, rhs) = do liftIO $ putStr $ showImp True (delab i lhs)
                                      liftIO $ putStr " = "
                                      liftIO $ putStrLn $ showImp True (delab i rhs)
process fn (TotCheck n) = do i <- get
                             case lookupTotal n (tt_ctxt i) of
                                [t] -> iputStrLn (showTotal t i)
                                _ -> return ()
process fn (DebugInfo n) 
                    = do i <- get
                         let oi = lookupCtxtName Nothing n (idris_optimisation i)
                         when (not (null oi)) $ iputStrLn (show oi)
                         let si = lookupCtxt Nothing n (idris_statics i)
                         when (not (null si)) $ iputStrLn (show si)
process fn (Info n) = do i <- get
                         case lookupCtxt Nothing n (idris_classes i) of
                              [c] -> classInfo c
                              _ -> iputStrLn "Not a class"
process fn (Search t) = iputStrLn "Not implemented"
process fn (Spec t) = do (tm, ty) <- elabVal toplevel False t
                         ctxt <- getContext
                         ist <- get
                         let tm' = specialise ctxt [] [] {- (idris_statics ist) -} tm
                         iputStrLn (show (delab ist tm'))
process fn (Prove n) = do prover (lit fn) n
                          -- recheck totality
                          i <- get
                          totcheck (FC "(input)" 0, n)
                          mapM_ (\ (f,n) -> setTotality n Unchecked) (idris_totcheck i)
                          mapM_ checkDeclTotality (idris_totcheck i)
process fn (HNF t)  = do (tm, ty) <- elabVal toplevel False t
                         ctxt <- getContext
                         ist <- get
                         let tm' = simplify ctxt [] tm
                         iputStrLn (show (delab ist tm'))
process fn TTShell  = do ist <- get
                         let shst = initState (tt_ctxt ist)
                         shst' <- lift $ runShell shst
                         return ()
process fn Execute = do (m, _) <- elabVal toplevel False 
                                        (PApp fc 
                                           (PRef fc (UN "run__IO"))
                                           [pexp $ PRef fc (NS (UN "main") ["main"])])
--                                      (PRef (FC "main" 0) (NS (UN "main") ["main"]))
                        (tmpn, tmph) <- liftIO tempfile
                        liftIO $ hClose tmph
                        compile tmpn m
                        liftIO $ system tmpn
                        return ()
  where fc = FC "main" 0                     
process fn (Compile f) = do (m, _) <- elabVal toplevel False
                                        (PApp fc 
                                           (PRef fc (UN "run__IO"))
                                           [pexp $ PRef fc (NS (UN "main") ["main"])])
                            compile f m
  where fc = FC "main" 0                     
process fn (LogLvl i) = setLogLevel i 
process fn Metavars 
                 = do ist <- get
                      let mvs = idris_metavars ist \\ primDefs
                      case mvs of
                        [] -> iputStrLn "No global metavariables to solve"
                        _ -> iputStrLn $ "Global metavariables:\n\t" ++ show mvs
process fn NOP      = return ()

classInfo :: ClassInfo -> Idris ()
classInfo ci = do iputStrLn "Methods:\n"
                  mapM_ dumpMethod (class_methods ci)
                  iputStrLn ""
                  iputStrLn "Instances:\n"
                  mapM_ dumpInstance (class_instances ci)

dumpMethod :: (Name, (FnOpts, PTerm)) -> Idris ()
dumpMethod (n, (_, t)) = iputStrLn $ show n ++ " : " ++ show t

dumpInstance :: Name -> Idris ()
dumpInstance n = do i <- get
                    ctxt <- getContext
                    imp <- impShow
                    case lookupTy Nothing n ctxt of
                         ts -> mapM_ (\t -> iputStrLn $ showImp imp (delab i t)) ts

showTotal t@(Partial (Other ns)) i
   = show t ++ "\n\t" ++ showSep "\n\t" (map (showTotalN i) ns)
showTotal t i = show t
showTotalN i n = case lookupTotal n (tt_ctxt i) of
                        [t] -> showTotal t i
                        _ -> ""

displayHelp = let vstr = showVersion version in
              "\nIdris version " ++ vstr ++ "\n" ++
              "--------------" ++ map (\x -> '-') vstr ++ "\n\n" ++
              concatMap cmdInfo help
  where cmdInfo (cmds, args, text) = "   " ++ col 16 12 (showSep " " cmds) args text 
        col c1 c2 l m r = 
            l ++ take (c1 - length l) (repeat ' ') ++ 
            m ++ take (c2 - length m) (repeat ' ') ++ r ++ "\n"

help =
  [ (["Command"], "Arguments", "Purpose"),
    ([""], "", ""),
    (["<expr>"], "", "Evaluate an expression"),
    ([":t"], "<expr>", "Check the type of an expression"),
    ([":i", ":info"], "<name>", "Display information about a type class"),
    ([":total"], "<name>", "Check the totality of a name"),
    ([":r",":reload"], "", "Reload current file"),
    ([":e",":edit"], "", "Edit current file using $EDITOR or $VISUAL"),
    ([":m",":metavars"], "", "Show remaining proof obligations (metavariables)"),
    ([":p",":prove"], "<name>", "Prove a metavariable"),
    ([":a",":addproof"], "", "Add last proof to source file"),
    ([":c",":compile"], "<filename>", "Compile to an executable <filename>"),
    ([":exec",":execute"], "", "Compile to an executable and run"),
    ([":?",":h",":help"], "", "Display this help text"),
    ([":q",":quit"], "", "Exit the Idris system")
  ]


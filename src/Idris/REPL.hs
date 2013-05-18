{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards, CPP #-}

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
import Idris.Primitives
import Idris.Coverage
import Idris.UnusedArgs
import Idris.Docs
import Idris.Help
import Idris.Completion
import Idris.IdeSlave

import Paths_idris
import Util.System
import Util.DynamicLinker

import Core.Evaluate
import Core.Execute (execute)
import Core.ProofShell
import Core.TT
import Core.Constraints

import IRTS.Compiler
import IRTS.LParser
import IRTS.CodegenCommon

-- import RTS.SC
-- import RTS.Bytecode
-- import RTS.PreC
-- import RTS.CodegenC
#ifdef IDRIS_LLVM
import LLVM.General.Target
#else
import Util.LLVMStubs
#endif
import System.Console.Haskeline as H
import System.FilePath
import System.Exit
import System.Environment
import System.Process
import System.Directory
import System.IO
import Control.Monad
import Control.Monad.Trans.State.Strict ( StateT, execStateT, get, put )
import Control.Monad.Trans ( liftIO, lift )
import Data.Maybe
import Data.List
import Data.Char
import Data.Version

import Debug.Trace

-- | Run the REPL
repl :: IState -- ^ The initial state
     -> [FilePath] -- ^ The loaded modules
     -> InputT Idris ()
repl orig mods
   = H.catch
      (do let quiet = opt_quiet (idris_options orig)
          let prompt = if quiet
                          then ""
                          else mkPrompt mods ++ "> "
          x <- getInputLine prompt
          case x of
              Nothing -> do lift $ when (not quiet) (iputStrLn "Bye bye")
                            return ()
              Just input -> H.catch 
                              (do ms <- lift $ processInput input orig mods
                                  case ms of
                                      Just mods -> repl orig mods
                                      Nothing -> return ())
                              ctrlC)
      ctrlC
   where ctrlC :: SomeException -> InputT Idris ()
         ctrlC e = do lift $ iputStrLn (show e)
                      repl orig mods

-- | Run the IdeSlave
ideslaveStart :: IState -> [FilePath] -> Idris ()
ideslaveStart orig mods
  = do i <- getIState
       case idris_outputmode i of
         IdeSlave n ->
           when (mods /= []) (do isetPrompt (mkPrompt mods))
       ideslave orig mods


ideslave :: IState -> [FilePath] -> Idris ()
ideslave orig mods
  = do idrisCatch
         (do l <- liftIO $ getLine
             let (sexp, id) = parseMessage l
             i <- getIState
             putIState $ i { idris_outputmode = (IdeSlave id) }
             case sexpToCommand sexp of
               Just (Interpret cmd) ->
                 do let fn = case mods of
                                 (f:_) -> f
                                 _ -> ""
                    case parseCmd i cmd of
                         Left err -> iFail $ show err
                         Right (Prove n') -> do iResult ""
                                                liftIO $ putStrLn $ convSExp "proof-mode" (True, n') id
                                                idrisCatch
                                                  (do process fn (Prove n'))
                                                  (\e -> do iFail $ show e)
                                                i <- getIState
                                                case (idris_outputmode i) of
                                                  IdeSlave id -> liftIO $ putStrLn $ convSExp "proof-mode" (False, n') id
                                                isetPrompt (mkPrompt mods)
                         Right cmd -> idrisCatch
                                        (do ideslaveProcess fn cmd)
                                        (\e -> do iFail $ show e)
               Just (REPLCompletions str) ->
                 do (unused, compls) <- replCompletion (reverse str, "")
                    let good = SexpList [SymbolAtom "ok", toSExp (map replacement compls, reverse unused)]
                    liftIO $ putStrLn $ convSExp "return" good id
               Just (LoadFile filename) ->
                 do clearErr
                    putIState (orig { idris_options = idris_options i,
                                      idris_outputmode = (IdeSlave id) })
                    loadModule filename
                    iucheck
                    isetPrompt (mkPrompt [filename])
                    -- report success! or failure!
                    ideslave orig [filename]
               Nothing -> do iFail "did not understand")
         (\e -> do iFail $ show e)
       ideslave orig mods

ideslaveProcess :: FilePath -> Command -> Idris ()
ideslaveProcess fn Help = process fn Help
ideslaveProcess fn (ChangeDirectory f) = do process fn (ChangeDirectory f)
                                            iResult "changed directory to"
ideslaveProcess fn (Eval t) = process fn (Eval t)
ideslaveProcess fn (ExecVal t) = process fn (ExecVal t)
ideslaveProcess fn (Check (PRef x n)) = process fn (Check (PRef x n))
ideslaveProcess fn (Check t) = process fn (Check t)
ideslaveProcess fn (DocStr n) = process fn (DocStr n)
ideslaveProcess fn Universes = process fn Universes
ideslaveProcess fn (Defn n) = do process fn (Defn n)
                                 iResult ""
ideslaveProcess fn (TotCheck n) = process fn (TotCheck n)
ideslaveProcess fn (DebugInfo n) = do process fn (DebugInfo n)
                                      iResult ""
ideslaveProcess fn (Info n) = process fn (Info n)
ideslaveProcess fn (Search t) = process fn (Search t)
ideslaveProcess fn (Spec t) = process fn (Spec t)
-- RmProof and AddProof not supported!
ideslaveProcess fn (ShowProof n') = process fn (ShowProof n')
ideslaveProcess fn (HNF t) = process fn (HNF t)
--ideslaveProcess fn TTShell = process fn TTShell -- need some prove mode!

--that most likely does not work, since we need to wrap
--input/output of the executed binary...
ideslaveProcess fn Execute = do process fn Execute
                                iResult ""
ideslaveProcess fn (NewCompile f) = do process fn (NewCompile f)
                                       iResult ""
ideslaveProcess fn (Compile codegen f) = do process fn (Compile codegen f)
                                            iResult ""
ideslaveProcess fn (LogLvl i) = do process fn (LogLvl i)
                                   iResult ""
ideslaveProcess fn (Pattelab t) = process fn (Pattelab t)
ideslaveProcess fn (Missing n) = process fn (Missing n)
ideslaveProcess fn (DynamicLink l) = do process fn (DynamicLink l)
                                        iResult ""
ideslaveProcess fn ListDynamic = do process fn ListDynamic
                                    iResult ""
ideslaveProcess fn Metavars = process fn Metavars
ideslaveProcess fn (SetOpt ErrContext) = do process fn (SetOpt ErrContext)
                                            iResult ""
ideslaveProcess fn (UnsetOpt ErrContext) = do process fn (UnsetOpt ErrContext)
                                              iResult ""
ideslaveProcess fn (SetOpt ShowImpl) = do process fn (SetOpt ShowImpl)
                                          iResult ""
ideslaveProcess fn (UnsetOpt ShowImpl) = do process fn (UnsetOpt ShowImpl)
                                            iResult ""
ideslaveProcess fn (SetOpt x) = process fn (SetOpt x)
ideslaveProcess fn (UnsetOpt x) = process fn (UnsetOpt x)
ideslaveProcess fn _ = iFail "command not recognized or not supported"


-- | The prompt consists of the currently loaded modules, or "Idris" if there are none
mkPrompt [] = "Idris"
mkPrompt [x] = "*" ++ dropExtension x
mkPrompt (x:xs) = "*" ++ dropExtension x ++ " " ++ mkPrompt xs

-- | Determine whether a file uses literate syntax
lit f = case splitExtension f of
            (_, ".lidr") -> True
            _ -> False

processInput :: String -> IState -> [FilePath] -> Idris (Maybe [FilePath])
processInput cmd orig inputs
    = do i <- getIState
         let opts = idris_options i
         let quiet = opt_quiet opts
         let fn = case inputs of
                        (f:_) -> f
                        _ -> ""
         case parseCmd i cmd of
            Left err ->   do liftIO $ print err
                             return (Just inputs)
            Right Reload -> 
                do putIState (orig { idris_options = idris_options i })
                   clearErr
                   mods <- mapM loadModule inputs  
                   return (Just inputs)
            Right (Load f) -> 
                do putIState (orig { idris_options = idris_options i })
                   clearErr
                   mod <- loadModule f
                   return (Just [f])
            Right (ModImport f) -> 
                do clearErr
                   fmod <- loadModule f
                   return (Just (inputs ++ [fmod]))
            Right Edit -> do edit fn orig
                             return (Just inputs)
            Right Proofs -> do proofs orig
                               return (Just inputs)
            Right Quit -> do when (not quiet) (iputStrLn "Bye bye")
                             return Nothing
            Right cmd  -> do idrisCatch (process fn cmd)
                                        (\e -> iputStrLn (show e))
                             return (Just inputs)

resolveProof :: Name -> Idris Name
resolveProof n'
  = do i <- getIState
       ctxt <- getContext
       n <- case lookupNames n' ctxt of
                 [x] -> return x
                 [] -> return n'
                 ns -> fail $ pshow i (CantResolveAlts (map show ns))
       return n

removeProof :: Name -> Idris ()
removeProof n =
  do i <- getIState
     let proofs = proof_list i
     let ps = filter ((/= n) . fst) proofs
     putIState $ i { proof_list = ps }

edit :: FilePath -> IState -> Idris ()
edit "" orig = iputStrLn "Nothing to edit"
edit f orig
    = do i <- getIState
         env <- liftIO $ getEnvironment
         let editor = getEditor env
         let line = case errLine i of
                        Just l -> " +" ++ show l ++ " "
                        Nothing -> " "
         let cmd = editor ++ line ++ f
         liftIO $ system cmd
         clearErr
         putIState (orig { idris_options = idris_options i })
         loadModule f
         iucheck
         return ()
   where getEditor env | Just ed <- lookup "EDITOR" env = ed
                       | Just ed <- lookup "VISUAL" env = ed
                       | otherwise = "vi"


proofs :: IState -> Idris ()
proofs orig
  = do i <- getIState
       let ps = proof_list i
       case ps of
            [] -> iputStrLn "No proofs available"
            _  -> iputStrLn $ "Proofs:\n\t" ++ (show $ map fst ps)

insertScript :: String -> [String] -> [String]
insertScript prf [] = "\n---------- Proofs ----------" : "" : [prf]
insertScript prf (p@"---------- Proofs ----------" : "" : xs)
    = p : "" : prf : xs
insertScript prf (x : xs) = x : insertScript prf xs

process :: FilePath -> Command -> Idris ()
process fn Help = iResult displayHelp
process fn (ChangeDirectory f)
                 = do liftIO $ setCurrentDirectory f
                      return ()
process fn (Eval t)
                 = do (tm, ty) <- elabVal toplevel False t
                      ctxt <- getContext
                      ist <- getIState
                      let tm' = normaliseAll ctxt [] tm
                      let ty' = normaliseAll ctxt [] ty
                      logLvl 3 $ "Raw: " ++ show (tm', ty')
                      imp <- impShow
                      iResult (showImp imp (delab ist tm') ++ " : " ++
                               showImp imp (delab ist ty'))
process fn (ExecVal t)
                  = do ctxt <- getContext
                       ist <- getIState
                       (tm, ty) <- elabVal toplevel False t
--                       let tm' = normaliseAll ctxt [] tm
                       let ty' = normaliseAll ctxt [] ty
                       res <- execute tm
                       imp <- impShow
                       iResult (showImp imp (delab ist res) ++ " : " ++
                                showImp imp (delab ist ty'))
process fn (Check (PRef _ n))
   = do ctxt <- getContext
        ist <- getIState
        imp <- impShow
        case lookupNames n ctxt of
             ts@(_:_) -> do mapM_ (\n -> iputStrLn $ show n ++ " : " ++
                                         showImp imp (delabTy ist n)) ts
                            iResult ""
             [] -> iFail $ "No such variable " ++ show n
process fn (Check t) = do (tm, ty) <- elabVal toplevel False t
                          ctxt <- getContext
                          ist <- getIState
                          imp <- impShow
                          let ty' = normaliseC ctxt [] ty
                          iResult (showImp imp (delab ist tm) ++ " : " ++
                                   showImp imp (delab ist ty))

process fn (DocStr n) = do i <- getIState
                           case lookupCtxtName n (idris_docstrings i) of
                                [] -> iFail $ "No documentation for " ++ show n
                                ns -> do mapM_ showDoc ns
                                         iResult ""
    where showDoc (n, d)
             = do doc <- getDocs n
                  iputStrLn $ show doc
process fn Universes = do i <- getIState
                          let cs = idris_constraints i
--                        iputStrLn $ showSep "\n" (map show cs)
                          iputStrLn $ show (map fst cs)
                          let n = length cs
                          iputStrLn $ "(" ++ show n ++ " constraints)"
                          case ucheck cs of
                            Error e -> iFail $ pshow i e
                            OK _ -> iResult "Universes OK"
process fn (Defn n) = do i <- getIState
                         iputStrLn "Compiled patterns:\n"
                         iputStrLn $ show (lookupDef n (tt_ctxt i))
                         case lookupCtxt n (idris_patdefs i) of
                            [] -> return ()
                            [(d, _)] -> do iputStrLn "Original definiton:\n"
                                           mapM_ (printCase i) d
                         case lookupTotal n (tt_ctxt i) of
                            [t] -> iputStrLn (showTotal t i)
                            _ -> return ()
    where printCase i (_, lhs, rhs)
             = do iputStrLn (showImp True (delab i lhs) ++ " = " ++
                             showImp True (delab i rhs))
process fn (TotCheck n) = do i <- getIState
                             case lookupTotal n (tt_ctxt i) of
                                [t] -> iResult (showTotal t i)
                                _ -> do iFail ""
                                        return ()
process fn (DebugInfo n)
   = do i <- getIState
        let oi = lookupCtxtName n (idris_optimisation i)
        when (not (null oi)) $ iputStrLn (show oi)
        let si = lookupCtxt n (idris_statics i)
        when (not (null si)) $ iputStrLn (show si)
        let di = lookupCtxt n (idris_datatypes i)
        when (not (null di)) $ iputStrLn (show di)
        let d = lookupDef n (tt_ctxt i)
        when (not (null d)) $ iputStrLn $ "Definition: " ++ (show (head d))
        let cg = lookupCtxtName n (idris_callgraph i)
        findUnusedArgs (map fst cg)
        i <- getIState
        let cg' = lookupCtxtName n (idris_callgraph i)
        sc <- checkSizeChange n
        iputStrLn $ "Size change: " ++ show sc
        when (not (null cg')) $ do iputStrLn "Call graph:\n"
                                   iputStrLn (show cg')
process fn (Info n) = do i <- getIState
                         case lookupCtxt n (idris_classes i) of
                              [c] -> classInfo c
                              _ -> iFail "Not a class"
process fn (Search t) = iFail "Not implemented"
process fn (Spec t) = do (tm, ty) <- elabVal toplevel False t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = simplify ctxt True [] {- (idris_statics ist) -} tm
                         iResult (show (delab ist tm'))

process fn (RmProof n')
  = do i <- getIState
       n <- resolveProof n'
       let proofs = proof_list i
       case lookup n proofs of
            Nothing -> iputStrLn "No proof to remove"
            Just _  -> do removeProof n
                          insertMetavar n
                          iputStrLn $ "Removed proof " ++ show n
                          where
                            insertMetavar :: Name -> Idris ()
                            insertMetavar n =
                              do i <- getIState
                                 let ms = idris_metavars i
                                 putIState $ i { idris_metavars = n : ms }

process fn' (AddProof prf)
  = do fn <- do
         ex <- liftIO $ doesFileExist fn'
         let fnExt = fn' <.> "idr"
         exExt <- liftIO $ doesFileExist fnExt
         if ex
            then return fn'
            else if exExt
                    then return fnExt
                    else fail $ "Neither \""++fn'++"\" nor \""++fnExt++"\" exist"
       let fb = fn ++ "~"
       liftIO $ copyFile fn fb -- make a backup in case something goes wrong!
       prog <- liftIO $ readFile fb
       i <- getIState
       let proofs = proof_list i
       n' <- case prf of
                Nothing -> case proofs of
                             [] -> fail "No proof to add"
                             ((x, p) : _) -> return x
                Just nm -> return nm
       n <- resolveProof n'
       case lookup n proofs of
            Nothing -> iputStrLn "No proof to add"
            Just p  -> do let prog' = insertScript (showProof (lit fn) n p) ls
                          liftIO $ writeFile fn (unlines prog')
                          removeProof n
                          iputStrLn $ "Added proof " ++ show n
                          where ls = (lines prog)

process fn (ShowProof n')
  = do i <- getIState
       n <- resolveProof n'
       let proofs = proof_list i
       case lookup n proofs of
            Nothing -> iFail "No proof to show"
            Just p  -> iResult $ showProof False n p

process fn (Prove n')
     = do ctxt <- getContext
          ist <- getIState
          n <- case lookupNames n' ctxt of
                    [x] -> return x
                    [] -> return n'
                    ns -> fail $ pshow ist (CantResolveAlts (map show ns))
          prover (lit fn) n
          -- recheck totality
          i <- getIState
          totcheck (FC "(input)" 0, n)
          mapM_ (\ (f,n) -> setTotality n Unchecked) (idris_totcheck i)
          mapM_ checkDeclTotality (idris_totcheck i)

process fn (HNF t)  = do (tm, ty) <- elabVal toplevel False t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = hnf ctxt [] tm
                         iResult (show (delab ist tm'))
process fn TTShell  = do ist <- getIState
                         let shst = initState (tt_ctxt ist)
                         runShell shst
                         return ()
process fn Execute = do (m, _) <- elabVal toplevel False
                                        (PApp fc
                                           (PRef fc (UN "run__IO"))
                                           [pexp $ PRef fc (NS (UN "main") ["Main"])])
--                                      (PRef (FC "main" 0) (NS (UN "main") ["main"]))
                        (tmpn, tmph) <- liftIO tempfile
                        liftIO $ hClose tmph
                        t <- codegen
                        compile t tmpn m
                        liftIO $ system tmpn
                        return ()
  where fc = FC "main" 0
process fn (NewCompile f)
     = do (m, _) <- elabVal toplevel False
                      (PApp fc (PRef fc (UN "run__IO"))
                          [pexp $ PRef fc (NS (UN "main") ["Main"])])
          compileEpic f m
  where fc = FC "main" 0
process fn (Compile codegen f)
      = do (m, _) <- elabVal toplevel False
                       (PApp fc (PRef fc (UN "run__IO"))
                       [pexp $ PRef fc (NS (UN "main") ["Main"])])
           compile codegen f m
  where fc = FC "main" 0
process fn (LogLvl i) = setLogLevel i
-- Elaborate as if LHS of a pattern (debug command)
process fn (Pattelab t)
     = do (tm, ty) <- elabVal toplevel True t
          iResult $ show tm ++ "\n\n : " ++ show ty

process fn (Missing n)
    = do i <- getIState
         case lookupCtxt n (idris_patdefs i) of
                  [] -> return ()
                  [(_, tms)] ->
                       iResult (showSep "\n" (map (showImp True) tms))
                  _ -> iFail $ "Ambiguous name"
process fn (DynamicLink l) = do i <- getIState
                                let lib = trim l
                                handle <- lift $ tryLoadLib lib
                                case handle of
                                  Nothing -> iFail $ "Could not load dynamic lib \"" ++ l ++ "\""
                                  Just x -> do let libs = idris_dynamic_libs i
                                               putIState $ i { idris_dynamic_libs = x:libs }
    where trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
process fn ListDynamic = do i <- getIState
                            iputStrLn "Dynamic libraries:"
                            showLibs $ idris_dynamic_libs i
    where showLibs []                = return ()
          showLibs ((Lib name _):ls) = do iputStrLn $ "\t" ++ name; showLibs ls
process fn Metavars
                 = do ist <- getIState
                      let mvs = idris_metavars ist \\ primDefs
                      case mvs of
                        [] -> iFail "No global metavariables to solve"
                        _ -> iResult $ "Global metavariables:\n\t" ++ show mvs
process fn NOP      = return ()

process fn (SetOpt   ErrContext) = setErrContext True
process fn (UnsetOpt ErrContext) = setErrContext False
process fn (SetOpt ShowImpl)     = setImpShow True
process fn (UnsetOpt ShowImpl)   = setImpShow False

process fn (SetOpt _) = iFail "Not a valid option"
process fn (UnsetOpt _) = iFail "Not a valid option"


classInfo :: ClassInfo -> Idris ()
classInfo ci = do iputStrLn "Methods:\n"
                  mapM_ dumpMethod (class_methods ci)
                  iputStrLn ""
                  iputStrLn "Instances:\n"
                  mapM_ dumpInstance (class_instances ci)
                  iResult ""

dumpMethod :: (Name, (FnOpts, PTerm)) -> Idris ()
dumpMethod (n, (_, t)) = iputStrLn $ show n ++ " : " ++ show t

dumpInstance :: Name -> Idris ()
dumpInstance n = do i <- getIState
                    ctxt <- getContext
                    imp <- impShow
                    case lookupTy n ctxt of
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
              concatMap cmdInfo helphead ++
              concatMap cmdInfo help
  where cmdInfo (cmds, args, text) = "   " ++ col 16 12 (showSep " " cmds) (show args) text 
        col c1 c2 l m r = 
            l ++ take (c1 - length l) (repeat ' ') ++ 
            m ++ take (c2 - length m) (repeat ' ') ++ r ++ "\n"

parseCodegen :: String -> Codegen
parseCodegen "C" = ViaC
parseCodegen "Java" = ViaJava
parseCodegen "bytecode" = Bytecode
parseCodegen "javascript" = ViaJavaScript
parseCodegen "node" = ViaNode
parseCodegen "llvm" = ViaLLVM
parseCodegen _ = error "unknown codegen" -- FIXME: partial function

parseArgs :: [String] -> [Opt]
parseArgs [] = []
parseArgs ("--quiet":ns)         = Quiet : (parseArgs ns)
parseArgs ("--ideslave":ns)      = Ideslave : (parseArgs ns)
parseArgs ("--log":lvl:ns)       = OLogging (read lvl) : (parseArgs ns)
parseArgs ("--noprelude":ns)     = NoPrelude : (parseArgs ns)
parseArgs ("--check":ns)         = NoREPL : (parseArgs ns)
parseArgs ("-o":n:ns)            = NoREPL : Output n : (parseArgs ns)
parseArgs ("-no":n:ns)           = NoREPL : NewOutput n : (parseArgs ns)
parseArgs ("--typecase":ns)      = TypeCase : (parseArgs ns)
parseArgs ("--typeintype":ns)    = TypeInType : (parseArgs ns)
parseArgs ("--total":ns)         = DefaultTotal : (parseArgs ns)
parseArgs ("--partial":ns)       = DefaultPartial : (parseArgs ns)
parseArgs ("--warnpartial":ns)   = WarnPartial : (parseArgs ns)
parseArgs ("--nocoverage":ns)    = NoCoverage : (parseArgs ns)
parseArgs ("--errorcontext":ns)  = ErrContext : (parseArgs ns)
parseArgs ("--help":ns)          = Usage : (parseArgs ns)
parseArgs ("--link":ns)          = ShowLibs : (parseArgs ns)
parseArgs ("--libdir":ns)        = ShowLibdir : (parseArgs ns)
parseArgs ("--include":ns)       = ShowIncs : (parseArgs ns)
parseArgs ("--version":ns)       = Ver : (parseArgs ns)
parseArgs ("--verbose":ns)       = Verbose : (parseArgs ns)
parseArgs ("--ibcsubdir":n:ns)   = IBCSubDir n : (parseArgs ns)
parseArgs ("-i":n:ns)            = ImportDir n : (parseArgs ns)
parseArgs ("--warn":ns)          = WarnOnly : (parseArgs ns)
parseArgs ("--package":n:ns)     = Pkg n : (parseArgs ns)
parseArgs ("-p":n:ns)            = Pkg n : (parseArgs ns)
parseArgs ("--build":n:ns)       = PkgBuild n : (parseArgs ns)
parseArgs ("--install":n:ns)     = PkgInstall n : (parseArgs ns)
parseArgs ("--clean":n:ns)       = PkgClean n : (parseArgs ns)
parseArgs ("--bytecode":n:ns)    = NoREPL : BCAsm n : (parseArgs ns)
parseArgs ("--fovm":n:ns)        = NoREPL : FOVM n : (parseArgs ns)
parseArgs ("-S":ns)              = OutputTy Raw : (parseArgs ns)
parseArgs ("-c":ns)              = OutputTy Object : (parseArgs ns)
parseArgs ("--dumpdefuns":n:ns)  = DumpDefun n : (parseArgs ns)
parseArgs ("--dumpcases":n:ns)   = DumpCases n : (parseArgs ns)
parseArgs ("--codegen":n:ns)     = UseCodegen (parseCodegen n) : (parseArgs ns)
parseArgs ["--exec"]             = InterpretScript "Main.main" : []
parseArgs ("--exec":expr:ns)     = InterpretScript expr : parseArgs ns
parseArgs ("-XTypeProviders":ns) = Extension TypeProviders : (parseArgs ns)
parseArgs ("-O3":ns)             = OptLevel 3 : parseArgs ns
parseArgs ("-O2":ns)             = OptLevel 2 : parseArgs ns
parseArgs ("-O1":ns)             = OptLevel 1 : parseArgs ns
parseArgs ("-O0":ns)             = OptLevel 0 : parseArgs ns
parseArgs ("-O":n:ns)            = OptLevel (read n) : parseArgs ns
parseArgs ("--target":n:ns)      = TargetTriple n : parseArgs ns
parseArgs ("--cpu":n:ns)         = TargetCPU n : parseArgs ns
parseArgs (n:ns)                 = Filename n : (parseArgs ns)

helphead =
  [ (["Command"], SpecialHeaderArg, "Purpose"),
    ([""], NoArg, "")
  ]


replSettings :: Settings Idris
replSettings = setComplete replCompletion defaultSettings

-- invoke as if from command line
idris :: [Opt] -> IO IState
idris opts = execStateT (idrisMain opts) idrisInit

idrisMain :: [Opt] -> Idris ()
idrisMain opts =
    do let inputs = opt getFile opts
       let quiet = Quiet `elem` opts
       let idesl = Ideslave `elem` opts
       let runrepl = not (NoREPL `elem` opts)
       let output = opt getOutput opts
       let newoutput = opt getNewOutput opts
       let ibcsubdir = opt getIBCSubDir opts
       let importdirs = opt getImportDir opts
       let bcs = opt getBC opts
       let vm = opt getFOVM opts
       let pkgdirs = opt getPkgDir opts
       let optimize = case opt getOptLevel opts of
                        [] -> 2
                        xs -> last xs
       trpl <- case opt getTriple opts of
                 [] -> liftIO $ getDefaultTargetTriple
                 xs -> return (last xs)
       tcpu <- case opt getCPU opts of
                 [] -> liftIO $ getHostCPUName
                 xs -> return (last xs)
       let outty = case opt getOutputTy opts of
                     [] -> Executable
                     xs -> last xs
       let cgn = case opt getCodegen opts of
                   [] -> ViaC
                   xs -> last xs
       script <- case opt getExecScript opts of
                   []     -> return Nothing
                   x:y:xs -> do iputStrLn "More than one interpreter expression found."
                                liftIO $ exitWith (ExitFailure 1)
                   [expr] -> return (Just expr)
       when (DefaultTotal `elem` opts) $ do i <- getIState
                                            putIState (i { default_total = True })
       mapM_ addLangExt (opt getLanguageExt opts)
       setREPL runrepl
       setQuiet (quiet || isJust script)
       setIdeSlave idesl
       setVerbose runrepl
       setCmdLine opts
       setOutputTy outty
       setCodegen cgn
       setTargetTriple trpl
       setTargetCPU tcpu
       setOptLevel optimize
       when (Verbose `elem` opts) $ setVerbose True
       mapM_ makeOption opts
       -- if we have the --fovm flag, drop into the first order VM testing
       case vm of
         [] -> return ()
         xs -> liftIO $ mapM_ (fovm cgn outty) xs 
       -- if we have the --bytecode flag, drop into the bytecode assembler
       case bcs of
         [] -> return ()
         xs -> return () -- liftIO $ mapM_ bcAsm xs 
       case ibcsubdir of
         [] -> setIBCSubDir ""
         (d:_) -> setIBCSubDir d
       setImportDirs importdirs

       addPkgDir "base"
       mapM_ addPkgDir pkgdirs
       elabPrims
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule "Prelude"
                                               return ()
       when (runrepl && not quiet && not idesl && not (isJust script)) $ iputStrLn banner
       ist <- getIState
       mods <- mapM loadModule inputs
       ok <- noErrors
       when ok $ case output of
                    [] -> return ()
                    (o:_) -> process "" (Compile cgn o)
       when ok $ case newoutput of
                    [] -> return ()
                    (o:_) -> process "" (NewCompile o)
       case script of
         Nothing -> return ()
         Just expr -> execScript expr
       when (runrepl && not idesl) $ runInputT replSettings $ repl ist inputs
       when (idesl) $ ideslaveStart ist inputs
       ok <- noErrors
       when (not ok) $ liftIO (exitWith (ExitFailure 1))
  where
    makeOption (OLogging i) = setLogLevel i
    makeOption TypeCase = setTypeCase True
    makeOption TypeInType = setTypeInType True
    makeOption NoCoverage = setCoverage False
    makeOption ErrContext = setErrContext True
    makeOption _ = return ()

    addPkgDir :: String -> Idris ()
    addPkgDir p = do ddir <- liftIO $ getDataDir 
                     addImportDir (ddir </> p)

execScript :: String -> Idris ()
execScript expr = do i <- getIState
                     case parseExpr i expr of
                       Left err -> do iputStrLn $ show err
                                      liftIO $ exitWith (ExitFailure 1)
                       Right term -> do ctxt <- getContext
                                        (tm, _) <- elabVal toplevel False term
                                        res <- execute tm
                                        liftIO $ exitWith ExitSuccess

getFile :: Opt -> Maybe String
getFile (Filename str) = Just str
getFile _ = Nothing

getBC :: Opt -> Maybe String
getBC (BCAsm str) = Just str
getBC _ = Nothing

getFOVM :: Opt -> Maybe String
getFOVM (FOVM str) = Just str
getFOVM _ = Nothing

getOutput :: Opt -> Maybe String
getOutput (Output str) = Just str
getOutput _ = Nothing

getNewOutput :: Opt -> Maybe String
getNewOutput (NewOutput str) = Just str
getNewOutput _ = Nothing

getIBCSubDir :: Opt -> Maybe String
getIBCSubDir (IBCSubDir str) = Just str
getIBCSubDir _ = Nothing

getImportDir :: Opt -> Maybe String
getImportDir (ImportDir str) = Just str
getImportDir _ = Nothing

getPkgDir :: Opt -> Maybe String
getPkgDir (Pkg str) = Just str
getPkgDir _ = Nothing

getPkg :: Opt -> Maybe (Bool, String)
getPkg (PkgBuild str) = Just (False, str)
getPkg (PkgInstall str) = Just (True, str)
getPkg _ = Nothing

getPkgClean :: Opt -> Maybe String
getPkgClean (PkgClean str) = Just str
getPkgClean _ = Nothing

getCodegen :: Opt -> Maybe Codegen
getCodegen (UseCodegen x) = Just x
getCodegen _ = Nothing

getExecScript :: Opt -> Maybe String
getExecScript (InterpretScript expr) = Just expr
getExecScript _ = Nothing

getOutputTy :: Opt -> Maybe OutputType
getOutputTy (OutputTy t) = Just t
getOutputTy _ = Nothing

getLanguageExt :: Opt -> Maybe LanguageExt
getLanguageExt (Extension e) = Just e
getLanguageExt _ = Nothing

getTriple :: Opt -> Maybe String
getTriple (TargetTriple x) = Just x
getTriple _ = Nothing

getCPU :: Opt -> Maybe String
getCPU (TargetCPU x) = Just x
getCPU _ = Nothing

getOptLevel :: Opt -> Maybe Int
getOptLevel (OptLevel x) = Just x
getOptLevel _ = Nothing

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe

ver = showVersion version

banner = "     ____    __     _                                          \n" ++     
         "    /  _/___/ /____(_)____                                     \n" ++
         "    / // __  / ___/ / ___/     Version " ++ ver ++ "\n" ++
         "  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      \n" ++
         " /___/\\__,_/_/  /_/____/       Type :? for help                \n" 



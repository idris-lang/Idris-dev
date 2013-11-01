{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards, CPP #-}

module Idris.REPL where

import Idris.AbsSyntax
import Idris.REPLParser
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Error
import Idris.Delaborate
import Idris.Prover
import Idris.Parser
import Idris.Primitives
import Idris.Coverage
import Idris.UnusedArgs
import Idris.Docs
import Idris.Help
import Idris.Completion
import Idris.IdeSlave
import Idris.Chaser
import Idris.Imports
import Idris.Colours
import Idris.Inliner
import Idris.CaseSplit

import Paths_idris
import Util.System
import Util.DynamicLinker
import Util.Net (listenOnLocalhost)

import Core.Evaluate
import Core.Execute (execute)
import Core.ProofShell
import Core.TT
import Core.Constraints

import IRTS.Compiler
import IRTS.LParser
import IRTS.CodegenCommon

import Text.Trifecta.Result(Result(..))

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
import Control.Monad.Trans.Error (ErrorT(..))
import Control.Monad.Trans.State.Strict ( StateT, execStateT, evalStateT, get, put )
import Control.Monad.Trans ( lift )
import Control.Concurrent.MVar
import Network
import Control.Concurrent
import Data.Maybe
import Data.List
import Data.Char
import Data.Version
import Data.Word (Word)

import qualified Text.PrettyPrint.ANSI.Leijen as ANSI

import Debug.Trace

-- | Run the REPL
repl :: IState -- ^ The initial state
     -> MVar IState -- ^ Server's MVar
     -> [FilePath] -- ^ The loaded modules
     -> InputT Idris ()
repl orig stvar mods
   = H.catch
      (do let quiet = opt_quiet (idris_options orig)
          i <- lift getIState
          lift $ runIO $ swapMVar stvar i -- update shared state
          let colour = idris_colourRepl i
          let theme = idris_colourTheme i
          let prompt = if quiet
                          then ""
                          else let str = mkPrompt mods ++ ">" in
                               (if colour then colourisePrompt theme str else str) ++ " "
          x <- getInputLine prompt
          case x of
              Nothing -> do lift $ when (not quiet) (iputStrLn "Bye bye")
                            return ()
              Just input -> H.catch
                              (do ms <- lift $ processInput stvar input orig mods
                                  case ms of
                                      Just mods -> repl orig stvar mods
                                      Nothing -> return ())
                              ctrlC)
      ctrlC
   where ctrlC :: SomeException -> InputT Idris ()
         ctrlC e = do lift $ iputStrLn (show e)
                      repl orig stvar mods

-- | Run the REPL server
startServer :: IState -> MVar IState -> [FilePath] -> Idris ()
startServer orig stvar fn_in = do tid <- runIO $ forkOS serverLoop
                                  return ()
  where serverLoop :: IO ()
        -- TODO: option for port number
        serverLoop = withSocketsDo $
                              do sock <- listenOnLocalhost $ PortNumber 4294
                                 i <- readMVar stvar
                                 loop fn i sock

        fn = case fn_in of
                  (f:_) -> f
                  _ -> ""

        loop fn ist sock
            = do (h,host,_) <- accept sock
                 -- just use the local part of the hostname
                 -- for the "localhost.localdomain" case
                 if ((takeWhile (/= '.') host) == "localhost" ||
                     host == "127.0.0.1")
                   then do
                     cmd <- hGetLine h
                     takeMVar stvar
                     (ist', fn) <- processNetCmd stvar orig ist h fn cmd
                     putMVar stvar ist'
                     hClose h
                     loop fn ist' sock
                   else hClose h

processNetCmd :: MVar IState ->
                 IState -> IState -> Handle -> FilePath -> String ->
                 IO (IState, FilePath)
processNetCmd stvar orig i h fn cmd
    = do res <- case parseCmd i "(net)" cmd of
                  Failure err -> return (Left (Msg " invalid command"))
                  Success c -> runErrorT $ evalStateT (processNet fn c) i
         case res of
              Right x -> return x
              Left err -> do hPutStrLn h (show err)
                             return (i, fn)
  where
    processNet fn Reload = processNet fn (Load fn)
    processNet fn (Load f) =
        do let ist = orig { idris_options = idris_options i
                          , idris_colourTheme = idris_colourTheme i
                          , idris_colourRepl = False
                          }
           putIState ist
           setErrContext True
           setOutH h
           setQuiet True
           setVerbose False
           mods <- loadInputs h [f]
           ist <- getIState
           return (ist, f)
    processNet fn c = do process h fn c
                         ist <- getIState
                         return (ist, fn)

-- | Run a command on the server on localhost
runClient :: String -> IO ()
runClient str = withSocketsDo $ do
                  h <- connectTo "localhost" (PortNumber 4294)
                  hPutStrLn h str
                  resp <- hGetResp "" h
                  putStr resp
                  hClose h
    where hGetResp acc h = do eof <- hIsEOF h
                              if eof then return acc
                                     else do l <- hGetLine h
                                             hGetResp (acc ++ l ++ "\n") h

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
         (do l <- runIO $ getLine
             let (sexp, id) = parseMessage l
             i <- getIState
             putIState $ i { idris_outputmode = (IdeSlave id) }
             case sexpToCommand sexp of
               Just (Interpret cmd) ->
                 do let fn = case mods of
                                 (f:_) -> f
                                 _ -> ""
                    c <- colourise
                    case parseCmd i "(input)" cmd of
                         Failure err -> iPrintError $ show (fixColour c err)
                         Success (Prove n') -> do iPrintResult ""
                                                  idrisCatch
                                                    (process stdout fn (Prove n'))
                                                    (\e -> getIState >>= iPrintError . flip pshow e)
                                                  isetPrompt (mkPrompt mods)
                         Success cmd -> idrisCatch
                                          (ideslaveProcess fn cmd)
                                          (\e -> getIState >>= iPrintError . flip pshow e)
               Just (REPLCompletions str) ->
                 do (unused, compls) <- replCompletion (reverse str, "")
                    let good = SexpList [SymbolAtom "ok", toSExp (map replacement compls, reverse unused)]
                    runIO $ putStrLn $ convSExp "return" good id
               Just (LoadFile filename) ->
                 do clearErr
                    putIState (orig { idris_options = idris_options i,
                                      idris_outputmode = (IdeSlave id) })
                    loadModule stdout filename
                    iucheck
                    isetPrompt (mkPrompt [filename])

                    -- Report either success or failure
                    i <- getIState
                    case (errLine i) of
                      Nothing -> iPrintResult $ "loaded " ++ filename
                      Just x -> iPrintError $ "didn't load " ++ filename
                    ideslave orig [filename]
               Nothing -> do iPrintError "did not understand")
         (\e -> do iPrintError $ show e)
       ideslave orig mods

ideslaveProcess :: FilePath -> Command -> Idris ()
ideslaveProcess fn Help = process stdout fn Help
ideslaveProcess fn (ChangeDirectory f) = do process stdout fn (ChangeDirectory f)
                                            iPrintResult "changed directory to"
ideslaveProcess fn (Eval t) = process stdout fn (Eval t)
ideslaveProcess fn (ExecVal t) = process stdout fn (ExecVal t)
ideslaveProcess fn (Check (PRef x n)) = process stdout fn (Check (PRef x n))
ideslaveProcess fn (Check t) = process stdout fn (Check t)
ideslaveProcess fn (DocStr n) = process stdout fn (DocStr n)
ideslaveProcess fn Universes = process stdout fn Universes
ideslaveProcess fn (Defn n) = do process stdout fn (Defn n)
                                 iPrintResult ""
ideslaveProcess fn (TotCheck n) = process stdout fn (TotCheck n)
ideslaveProcess fn (DebugInfo n) = do process stdout fn (DebugInfo n)
                                      iPrintResult ""
ideslaveProcess fn (Info n) = process stdout fn (Info n)
ideslaveProcess fn (Search t) = process stdout fn (Search t)
ideslaveProcess fn (Spec t) = process stdout fn (Spec t)
-- RmProof and AddProof not supported!
ideslaveProcess fn (ShowProof n') = process stdout fn (ShowProof n')
ideslaveProcess fn (HNF t) = process stdout fn (HNF t)
--ideslaveProcess fn TTShell = process stdout fn TTShell -- need some prove mode!

--that most likely does not work, since we need to wrap
--input/output of the executed binary...
ideslaveProcess fn Execute = do process stdout fn Execute
                                iPrintResult ""
ideslaveProcess fn (Compile codegen f) = do process stdout fn (Compile codegen f)
                                            iPrintResult ""
ideslaveProcess fn (LogLvl i) = do process stdout fn (LogLvl i)
                                   iPrintResult ""
ideslaveProcess fn (Pattelab t) = process stdout fn (Pattelab t)
ideslaveProcess fn (Missing n) = process stdout fn (Missing n)
ideslaveProcess fn (DynamicLink l) = do process stdout fn (DynamicLink l)
                                        iPrintResult ""
ideslaveProcess fn ListDynamic = do process stdout fn ListDynamic
                                    iPrintResult ""
ideslaveProcess fn Metavars = process stdout fn Metavars
ideslaveProcess fn (SetOpt ErrContext) = do process stdout fn (SetOpt ErrContext)
                                            iPrintResult ""
ideslaveProcess fn (UnsetOpt ErrContext) = do process stdout fn (UnsetOpt ErrContext)
                                              iPrintResult ""
ideslaveProcess fn (SetOpt ShowImpl) = do process stdout fn (SetOpt ShowImpl)
                                          iPrintResult ""
ideslaveProcess fn (UnsetOpt ShowImpl) = do process stdout fn (UnsetOpt ShowImpl)
                                            iPrintResult ""
ideslaveProcess fn (SetOpt x) = process stdout fn (SetOpt x)
ideslaveProcess fn (UnsetOpt x) = process stdout fn (UnsetOpt x)
ideslaveProcess fn _ = iPrintError "command not recognized or not supported"


-- | The prompt consists of the currently loaded modules, or "Idris" if there are none
mkPrompt [] = "Idris"
mkPrompt [x] = "*" ++ dropExtension x
mkPrompt (x:xs) = "*" ++ dropExtension x ++ " " ++ mkPrompt xs

-- | Determine whether a file uses literate syntax
lit f = case splitExtension f of
            (_, ".lidr") -> True
            _ -> False

processInput :: MVar IState -> String ->
                IState -> [FilePath] -> Idris (Maybe [FilePath])
processInput stvar cmd orig inputs
    = do i <- getIState
         let opts = idris_options i
         let quiet = opt_quiet opts
         let fn = case inputs of
                        (f:_) -> f
                        _ -> ""
         c <- colourise
         case parseCmd i "(input)" cmd of
            Failure err ->   do runIO $ print (fixColour c err)
                                return (Just inputs)
            Success Reload ->
                do putIState $ orig { idris_options = idris_options i
                                    , idris_colourTheme = idris_colourTheme i
                                    }
                   clearErr
                   mods <- loadInputs stdout inputs
                   return (Just inputs)
            Success (Load f) ->
                do putIState orig { idris_options = idris_options i
                                  , idris_colourTheme = idris_colourTheme i
                                  }
                   clearErr
                   mod <- loadModule stdout f
                   return (Just [f])
            Success (ModImport f) ->
                do clearErr
                   fmod <- loadModule stdout f
                   return (Just (inputs ++ [fmod]))
            Success Edit -> do -- takeMVar stvar
                               edit fn orig
                               return (Just inputs)
            Success Proofs -> do proofs orig
                                 return (Just inputs)
            Success Quit -> do when (not quiet) (iputStrLn "Bye bye")
                               return Nothing
            Success cmd  -> do idrisCatch (process stdout fn cmd)
                                          (\e -> do msg <- showErr e ; iputStrLn msg)
                               return (Just inputs)

resolveProof :: Name -> Idris Name
resolveProof n'
  = do i <- getIState
       ctxt <- getContext
       n <- case lookupNames n' ctxt of
                 [x] -> return x
                 [] -> return n'
                 ns -> ierror (CantResolveAlts (map show ns))
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
         env <- runIO $ getEnvironment
         let editor = getEditor env
         let line = case errLine i of
                        Just l -> " +" ++ show l ++ " "
                        Nothing -> " "
         let cmd = editor ++ line ++ fixName f
         runIO $ system cmd
         clearErr
         putIState $ orig { idris_options = idris_options i
                          , idris_colourTheme = idris_colourTheme i
                          }
         loadInputs stdout [f]
         iucheck
         return ()
   where getEditor env | Just ed <- lookup "EDITOR" env = ed
                       | Just ed <- lookup "VISUAL" env = ed
                       | otherwise = "vi"
         fixName file | map toLower (takeExtension file) `elem` [".lidr", ".idr"] = file
                      | otherwise = addExtension file "idr"



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

process :: Handle -> FilePath -> Command -> Idris ()
process h fn Help = iPrintResult displayHelp
process h fn (ChangeDirectory f)
                 = do runIO $ setCurrentDirectory f
                      return ()
process h fn (Eval t)
                 = do (tm, ty) <- elabVal toplevel False t
                      ctxt <- getContext
                      ist <- getIState
                      let tm' = normaliseAll ctxt [] tm
                      let ty' = normaliseAll ctxt [] ty
                      -- Add value to context, call it "it"
                      updateContext (addCtxtDef (UN "it") (Function ty' tm'))
                      logLvl 3 $ "Raw: " ++ show (tm', ty')
                      logLvl 10 $ "Debug: " ++ showEnvDbg [] tm'
                      imp <- impShow
                      c <- colourise
                      ihPrintResult h (showImp (Just ist) imp c (delab ist tm') ++ " : " ++
                               showImp (Just ist) imp c (delab ist ty'))
process h fn (ExecVal t)
                  = do ctxt <- getContext
                       ist <- getIState
                       (tm, ty) <- elabVal toplevel False t
--                       let tm' = normaliseAll ctxt [] tm
                       let ty' = normaliseAll ctxt [] ty
                       res <- execute tm
                       imp <- impShow
                       c <- colourise
                       ihPrintResult h (showImp (Just ist) imp c (delab ist res) ++ " : " ++
                                showImp (Just ist) imp c (delab ist ty'))
process h fn (Check (PRef _ n))
   = do ctxt <- getContext
        ist <- getIState
        imp <- impShow
        c <- colourise
        case lookupNames n ctxt of
          ts@(t:_) ->
            case lookup t (idris_metavars ist) of
                Just (_, i) -> showMetavarInfo c imp ist n i
                Nothing -> do mapM_ (\n -> ihputStrLn h $ showName (Just ist) [] False c n ++ " : " ++
                                           showImp (Just ist) imp c (delabTy ist n)) ts
                              ihPrintResult h ""
          [] -> ihPrintError h $ "No such variable " ++ show n
  where
    showMetavarInfo c imp ist n i
         = case lookupTy n (tt_ctxt ist) of
                (ty:_) -> putTy c imp ist i (delab ist ty)
    putTy c imp ist 0 sc = putGoal c imp ist sc
    putTy c imp ist i (PPi _ n t sc)
               = do ihputStrLn h $ "  " ++
                         (case n of
                              MN _ _ -> "_"
                              UN ('_':'_':_) -> "_"
                              _ -> showName (Just ist) [] False c n) ++
                                   " : " ++ showImp (Just ist) imp c t
                    putTy c imp ist (i-1) sc
    putTy c imp ist _ sc = putGoal c imp ist sc
    putGoal c imp ist g
               = do ihputStrLn h $ "--------------------------------------"
                    ihputStrLn h $ showName (Just ist) [] False c n ++ " : "
                                   ++ showImp (Just ist) imp c g


process h fn (Check t)
   = do (tm, ty) <- elabVal toplevel False t
        ctxt <- getContext
        ist <- getIState
        imp <- impShow
        c <- colourise
        let ty' = normaliseC ctxt [] ty
        case tm of
             TType _ -> ihPrintResult h ("Type : Type 1")
             _ -> ihPrintResult h (showImp (Just ist) imp c (delab ist tm) ++ " : " ++
                                 showImp (Just ist) imp c (delab ist ty))

process h fn (DocStr n)
                      = do i <- getIState
                           case lookupCtxtName n (idris_docstrings i) of
                                [] -> iPrintError $ "No documentation for " ++ show n
                                ns -> do mapM_ showDoc ns
                                         iPrintResult ""
    where showDoc (n, d)
             = do doc <- getDocs n
                  iputStrLn $ show doc
process h fn Universes
                     = do i <- getIState
                          let cs = idris_constraints i
--                        iputStrLn $ showSep "\n" (map show cs)
                          iputStrLn $ show (map fst cs)
                          let n = length cs
                          iputStrLn $ "(" ++ show n ++ " constraints)"
                          case ucheck cs of
                            Error e -> iPrintError $ pshow i e
                            OK _ -> iPrintResult "Universes OK"
process h fn (Defn n)
                    = do i <- getIState
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
             = do c <- colourise
                  iputStrLn (showImp (Just i) True c (delab i lhs) ++ " = " ++
                             showImp (Just i) True c (delab i rhs))
process h fn (TotCheck n)
                        = do i <- getIState
                             case lookupTotal n (tt_ctxt i) of
                                [t] -> iPrintResult (showTotal t i)
                                _ -> do iPrintError ""
                                        return ()
process h fn (DebugInfo n)
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
process h fn (Info n)
                    = do i <- getIState
                         case lookupCtxt n (idris_classes i) of
                              [c] -> classInfo c
                              _ -> iPrintError "Not a class"
process h fn (Search t) = iPrintError "Not implemented"
process h fn (CaseSplit n t)
   = do tms <- split n t
        iputStrLn (showSep "\n" (map show tms))
process h fn (CaseSplitAt updatefile l n)
   = do src <- runIO $ readFile fn
        res <- splitOnLine l n fn
        iLOG (showSep "\n" (map show res))
        let (before, (ap : later)) = splitAt (l-1) (lines src)
        res' <- replaceSplits ap res
        let new = concat res'
        if updatefile then
           do let fb = fn ++ "~" -- make a backup!
              runIO $ writeFile fb (unlines before ++ new ++ unlines later)
              runIO $ copyFile fb fn
           else -- do ihputStrLn h (show res)
                   ihputStrLn h new
process h fn (AddClauseFrom updatefile l n)
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getClause l n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile then
           do let fb = fn ++ "~"
              runIO $ writeFile fb (unlines (before ++ nonblank)
                                        ++ replicate indent ' ' ++
                                        cl ++ "\n" ++
                                    unlines rest)
              runIO $ copyFile fb fn
           else ihputStrLn h cl
    where
       getIndent i n [] = 0
       getIndent i n xs | take (length n) xs == n = i
       getIndent i n (x : xs) = getIndent (i + 1) n xs
process h fn (AddMissing updatefile l n)
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        i <- getIState
        cl <- getInternalApp fn l
        let n' = getAppName cl
        extras <- case lookupCtxt n' (idris_patdefs i) of
                       [] -> return ""
                       [(_, tms)] -> showNew (show n ++ "_rhs") 1 tms
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile then
           do let fb = fn ++ "~"
              runIO $ writeFile fb (unlines (before ++ nonblank) ++
                                           extras ++ unlines rest)
              runIO $ copyFile fb fn
           else ihputStrLn h extras
    where showPat = show . stripNS
          stripNS tm = mapPT dens tm where
              dens (PRef fc n) = PRef fc (nsroot n)
              dens t = t

          nsroot (NS n _) = nsroot n
          nsroot (SN (WhereN _ _ n)) = nsroot n
          nsroot n = n

          getAppName (PApp _ r _) = getAppName r
          getAppName (PRef _ r) = r
          getAppName _ = n

          showNew nm i (tm : tms)
                        = do (nm', i') <- getUniq nm i
                             rest <- showNew nm i' tms
                             return (showPat tm ++ " = ?" ++ nm' ++
                                     "\n" ++ rest)
          showNew nm i [] = return ""

process h fn (MakeWith updatefile l n)
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let with = mkWith tyline n
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) later
        if updatefile then
           do let fb = fn ++ "~"
              runIO $ writeFile fb (unlines (before ++ nonblank)
                                        ++ with ++ "\n" ++
                                    unlines rest)
              runIO $ copyFile fb fn
           else ihputStrLn h with
process h fn (DoProofSearch updatefile l n hints)
    = do src <- runIO $ readFile fn
         let (before, tyline : later) = splitAt (l-1) (lines src)
         ctxt <- getContext
         mn <- case lookupNames n ctxt of
                    [x] -> return x
                    [] -> return n
                    ns -> ierror (CantResolveAlts (map show ns))
         i <- getIState
         let (top, envlen) = case lookup mn (idris_metavars i) of
                                  Just mi -> mi
                                  _ -> (Nothing, 0)
         let fc = fileFC fn
         let body t = PProof [Try (TSeq Intros (ProofSearch t n hints))
                                  (ProofSearch t n hints)]
         let def = PClause fc mn (PRef fc mn) [] (body top) []
         newmv <- idrisCatch
             (do elabDecl' EAll toplevel (PClauses fc [] mn [def])
                 (tm, ty) <- elabVal toplevel False (PRef fc mn)
                 ctxt <- getContext
                 i <- getIState
                 return $ show (stripNS
                           (dropCtxt envlen
                              (delab i (specialise ctxt [] [(mn, 1)] tm)))))
             (\e -> return ("?" ++ show n))
         if updatefile then
            do let fb = fn ++ "~"
               runIO $ writeFile fb (unlines before ++
                                     updateMeta tyline (show n) newmv ++ "\n"
                                       ++ unlines later)
               runIO $ copyFile fb fn
            else ihputStrLn h newmv
    where dropCtxt 0 sc = sc
          dropCtxt i (PPi _ _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt i (PLet _ _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt i (PLam _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt _ t = t

          stripNS tm = mapPT dens tm where
              dens (PRef fc n) = PRef fc (nsroot n)
              dens t = t

          nsroot (NS n _) = nsroot n
          nsroot (SN (WhereN _ _ n)) = nsroot n
          nsroot n = n

          updateMeta ('?':cs) n new
            | length cs >= length n
              = case splitAt (length n) cs of
                     (mv, c:cs) ->
                          if (isSpace c && mv == n)
                             then new ++ (c : cs)
                             else '?' : mv ++ c : updateMeta cs n new
                     (mv, []) -> if (mv == n) then new else '?' : mv
          updateMeta (c:cs) n new = c : updateMeta cs n new
          updateMeta [] n new = ""

process h fn (Spec t)
                    = do (tm, ty) <- elabVal toplevel False t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = simplify ctxt [] {- (idris_statics ist) -} tm
                         iPrintResult (show (delab ist tm'))

process h fn (RmProof n')
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
                                 putIState $ i { idris_metavars = (n, (Nothing, 0)) : ms }

process h fn' (AddProof prf)
  = do fn <- do
         ex <- runIO $ doesFileExist fn'
         let fnExt = fn' <.> "idr"
         exExt <- runIO $ doesFileExist fnExt
         if ex
            then return fn'
            else if exExt
                    then return fnExt
                    else ifail $ "Neither \""++fn'++"\" nor \""++fnExt++"\" exist"
       let fb = fn ++ "~"
       runIO $ copyFile fn fb -- make a backup in case something goes wrong!
       prog <- runIO $ readFile fb
       i <- getIState
       let proofs = proof_list i
       n' <- case prf of
                Nothing -> case proofs of
                             [] -> ifail "No proof to add"
                             ((x, p) : _) -> return x
                Just nm -> return nm
       n <- resolveProof n'
       case lookup n proofs of
            Nothing -> iputStrLn "No proof to add"
            Just p  -> do let prog' = insertScript (showProof (lit fn) n p) ls
                          runIO $ writeFile fn (unlines prog')
                          removeProof n
                          iputStrLn $ "Added proof " ++ show n
                          where ls = (lines prog)

process h fn (ShowProof n')
  = do i <- getIState
       n <- resolveProof n'
       let proofs = proof_list i
       case lookup n proofs of
            Nothing -> iPrintError "No proof to show"
            Just p  -> iPrintResult $ showProof False n p

process h fn (Prove n')
     = do ctxt <- getContext
          ist <- getIState
          n <- case lookupNames n' ctxt of
                    [x] -> return x
                    [] -> return n'
                    ns -> ierror (CantResolveAlts (map show ns))
          prover (lit fn) n
          -- recheck totality
          i <- getIState
          totcheck (fileFC "(input)", n)
          mapM_ (\ (f,n) -> setTotality n Unchecked) (idris_totcheck i)
          mapM_ checkDeclTotality (idris_totcheck i)

process h fn (HNF t)
                    = do (tm, ty) <- elabVal toplevel False t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = hnf ctxt [] tm
                         iPrintResult (show (delab ist tm'))
process h fn (TestInline t)
                           = do (tm, ty) <- elabVal toplevel False t
                                ctxt <- getContext
                                ist <- getIState
                                let tm' = inlineTerm ist tm
                                imp <- impShow
                                c <- colourise
                                iPrintResult (showImp (Just ist) imp c (delab ist tm'))
process h fn TTShell
                    = do ist <- getIState
                         let shst = initState (tt_ctxt ist)
                         runShell shst
                         return ()
process h fn Execute
                   = do (m, _) <- elabVal toplevel False
                                        (PApp fc
                                           (PRef fc (UN "run__IO"))
                                           [pexp $ PRef fc (NS (UN "main") ["Main"])])
--                                      (PRef (FC "main" 0) (NS (UN "main") ["main"]))
                        (tmpn, tmph) <- runIO tempfile
                        runIO $ hClose tmph
                        t <- codegen
                        compile t tmpn m
                        runIO $ system tmpn
                        return ()
  where fc = fileFC "main"
process h fn (Compile codegen f)
      = do (m, _) <- elabVal toplevel False
                       (PApp fc (PRef fc (UN "run__IO"))
                       [pexp $ PRef fc (NS (UN "main") ["Main"])])
           compile codegen f m
  where fc = fileFC "main"
process h fn (LogLvl i) = setLogLevel i
-- Elaborate as if LHS of a pattern (debug command)
process h fn (Pattelab t)
     = do (tm, ty) <- elabVal toplevel True t
          iPrintResult $ show tm ++ "\n\n : " ++ show ty

process h fn (Missing n)
    = do i <- getIState
         c <- colourise
         case lookupCtxt n (idris_patdefs i) of
                  [] -> return ()
                  [(_, tms)] ->
                       iPrintResult (showSep "\n" (map (showImp (Just i) True c) tms))
                  _ -> iPrintError $ "Ambiguous name"
process h fn (DynamicLink l)
                           = do i <- getIState
                                let lib = trim l
                                handle <- lift . lift $ tryLoadLib lib
                                case handle of
                                  Nothing -> iPrintError $ "Could not load dynamic lib \"" ++ l ++ "\""
                                  Just x -> do let libs = idris_dynamic_libs i
                                               if x `elem` libs
                                                  then do iLOG ("Tried to load duplicate library " ++ lib_name x)
                                                          return ()
                                                  else putIState $ i { idris_dynamic_libs = x:libs }
    where trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
process h fn ListDynamic
                       = do i <- getIState
                            iputStrLn "Dynamic libraries:"
                            showLibs $ idris_dynamic_libs i
    where showLibs []                = return ()
          showLibs ((Lib name _):ls) = do iputStrLn $ "\t" ++ name; showLibs ls
process h fn Metavars
                 = do ist <- getIState
                      let mvs = map fst (idris_metavars ist) \\ primDefs
                      case mvs of
                        [] -> iPrintError "No global metavariables to solve"
                        _ -> iPrintResult $ "Global metavariables:\n\t" ++ show mvs
process h fn NOP      = return ()

process h fn (SetOpt   ErrContext) = setErrContext True
process h fn (UnsetOpt ErrContext) = setErrContext False
process h fn (SetOpt ShowImpl)     = setImpShow True
process h fn (UnsetOpt ShowImpl)   = setImpShow False

process h fn (SetOpt _) = iPrintError "Not a valid option"
process h fn (UnsetOpt _) = iPrintError "Not a valid option"
process h fn (SetColour ty c) = setColour ty c
process h fn ColourOn
                    = do ist <- getIState
                         putIState $ ist { idris_colourRepl = True }
process h fn ColourOff
                     = do ist <- getIState
                          putIState $ ist { idris_colourRepl = False }

classInfo :: ClassInfo -> Idris ()
classInfo ci = do iputStrLn "Methods:\n"
                  mapM_ dumpMethod (class_methods ci)
                  iputStrLn ""
                  iputStrLn "Instances:\n"
                  mapM_ dumpInstance (class_instances ci)
                  iPrintResult ""

dumpMethod :: (Name, (FnOpts, PTerm)) -> Idris ()
dumpMethod (n, (_, t)) = iputStrLn $ show n ++ " : " ++ show t

dumpInstance :: Name -> Idris ()
dumpInstance n = do i <- getIState
                    ctxt <- getContext
                    imp <- impShow
                    case lookupTy n ctxt of
                         ts -> mapM_ (\t -> iputStrLn $ showImp Nothing imp False (delab i t)) ts

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
parseArgs ("--client":ns)        = [Client (showSep " " ns)]
parseArgs ("--log":lvl:ns)       = OLogging (read lvl) : (parseArgs ns)
parseArgs ("--noprelude":ns)     = NoPrelude : (parseArgs ns)
parseArgs ("--check":ns)         = NoREPL : (parseArgs ns)
parseArgs ("-o":n:ns)            = NoREPL : Output n : (parseArgs ns)
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
parseArgs ("--mvn":ns)           = OutputTy MavenProject : (parseArgs ns)
parseArgs ("--dumpdefuns":n:ns)  = DumpDefun n : (parseArgs ns)
parseArgs ("--dumpcases":n:ns)   = DumpCases n : (parseArgs ns)
parseArgs ("--codegen":n:ns)     = UseCodegen (parseCodegen n) : (parseArgs ns)
parseArgs ["--exec"]             = InterpretScript "Main.main" : []
parseArgs ("--exec":expr:ns)     = InterpretScript expr : parseArgs ns
parseArgs ("-XTypeProviders":ns) = Extension TypeProviders : (parseArgs ns)
parseArgs ("-XErrorReflection":ns) = Extension ErrorReflection : (parseArgs ns)
parseArgs ("-O3":ns)             = OptLevel 3 : parseArgs ns
parseArgs ("-O2":ns)             = OptLevel 2 : parseArgs ns
parseArgs ("-O1":ns)             = OptLevel 1 : parseArgs ns
parseArgs ("-O0":ns)             = OptLevel 0 : parseArgs ns
parseArgs ("-O":n:ns)            = OptLevel (read n) : parseArgs ns
parseArgs ("--target":n:ns)      = TargetTriple n : parseArgs ns
parseArgs ("--cpu":n:ns)         = TargetCPU n : parseArgs ns
parseArgs ("--colour":ns)        = ColourREPL True : parseArgs ns
parseArgs ("--color":ns)         = ColourREPL True : parseArgs ns
parseArgs ("--nocolour":ns)      = ColourREPL False : parseArgs ns
parseArgs ("--nocolor":ns)       = ColourREPL False : parseArgs ns
parseArgs (n:ns)                 = Filename n : (parseArgs ns)

helphead =
  [ (["Command"], SpecialHeaderArg, "Purpose"),
    ([""], NoArg, "")
  ]


replSettings :: Maybe FilePath -> Settings Idris
replSettings hFile = setComplete replCompletion $ defaultSettings {
                       historyFile = hFile
                     }

-- invoke as if from command line
idris :: [Opt] -> IO ()
idris opts = do res <- runErrorT $ execStateT (idrisMain opts) idrisInit
                case res of
                  Left err -> putStrLn $ pshow idrisInit err
                  Right ist -> return ()


loadInputs :: Handle -> [FilePath] -> Idris ()
loadInputs h inputs
  = do ist <- getIState
       -- if we're in --check and not outputting anything, don't bother
       -- loading, as it gets really slow if there's lots of modules in
       -- a package (instead, reload all at the end to check for
       -- consistency only)
       opts <- getCmdLine

       let loadCode = case opt getOutput opts of
                           [] -> not (NoREPL `elem` opts)
                           _ -> True

       -- For each ifile list, check it and build ibcs in the same clean IState
       -- so that they don't interfere with each other when checking

       let ninputs = zip [1..] inputs
       ifiles <- mapM (\(num, input) ->
            do putIState ist
               v <- verbose
--                           when v $ iputStrLn $ "(" ++ show num ++ "/" ++
--                                                show (length inputs) ++
--                                                ") " ++ input
               modTree <- buildTree
                               (map snd (take (num-1) ninputs))
                               input
               let ifiles = getModuleFiles modTree
               iLOG ("MODULE TREE : " ++ show modTree)
               iLOG ("RELOAD: " ++ show ifiles)
               when (not (all ibc ifiles) || loadCode) $ tryLoad ifiles
               -- return the files that need rechecking
               return (if (all ibc ifiles) then ifiles else []))
                  ninputs
       inew <- getIState
       -- to check everything worked consistently (in particular, will catch
       -- if the ibc version is out of date) if we weren't loading per
       -- module
       case errLine inew of
          Nothing ->
            do putIState ist
               when (not loadCode) $ tryLoad $ nub (concat ifiles)
          _ -> return ()
       putIState inew
--        inew <- getIState
--        case errLine inew of
--             Nothing ->
--             -- Then, load all the ibcs again, if there were no errors.
--               do putIState ist
--                  modTree <- mapM (buildTree (map snd ninputs)) inputs
--                  let ifiless = map getModuleFiles modTree
--                  mapM_ loadFromIFile (concat ifiless)
--             _ -> return ()
   where -- load all files, stop if any fail
         tryLoad :: [IFileType] -> Idris ()
         tryLoad [] = return ()
         tryLoad (f : fs) = do loadFromIFile h f
                               inew <- getIState
                               case errLine inew of
                                    Nothing -> tryLoad fs
                                    _ -> return () -- error, stop

         ibc (IBC _ _) = True
         ibc _ = False

idrisMain :: [Opt] -> Idris ()
idrisMain opts =
    do let inputs = opt getFile opts
       let quiet = Quiet `elem` opts
       let idesl = Ideslave `elem` opts
       let runrepl = not (NoREPL `elem` opts)
       let output = opt getOutput opts
       let ibcsubdir = opt getIBCSubDir opts
       let importdirs = opt getImportDir opts
       let bcs = opt getBC opts
       let vm = opt getFOVM opts
       let pkgdirs = opt getPkgDir opts
       let optimize = case opt getOptLevel opts of
                        [] -> 2
                        xs -> last xs
       trpl <- case opt getTriple opts of
                 [] -> runIO $ getDefaultTargetTriple
                 xs -> return (last xs)
       tcpu <- case opt getCPU opts of
                 [] -> runIO $ getHostCPUName
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
                                runIO $ exitWith (ExitFailure 1)
                   [expr] -> return (Just expr)
       when (DefaultTotal `elem` opts) $ do i <- getIState
                                            putIState (i { default_total = True })
       setColourise $ not quiet && last (True : opt getColour opts)
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
         xs -> runIO $ mapM_ (fovm cgn outty) xs
       -- if we have the --bytecode flag, drop into the bytecode assembler
       case bcs of
         [] -> return ()
         xs -> return () -- runIO $ mapM_ bcAsm xs
       case ibcsubdir of
         [] -> setIBCSubDir ""
         (d:_) -> setIBCSubDir d
       setImportDirs importdirs

       addPkgDir "base"
       mapM_ addPkgDir pkgdirs
       elabPrims
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule stdout "Prelude"
                                               return ()
       when (runrepl && not quiet && not idesl && not (isJust script)) $ iputStrLn banner
       ist <- getIState

       loadInputs stdout inputs

       runIO $ hSetBuffering stdout LineBuffering

       ok <- noErrors
       when ok $ case output of
                    [] -> return ()
                    (o:_) -> process stdout "" (Compile cgn o)
       case script of
         Nothing -> return ()
         Just expr -> execScript expr

       historyFile <- fmap (</> "repl" </> "history") getIdrisUserDataDir

       when runrepl $ initScript
       stvar <- runIO $ newMVar ist
       when runrepl $ startServer ist stvar inputs
       when (runrepl && not idesl) $ runInputT (replSettings (Just historyFile)) $ repl ist stvar inputs
       when (idesl) $ ideslaveStart ist inputs
       ok <- noErrors
       when (not ok) $ runIO (exitWith (ExitFailure 1))
  where
    makeOption (OLogging i) = setLogLevel i
    makeOption TypeCase = setTypeCase True
    makeOption TypeInType = setTypeInType True
    makeOption NoCoverage = setCoverage False
    makeOption ErrContext = setErrContext True
    makeOption _ = return ()

    addPkgDir :: String -> Idris ()
    addPkgDir p = do ddir <- runIO $ getDataDir
                     addImportDir (ddir </> p)

execScript :: String -> Idris ()
execScript expr = do i <- getIState
                     c <- colourise
                     case parseExpr i expr of
                          Failure err -> do iputStrLn $ show (fixColour c err)
                                            runIO $ exitWith (ExitFailure 1)
                          Success term -> do ctxt <- getContext
                                             (tm, _) <- elabVal toplevel False term
                                             res <- execute tm
                                             runIO $ exitWith ExitSuccess

-- | Check if the coloring matches the options and corrects if necessary
fixColour :: Bool -> ANSI.Doc -> ANSI.Doc
fixColour False doc = ANSI.plain doc
fixColour True doc  = doc

-- | Get the platform-specific, user-specific Idris dir
getIdrisUserDataDir :: Idris FilePath
getIdrisUserDataDir = runIO $ getAppUserDataDirectory "idris"

-- | Locate the platform-specific location for the init script
getInitScript :: Idris FilePath
getInitScript = do idrisDir <- getIdrisUserDataDir
                   return $ idrisDir </> "repl" </> "init"

-- | Run the initialisation script
initScript :: Idris ()
initScript = do script <- getInitScript
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
                           script <- getInitScript
                           c <- colourise
                           processLine ist line script c
                           runInit h
          processLine i cmd input clr =
              case parseCmd i input cmd of
                   Failure err -> runIO $ print (fixColour clr err)
                   Success Reload -> iPrintError "Init scripts cannot reload the file"
                   Success (Load f) -> iPrintError "Init scripts cannot load files"
                   Success (ModImport f) -> iPrintError "Init scripts cannot import modules"
                   Success Edit -> iPrintError "Init scripts cannot invoke the editor"
                   Success Proofs -> proofs i
                   Success Quit -> iPrintError "Init scripts cannot quit Idris"
                   Success cmd  -> process stdout [] cmd

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

getOptLevel :: Opt -> Maybe Word
getOptLevel (OptLevel x) = Just x
getOptLevel _ = Nothing

getColour :: Opt -> Maybe Bool
getColour (ColourREPL b) = Just b
getColour _ = Nothing

opt :: (Opt -> Maybe a) -> [Opt] -> [a]
opt = mapMaybe

ver = showVersion version

banner = "     ____    __     _                                          \n" ++
         "    /  _/___/ /____(_)____                                     \n" ++
         "    / // __  / ___/ / ___/     Version " ++ ver ++ "\n" ++
         "  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      \n" ++
         " /___/\\__,_/_/  /_/____/       Type :? for help                \n"



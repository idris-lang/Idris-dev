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
import Idris.Docs hiding (Doc)
import Idris.Help
import Idris.Completion
import qualified Idris.IdeSlave as IdeSlave
import Idris.Chaser
import Idris.Imports
import Idris.Colours
import Idris.Inliner
import Idris.CaseSplit
import Idris.DeepSeq

import Paths_idris
import Version_idris (gitHash)
import Util.System
import Util.DynamicLinker
import Util.Net (listenOnLocalhost)
import Util.Pretty hiding ((</>))

import Idris.Core.Evaluate
import Idris.Core.Execute (execute)
import Idris.Core.TT
import Idris.Core.Constraints

import IRTS.Compiler
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
import Control.DeepSeq

import qualified Text.PrettyPrint.ANSI.Leijen as ANSI

import Debug.Trace

-- | Run the REPL
repl :: IState -- ^ The initial state
     -> [FilePath] -- ^ The loaded modules
     -> InputT Idris ()
repl orig mods
   = -- H.catch
     do let quiet = opt_quiet (idris_options orig)
        i <- lift getIState
        let colour = idris_colourRepl i
        let theme = idris_colourTheme i
        let mvs = idris_metavars i
        let prompt = if quiet
                        then ""
                        else showMVs colour theme mvs ++
                             let str = mkPrompt mods ++ ">" in
                             (if colour then colourisePrompt theme str else str) ++ " "
        x <- H.catch (getInputLine prompt)
                     (ctrlC (return Nothing))
        case x of
            Nothing -> do lift $ when (not quiet) (iputStrLn "Bye bye")
                          return ()
            Just input -> -- H.catch
                do ms <- H.catch (lift $ processInput input orig mods)
                                 (ctrlC (return (Just mods))) 
                   case ms of
                        Just mods -> repl orig mods
                        Nothing -> return ()
--                             ctrlC)
--       ctrlC
   where ctrlC :: InputT Idris a -> SomeException -> InputT Idris a
         ctrlC act e = do lift $ iputStrLn (show e)
                          act -- repl orig mods

         showMVs c thm [] = ""
         showMVs c thm ms = "Metavariables: " ++ 
                                 show' 4 c thm (map fst ms) ++ "\n"

         show' 0 c thm ms = let l = length ms in
                          "... ( + " ++ show l
                             ++ " other"
                             ++ if l == 1 then ")" else "s)"
         show' n c thm [m] = showM c thm m
         show' n c thm (m : ms) = showM c thm m ++ ", " ++ 
                                  show' (n - 1) c thm ms

         showM c thm n = if c then colouriseFun thm (show n)
                              else show n

-- | Run the REPL server
startServer :: IState -> [FilePath] -> Idris ()
startServer orig fn_in = do tid <- runIO $ forkOS serverLoop
                            return ()
  where serverLoop :: IO ()
        -- TODO: option for port number
        serverLoop = withSocketsDo $
                              do sock <- listenOnLocalhost $ PortNumber 4294
                                 loop fn orig sock

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
                     (ist', fn) <- processNetCmd orig ist h fn cmd
                     hClose h
                     loop fn ist' sock
                   else do
                     putStrLn $ "Closing connection attempt from non-localhost " ++ host
                     hClose h

processNetCmd :: IState -> IState -> Handle -> FilePath -> String ->
                 IO (IState, FilePath)
processNetCmd orig i h fn cmd
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
             (sexp, id) <- case IdeSlave.parseMessage l of
                             Left err -> ierror err
                             Right (sexp, id) -> return (sexp, id)
             i <- getIState
             putIState $ i { idris_outputmode = (IdeSlave id) }
             idrisCatch -- to report correct id back!
               (do let fn = case mods of
                              (f:_) -> f
                              _ -> ""
                   case IdeSlave.sexpToCommand sexp of
                     Just (IdeSlave.Interpret cmd) ->
                       do c <- colourise
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
                     Just (IdeSlave.REPLCompletions str) ->
                       do (unused, compls) <- replCompletion (reverse str, "")
                          let good = IdeSlave.SexpList [IdeSlave.SymbolAtom "ok", IdeSlave.toSExp (map replacement compls, reverse unused)]
                          runIO $ putStrLn $ IdeSlave.convSExp "return" good id
                     Just (IdeSlave.LoadFile filename) ->
                       do clearErr
                          putIState (orig { idris_options = idris_options i,
                                            idris_outputmode = (IdeSlave id) })
                          loadInputs stdout [filename]
                          isetPrompt (mkPrompt [filename])
                          -- Report either success or failure
                          i <- getIState
                          case (errLine i) of
                            Nothing -> iPrintResult $ "loaded " ++ filename
                            Just x -> iPrintError $ "didn't load " ++ filename
                          ideslave orig [filename]
                     Just (IdeSlave.TypeOf name) ->
                       process stdout "(ideslave)" (Check (PRef (FC "(ideslave)" 0 0) (sUN name)))
                     Just (IdeSlave.CaseSplit line name) ->
                       process stdout fn (CaseSplitAt False line (sUN name))
                     Just (IdeSlave.AddClause line name) ->
                       process stdout fn (AddClauseFrom False line (sUN name))
                     Just (IdeSlave.AddProofClause line name) ->
                       process stdout fn (AddProofClauseFrom False line (sUN name))
                     Just (IdeSlave.AddMissing line name) ->
                       process stdout fn (AddMissing False line (sUN name))
                     Just (IdeSlave.MakeWithBlock line name) ->
                       process stdout fn (MakeWith False line (sUN name))
                     Just (IdeSlave.ProofSearch line name hints) ->
                       process stdout fn (DoProofSearch False line (sUN name) (map sUN hints))
                     Nothing -> do iPrintError "did not understand")
               (\e -> do iPrintError $ show e))
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
ideslaveProcess fn (TestInline t) = process stdout fn (TestInline t)

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
ideslaveProcess fn (SetOpt ShowOrigErr) = do process stdout fn (SetOpt ShowOrigErr)
                                             iPrintResult ""
ideslaveProcess fn (UnsetOpt ShowOrigErr) = do process stdout fn (UnsetOpt ShowOrigErr)
                                               iPrintResult ""
ideslaveProcess fn (SetOpt x) = process stdout fn (SetOpt x)
ideslaveProcess fn (UnsetOpt x) = process stdout fn (UnsetOpt x)
ideslaveProcess fn (CaseSplitAt False pos str) = process stdout fn (CaseSplitAt False pos str)
ideslaveProcess fn (AddProofClauseFrom False pos str) = process stdout fn (AddProofClauseFrom False pos str)
ideslaveProcess fn (AddClauseFrom False pos str) = process stdout fn (AddClauseFrom False pos str)
ideslaveProcess fn (AddMissing False pos str) = process stdout fn (AddMissing False pos str)
ideslaveProcess fn (MakeWith False pos str) = process stdout fn (MakeWith False pos str)
ideslaveProcess fn (DoProofSearch False pos str xs) = process stdout fn (DoProofSearch False pos str xs)
ideslaveProcess fn _ = iPrintError "command not recognized or not supported"


-- | The prompt consists of the currently loaded modules, or "Idris" if there are none
mkPrompt [] = "Idris"
mkPrompt [x] = "*" ++ dropExtension x
mkPrompt (x:xs) = "*" ++ dropExtension x ++ " " ++ mkPrompt xs

-- | Determine whether a file uses literate syntax
lit f = case splitExtension f of
            (_, ".lidr") -> True
            _ -> False

processInput :: String ->
                IState -> [FilePath] -> Idris (Maybe [FilePath])
processInput cmd orig inputs
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
                   mod <- loadInputs stdout [f]
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
--          clearOrigPats
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
                 = withErrorReflection $ do (tm, ty) <- elabVal toplevel False t
                                            ctxt <- getContext
                                            let tm' = force (normaliseAll ctxt [] tm)
                                            let ty' = force (normaliseAll ctxt [] ty)
                                            -- Add value to context, call it "it"
                                            updateContext (addCtxtDef (sUN "it") (Function ty' tm'))
                                            ist <- getIState
                                            logLvl 3 $ "Raw: " ++ show (tm', ty')
                                            logLvl 10 $ "Debug: " ++ showEnvDbg [] tm'
                                            let imp = opt_showimp (idris_options ist)
                                                tmDoc = prettyImp imp (delab ist tm')
                                                tyDoc = prettyImp imp (delab ist ty')
                                            ihPrintTermWithType h tmDoc tyDoc

process h fn (ExecVal t)
                  = do ctxt <- getContext
                       ist <- getIState
                       let imp = opt_showimp (idris_options ist)
                       (tm, ty) <- elabVal toplevel False t
--                       let tm' = normaliseAll ctxt [] tm
                       let ty' = normaliseAll ctxt [] ty
                       res <- execute tm
                       let (resOut, tyOut) = (prettyImp imp (delab ist res),
                                              prettyImp imp (delab ist ty'))
                       ihPrintTermWithType h resOut tyOut

process h fn (Check (PRef _ n))
   = do ctxt <- getContext
        ist <- getIState
        imp <- impShow
        case lookupNames n ctxt of
          ts@(t:_) ->
            case lookup t (idris_metavars ist) of
                Just (_, i, _) -> ihRenderResult h . fmap (fancifyAnnots ist) $
                                  showMetavarInfo imp ist n i
                Nothing -> ihPrintFunTypes h n (map (\n -> (n, delabTy ist n)) ts)
          [] -> ihPrintError h $ "No such variable " ++ show n
  where
    showMetavarInfo imp ist n i
         = case lookupTy n (tt_ctxt ist) of
                (ty:_) -> putTy imp ist i [] (delab ist ty)
    putTy :: Bool -> IState -> Int -> [(Name, Bool)] -> PTerm -> Doc OutputAnnotation
    putTy imp ist 0 bnd sc = putGoal imp ist bnd sc
    putTy imp ist i bnd (PPi _ n t sc)
               = let current = text "  " <>
                               (case n of
                                   MN _ _ -> text "_"
                                   UN nm | ('_':'_':_) <- str nm -> text "_"
                                   _ -> bindingOf n False) <+>
                               colon <+> align (tPretty bnd ist t) <> line
                 in
                    current <> putTy imp ist (i-1) ((n,False):bnd) sc
    putTy imp ist _ bnd sc = putGoal imp ist ((n,False):bnd) sc
    putGoal imp ist bnd g
               = text "--------------------------------------" <$>
                 annotate (AnnName n Nothing Nothing) (text $ show n) <+> colon <+>
                 align (tPretty bnd ist g)

    tPretty bnd ist t = pprintPTerm (opt_showimp (idris_options ist)) bnd t


process h fn (Check t)
   = do (tm, ty) <- elabVal toplevel False t
        ctxt <- getContext
        ist <- getIState
        let imp = opt_showimp (idris_options ist)
            ty' = normaliseC ctxt [] ty
        case tm of
           TType _ ->
             ihPrintTermWithType h (prettyImp imp PType) type1Doc
           _ -> ihPrintTermWithType h (prettyImp imp (delab ist tm))
                                      (prettyImp imp (delab ist ty))

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
             = let i' = i { idris_options = (idris_options i) { opt_showimp = True } }
               in iputStrLn (showTm i' (delab i lhs) ++ " = " ++
                             showTm i' (delab i rhs))
process h fn (TotCheck n)
                        = do i <- getIState
                             case lookupNameTotal n (tt_ctxt i) of
                                []  -> ihPrintError h $ "Unknown operator " ++ show n
                                ts  -> do ist <- getIState
                                          c <- colourise
                                          imp <- impShow
                                          let showN = showName (Just ist) [] imp c
                                          ihPrintResult h . concat . intersperse "\n" .
                                            map (\(n, t) -> showN n ++ " is " ++ showTotal t i) $
                                            ts


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
-- FIXME: There is far too much repetition in the cases below!
process h fn (CaseSplitAt updatefile l n)
   = do src <- runIO $ readFile fn
        res <- splitOnLine l n fn
        iLOG (showSep "\n" (map show res))
        let (before, (ap : later)) = splitAt (l-1) (lines src)
        res' <- replaceSplits ap res
        let new = concat res'
        if updatefile
          then do let fb = fn ++ "~" -- make a backup!
                  runIO $ writeFile fb (unlines before ++ new ++ unlines later)
                  runIO $ copyFile fb fn
          else -- do ihputStrLn h (show res)
            ihPrintResult h new
process h fn (AddClauseFrom updatefile l n)
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getClause l n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeFile fb (unlines (before ++ nonblank) ++
                                        replicate indent ' ' ++
                                        cl ++ "\n" ++
                                        unlines rest)
                  runIO $ copyFile fb fn
          else ihPrintResult h cl
    where
       getIndent i n [] = 0
       getIndent i n xs | take (length n) xs == n = i
       getIndent i n (x : xs) = getIndent (i + 1) n xs
process h fn (AddProofClauseFrom updatefile l n)
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getProofClause l n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeFile fb (unlines (before ++ nonblank) ++
                                        replicate indent ' ' ++
                                        cl ++ "\n" ++
                                        unlines rest)
                  runIO $ copyFile fb fn
          else ihPrintResult h cl
    where
       getIndent i n [] = 0
       getIndent i n xs | take (length n) xs == n = i
       getIndent i n (x : xs) = getIndent (i + 1) n xs
process h fn (AddMissing updatefile l n)
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        i <- getIState
        cl <- getInternalApp fn l
        let n' = getAppName cl

        extras <- case lookupCtxt n' (idris_patdefs i) of
                       [] -> return ""
                       [(_, tms)] -> do tms' <- nameMissing tms
                                        showNew (show n ++ "_rhs") 1 indent tms'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeFile fb (unlines (before ++ nonblank)
                                        ++ extras ++ unlines rest)
                  runIO $ copyFile fb fn
          else ihPrintResult h extras
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

          showNew nm i ind (tm : tms)
                        = do (nm', i') <- getUniq nm i
                             rest <- showNew nm i' ind tms
                             return (replicate ind ' ' ++
                                     showPat tm ++ " = ?" ++ nm' ++
                                     "\n" ++ rest)
          showNew nm i _ [] = return ""

          getIndent i n [] = 0
          getIndent i n xs | take (length n) xs == n = i
          getIndent i n (x : xs) = getIndent (i + 1) n xs

process h fn (MakeWith updatefile l n)
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let ind = getIndent tyline
        let with = mkWith tyline n
        -- add clause before first blank line in 'later',
        -- or (TODO) before first line with same indentation as tyline
        let (nonblank, rest) = span (\x -> not (all isSpace x) &&
                                           not (ind == getIndent x)) later
        if updatefile then
           do let fb = fn ++ "~"
              runIO $ writeFile fb (unlines (before ++ nonblank)
                                        ++ with ++ "\n" ++
                                    unlines rest)
              runIO $ copyFile fb fn
           else ihPrintResult h with
  where getIndent s = length (takeWhile isSpace s)
    
process h fn (DoProofSearch updatefile l n hints)
    = do src <- runIO $ readFile fn
         let (before, tyline : later) = splitAt (l-1) (lines src)
         ctxt <- getContext
         mn <- case lookupNames n ctxt of
                    [x] -> return x
                    [] -> return n
                    ns -> ierror (CantResolveAlts (map show ns))
         i <- getIState
         let (top, envlen, _) = case lookup mn (idris_metavars i) of
                                  Just (t, e, False) -> (t, e, False)
                                  _ -> (Nothing, 0, True)
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
                                     updateMeta False tyline (show n) newmv ++ "\n"
                                       ++ unlines later)
               runIO $ copyFile fb fn
            else ihPrintResult h newmv
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

          updateMeta brack ('?':cs) n new
            | length cs >= length n
              = case splitAt (length n) cs of
                     (mv, c:cs) ->
                          if ((isSpace c || c == ')' || c == '}') && mv == n)
                             then addBracket brack new ++ (c : cs)
                             else '?' : mv ++ c : updateMeta True cs n new
                     (mv, []) -> if (mv == n) then addBracket brack new else '?' : mv
          updateMeta brack ('=':cs) n new = '=':updateMeta False cs n new
          updateMeta brack (c:cs) n new 
              = c : updateMeta (brack || not (isSpace c)) cs n new
          updateMeta brack [] n new = ""

          addBracket False new = new
          addBracket True new@('(':xs) | last xs == ')' = new
          addBracket True new | any isSpace new = '(' : new ++ ")"
                              | otherwise = new

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
                                 putIState $ i { idris_metavars = (n, (Nothing, 0, False)) : ms }

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
          let ns = lookupNames n' ctxt
          let metavars = mapMaybe (\n -> do c <- lookup n (idris_metavars ist); return (n, c)) ns
          n <- case metavars of
              [] -> ierror (Msg $ "Cannot find metavariable " ++ show n')
              [(n, (_,_,False))] -> return n
              [(_, (_,_,True))]  -> ierror (Msg $ "Declarations not solvable using prover")
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
                                iPrintResult (showTm ist (delab ist tm'))
process h fn Execute
                   = do (m, _) <- elabVal toplevel False
                                        (PApp fc
                                           (PRef fc (sUN "run__IO"))
                                           [pexp $ PRef fc (sNS (sUN "main") ["Main"])])
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
                       (PApp fc (PRef fc (sUN "run__IO"))
                       [pexp $ PRef fc (sNS (sUN "main") ["Main"])])
           compile codegen f m
  where fc = fileFC "main"
process h fn (LogLvl i) = setLogLevel i
-- Elaborate as if LHS of a pattern (debug command)
process h fn (Pattelab t)
     = do (tm, ty) <- elabVal toplevel True t
          iPrintResult $ show tm ++ "\n\n : " ++ show ty

process h fn (Missing n)
    = do i <- getIState
         let i' = i { idris_options = (idris_options i) { opt_showimp = True } }
         case lookupCtxt n (idris_patdefs i) of
                  [] -> return ()
                  [(_, tms)] ->
                       iPrintResult (showSep "\n" (map (showTm i') tms))
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

process h fn (SetOpt   ErrContext)  = setErrContext True
process h fn (UnsetOpt ErrContext)  = setErrContext False
process h fn (SetOpt ShowImpl)      = setImpShow True
process h fn (UnsetOpt ShowImpl)    = setImpShow False
process h fn (SetOpt ShowOrigErr)   = setShowOrigErr True
process h fn (UnsetOpt ShowOrigErr) = setShowOrigErr False

process h fn (SetOpt _) = iPrintError "Not a valid option"
process h fn (UnsetOpt _) = iPrintError "Not a valid option"
process h fn (SetColour ty c) = setColour ty c
process h fn ColourOn
                    = do ist <- getIState
                         putIState $ ist { idris_colourRepl = True }
process h fn ColourOff
                     = do ist <- getIState
                          putIState $ ist { idris_colourRepl = False }
process h fn ListErrorHandlers =
  do ist <- getIState
     case idris_errorhandlers ist of
       [] -> iPrintResult "No registered error handlers"
       handlers ->
           iPrintResult $ "Registered error handlers: " ++ (concat . intersperse ", " . map show) handlers
process h fn (SetConsoleWidth w) = setWidth w


classInfo :: ClassInfo -> Idris ()
classInfo ci = do iputStrLn "Methods:\n"
                  mapM_ dumpMethod (class_methods ci)
                  iputStrLn ""
                  iputStrLn "Default superclass instances:\n"
                  mapM_ dumpDefaultInstance (class_default_superclasses ci)
                  iputStrLn ""
                  iputStrLn "Instances:\n"
                  mapM_ dumpInstance (class_instances ci)
                  iPrintResult ""

dumpMethod :: (Name, (FnOpts, PTerm)) -> Idris ()
dumpMethod (n, (_, t)) = iputStrLn $ show n ++ " : " ++ show t

dumpDefaultInstance :: PDecl -> Idris ()
dumpDefaultInstance (PInstance _ _ _ _ _ t _ _) = iputStrLn $ show t

dumpInstance :: Name -> Idris ()
dumpInstance n = do i <- getIState
                    ctxt <- getContext
                    case lookupTy n ctxt of
                         ts -> mapM_ (\t -> iputStrLn $ showTm i (delab i t)) ts

showTotal :: Totality -> IState -> String
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
parseArgs ("--nobanner":ns)      = NoBanner : (parseArgs ns)
parseArgs ("--quiet":ns)         = Quiet : (parseArgs ns)
parseArgs ("--ideslave":ns)      = Ideslave : (parseArgs ns)
parseArgs ("--client":ns)        = [Client (showSep " " ns)]
parseArgs ("--log":lvl:ns)       = OLogging (read lvl) : (parseArgs ns)
parseArgs ("--nobasepkgs":ns)    = NoBasePkgs : (parseArgs ns)
parseArgs ("--noprelude":ns)     = NoPrelude : (parseArgs ns)
parseArgs ("--nobuiltins":ns)    = NoBuiltins : NoPrelude : (parseArgs ns)
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
-- Package Related options
parseArgs ("--package":n:ns)     = Pkg n : (parseArgs ns)
parseArgs ("-p":n:ns)            = Pkg n : (parseArgs ns)
parseArgs ("--build":n:ns)       = PkgBuild n : (parseArgs ns)
parseArgs ("--install":n:ns)     = PkgInstall n : (parseArgs ns)
parseArgs ("--repl":n:ns)        = PkgREPL n : (parseArgs ns)
parseArgs ("--clean":n:ns)       = PkgClean n : (parseArgs ns)
parseArgs ("--checkpkg":n:ns)    = PkgCheck n : (parseArgs ns)
-- Misc Options
parseArgs ("--bytecode":n:ns)    = NoREPL : BCAsm n : (parseArgs ns)
parseArgs ("-S":ns)              = OutputTy Raw : (parseArgs ns)
parseArgs ("-c":ns)              = OutputTy Object : (parseArgs ns)
parseArgs ("--mvn":ns)           = OutputTy MavenProject : (parseArgs ns)
parseArgs ("--dumpdefuns":n:ns)  = DumpDefun n : (parseArgs ns)
parseArgs ("--dumpcases":n:ns)   = DumpCases n : (parseArgs ns)
parseArgs ("--codegen":n:ns)     = UseCodegen (parseCodegen n) : (parseArgs ns)
parseArgs ["--exec"]             = InterpretScript "Main.main" : []
parseArgs ("--exec":expr:ns)     = InterpretScript expr : parseArgs ns
parseArgs (('-':'X':extName):ns) = case maybeRead extName of
  Just ext -> Extension ext : parseArgs ns
  -- Not sure what to do for the Nothing case
  Nothing -> error ("Unknown extension " ++ extName)
  where maybeRead = fmap fst . listToMaybe . reads
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
idris :: [Opt] -> IO (Maybe IState)
idris opts = do res <- runErrorT $ execStateT (idrisMain opts) idrisInit
                case res of
                  Left err -> do putStrLn $ pshow idrisInit err
                                 return Nothing
                  Right ist -> return (Just ist)


loadInputs :: Handle -> [FilePath] -> Idris ()
loadInputs h inputs
  = idrisCatch
       (do ist <- getIState
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
           ifiles <- mapWhileOK (\(num, input) ->
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
           putIState inew)
        (\e -> do i <- getIState
                  case e of
                    At f _ -> do setErrLine (fc_line f)
                                 iputStrLn (show e)
                    ProgramLineComment -> return () -- fail elsewhere
                    _ -> do setErrLine 3 -- FIXME! Propagate it
                            iputStrLn (pshow i e))
   where -- load all files, stop if any fail
         tryLoad :: [IFileType] -> Idris ()
         tryLoad [] = return ()
         tryLoad (f : fs) = do loadFromIFile h f
                               ok <- noErrors
                               when ok $ tryLoad fs

         ibc (IBC _ _) = True
         ibc _ = False

         -- Like mapM, but give up when there's an error
         mapWhileOK f [] = return []
         mapWhileOK f (x : xs) = do x' <- f x
                                    ok <- noErrors
                                    if ok then do xs' <- mapWhileOK f xs
                                                  return (x' : xs')
                                          else return [x']

idrisMain :: [Opt] -> Idris ()
idrisMain opts =
    do let inputs = opt getFile opts
       let quiet = Quiet `elem` opts
       let nobanner = NoBanner `elem` opts
       let idesl = Ideslave `elem` opts
       let runrepl = not (NoREPL `elem` opts)
       let verbose = runrepl || Verbose `elem` opts
       let output = opt getOutput opts
       let ibcsubdir = opt getIBCSubDir opts
       let importdirs = opt getImportDir opts
       let bcs = opt getBC opts
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
       setVerbose verbose
       setCmdLine opts
       setOutputTy outty
       setCodegen cgn
       setTargetTriple trpl
       setTargetCPU tcpu
       setOptLevel optimize
       mapM_ makeOption opts
       -- if we have the --bytecode flag, drop into the bytecode assembler
       case bcs of
         [] -> return ()
         xs -> return () -- runIO $ mapM_ bcAsm xs
       case ibcsubdir of
         [] -> setIBCSubDir ""
         (d:_) -> setIBCSubDir d
       setImportDirs importdirs

       when (not (NoBasePkgs `elem` opts)) $ do
           addPkgDir "prelude"
           addPkgDir "base"
       mapM_ addPkgDir pkgdirs
       elabPrims
       when (not (NoBuiltins `elem` opts)) $ do x <- loadModule stdout "Builtins"
                                                return ()
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule stdout "Prelude"
                                               return ()
       when (runrepl && not quiet && not idesl && not (isJust script) && not nobanner) $ iputStrLn banner

       orig <- getIState
       loadInputs stdout inputs

       runIO $ hSetBuffering stdout LineBuffering

       ok <- noErrors
       when ok $ case output of
                    [] -> return ()
                    (o:_) -> idrisCatch (process stdout "" (Compile cgn o))
                               (\e -> do ist <- getIState ; iputStrLn $ pshow ist e)
       case script of
         Nothing -> return ()
         Just expr -> execScript expr

       -- Create Idris data dir + repl history and config dir
       idrisCatch (do dir <- getIdrisUserDataDir
                      exists <- runIO $ doesDirectoryExist dir
                      unless exists $ iLOG ("Creating " ++ dir)
                      runIO $ createDirectoryIfMissing True (dir </> "repl"))
         (\e -> return ())

       historyFile <- fmap (</> "repl" </> "history") getIdrisUserDataDir

       when (runrepl && not idesl) $ do
--          clearOrigPats
         initScript
         startServer orig inputs
         runInputT (replSettings (Just historyFile)) $ repl orig inputs
       when (idesl) $ ideslaveStart orig inputs
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

getPkgREPL :: Opt -> Maybe String
getPkgREPL (PkgREPL str) = Just str
getPkgREPL _ = Nothing

getPkgCheck :: Opt -> Maybe String
getPkgCheck (PkgCheck str) = Just str
getPkgCheck _              = Nothing

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

ver = showVersion version ++ gitHash

banner = "     ____    __     _                                          \n" ++
         "    /  _/___/ /____(_)____                                     \n" ++
         "    / // __  / ___/ / ___/     Version " ++ ver ++ "\n" ++
         "  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      \n" ++
         " /___/\\__,_/_/  /_/____/       Type :? for help                \n"



{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards, CPP #-}

module Idris.REPL where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Apropos (apropos)
import Idris.REPLParser
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Erasure
import Idris.Error
import Idris.ErrReverse
import Idris.Delaborate
import Idris.Docstrings (Docstring, overview, renderDocstring)
import Idris.IdrisDoc
import Idris.Prover
import Idris.Parser hiding (indent)
import Idris.Primitives
import Idris.Coverage
import Idris.Docs hiding (Doc)
import Idris.Help
import Idris.Completion
import qualified Idris.IdeSlave as IdeSlave
import Idris.Chaser
import Idris.Imports
import Idris.Colours hiding (colourise)
import Idris.Inliner
import Idris.CaseSplit
import Idris.DeepSeq
import Idris.Output
import Idris.Interactive
import Idris.WhoCalls
import Idris.TypeSearch (searchByType)

import Idris.Elab.Type
import Idris.Elab.Clause
import Idris.Elab.Data
import Idris.Elab.Value

import Version_idris (gitHash)
import Util.System
import Util.DynamicLinker
import Util.Net (listenOnLocalhost, listenOnLocalhostAnyPort)
import Util.Pretty hiding ((</>))

import Idris.Core.Evaluate
import Idris.Core.Execute (execute)
import Idris.Core.TT
import Idris.Core.Constraints

import IRTS.Compiler
import IRTS.CodegenCommon
import IRTS.System

import Control.Category
import Prelude hiding ((.), id)
import Data.List.Split (splitOn)
import Data.List (groupBy)
import qualified Data.Text as T

import Text.Trifecta.Result(Result(..))

-- import RTS.SC
-- import RTS.Bytecode
-- import RTS.PreC
-- import RTS.CodegenC
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
import Data.Either (partitionEithers)
import Control.DeepSeq

import Numeric ( readHex )

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
                                 loop fn orig { idris_colourRepl = False } sock

        fn = case fn_in of
                  (f:_) -> f
                  _ -> ""

        loop fn ist sock
            = do (h,_,_) <- accept sock
                 hSetEncoding h utf8
                 cmd <- hGetLine h
                 let isth = case idris_outputmode ist of
                              RawOutput _ -> ist {idris_outputmode = RawOutput h}
                              IdeSlave n _ -> ist {idris_outputmode = IdeSlave n h}
                 (ist', fn) <- processNetCmd orig isth h fn cmd
                 hClose h
                 loop fn ist' sock

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
    processNet fn Reload = processNet fn (Load fn Nothing)
    processNet fn (Load f toline) =
        do let ist = orig { idris_options = idris_options i
                          , idris_colourTheme = idris_colourTheme i
                          , idris_colourRepl = False
                          }
           putIState ist
           setErrContext True
           setOutH h
           setQuiet True
           setVerbose False
           mods <- loadInputs [f] toline
           ist <- getIState
           return (ist, f)
    processNet fn c = do process fn c
                         ist <- getIState
                         return (ist, fn)
    setOutH :: Handle -> Idris ()
    setOutH h =
      do ist <- getIState
         putIState $ case idris_outputmode ist of
           RawOutput _ -> ist {idris_outputmode = RawOutput h}
           IdeSlave n _ -> ist {idris_outputmode = IdeSlave n h}

-- | Run a command on the server on localhost
runClient :: String -> IO ()
runClient str = withSocketsDo $ do
                  h <- connectTo "localhost" (PortNumber 4294)
                  hSetEncoding h utf8
                  hPutStrLn h str
                  resp <- hGetResp "" h
                  putStr resp
                  hClose h
    where hGetResp acc h = do eof <- hIsEOF h
                              if eof then return acc
                                     else do l <- hGetLine h
                                             hGetResp (acc ++ l ++ "\n") h

initIdeslaveSocket :: IO Handle
initIdeslaveSocket = do
  (sock, port) <- listenOnLocalhostAnyPort
  putStrLn $ show port
  (h, _, _) <- accept sock
  hSetEncoding h utf8
  return h

-- | Run the IdeSlave
ideslaveStart :: Bool -> IState -> [FilePath] -> Idris ()
ideslaveStart s orig mods
  = do h <- runIO $ if s then initIdeslaveSocket else return stdout
       setIdeSlave True h
       i <- getIState
       case idris_outputmode i of
         IdeSlave n h ->
           do runIO $ hPutStrLn h $ IdeSlave.convSExp "protocol-version" IdeSlave.ideSlaveEpoch n
              case mods of
                a:_ -> runIdeSlaveCommand h n i "" [] (IdeSlave.LoadFile a Nothing)
                _   -> return ()
       ideslave h orig mods

ideslave :: Handle -> IState -> [FilePath] -> Idris ()
ideslave h orig mods
  = do idrisCatch
         (do let inh = if h == stdout then stdin else h
             len' <- runIO $ IdeSlave.getLen inh
             len <- case len' of
               Left err -> ierror err
               Right n  -> return n
             l <- runIO $ IdeSlave.getNChar inh len ""
             (sexp, id) <- case IdeSlave.parseMessage l of
                             Left err -> ierror err
                             Right (sexp, id) -> return (sexp, id)
             i <- getIState
             putIState $ i { idris_outputmode = (IdeSlave id h) }
             idrisCatch -- to report correct id back!
               (do let fn = case mods of
                              (f:_) -> f
                              _     -> ""
                   case IdeSlave.sexpToCommand sexp of
                     Just cmd -> runIdeSlaveCommand h id orig fn mods cmd
                     Nothing  -> iPrintError "did not understand" )
               (\e -> do iPrintError $ show e))
         (\e -> do iPrintError $ show e)
       ideslave h orig mods

-- | Run IDESlave commands
runIdeSlaveCommand :: Handle -- ^^ The handle for communication
                   -> Integer -- ^^ The continuation ID for the client
                   -> IState -- ^^ The original IState
                   -> FilePath -- ^^ The current open file
                   -> [FilePath] -- ^^ The currently loaded modules
                   -> IdeSlave.IdeSlaveCommand -- ^^ The command to process
                   -> Idris ()
runIdeSlaveCommand h id orig fn mods (IdeSlave.Interpret cmd) =
  do c <- colourise
     i <- getIState
     case parseCmd i "(input)" cmd of
       Failure err -> iPrintError $ show (fixColour False err)
       Success (Prove n') ->
         idrisCatch
           (do process fn (Prove n')
               isetPrompt (mkPrompt mods)
               case idris_outputmode i of
                 IdeSlave n h -> -- signal completion of proof to ide
                   runIO . hPutStrLn h $
                     IdeSlave.convSExp "return"
                       (IdeSlave.SymbolAtom "ok", "")
                       n
                 _ -> return ())
           (\e -> do ist <- getIState
                     isetPrompt (mkPrompt mods)
                     case idris_outputmode i of
                       IdeSlave n h ->
                         runIO . hPutStrLn h $
                           IdeSlave.convSExp "abandon-proof" "Abandoned" n
                       _ -> return ()
                     iRenderError $ pprintErr ist e)
       Success cmd -> idrisCatch
                        (ideslaveProcess fn cmd)
                        (\e -> getIState >>= iRenderError . flip pprintErr e)
runIdeSlaveCommand h id orig fn mods (IdeSlave.REPLCompletions str) =
  do (unused, compls) <- replCompletion (reverse str, "")
     let good = IdeSlave.SexpList [IdeSlave.SymbolAtom "ok",
                                   IdeSlave.toSExp (map replacement compls,
                                   reverse unused)]
     runIO . hPutStrLn h $ IdeSlave.convSExp "return" good id
runIdeSlaveCommand h id orig fn mods (IdeSlave.LoadFile filename toline) =
  do i <- getIState
     clearErr
     putIState (orig { idris_options = idris_options i,
                       idris_outputmode = (IdeSlave id h) })
     loadInputs [filename] toline
     isetPrompt (mkPrompt [filename])
     -- Report either success or failure
     i <- getIState
     case (errSpan i) of
       Nothing -> let msg = maybe (IdeSlave.SexpList [IdeSlave.SymbolAtom "ok",
                                                      IdeSlave.SexpList []])
                                  (\fc -> IdeSlave.SexpList [IdeSlave.SymbolAtom "ok",
                                                             IdeSlave.toSExp fc])
                                  (idris_parsedSpan i)
                  in runIO . hPutStrLn h $ IdeSlave.convSExp "return" msg id
       Just x -> iPrintError $ "didn't load " ++ filename
     ideslave h orig [filename]
runIdeSlaveCommand h id orig fn mods (IdeSlave.TypeOf name) =
  case splitName name of
    Left err -> iPrintError err
    Right n -> process "(ideslave)"
                 (Check (PRef (FC "(ideslave)" (0,0) (0,0)) n))
  where splitName :: String -> Either String Name
        splitName s = case reverse $ splitOn "." s of
                        [] -> Left ("Didn't understand name '" ++ s ++ "'")
                        [n] -> Right $ sUN n
                        (n:ns) -> Right $ sNS (sUN n) ns
runIdeSlaveCommand h id orig fn mods (IdeSlave.DocsFor name) =
  case parseConst orig name of
    Success c -> process "(ideslave)" (DocStr (Right c))
    Failure _ ->
     case splitName name of
       Left err -> iPrintError err
       Right n -> process "(ideslave)" (DocStr (Left n))
runIdeSlaveCommand h id orig fn mods (IdeSlave.CaseSplit line name) =
  process fn (CaseSplitAt False line (sUN name))
runIdeSlaveCommand h id orig fn mods (IdeSlave.AddClause line name) =
  process fn (AddClauseFrom False line (sUN name))
runIdeSlaveCommand h id orig fn mods (IdeSlave.AddProofClause line name) =
  process fn (AddProofClauseFrom False line (sUN name))
runIdeSlaveCommand h id orig fn mods (IdeSlave.AddMissing line name) =
  process fn (AddMissing False line (sUN name))
runIdeSlaveCommand h id orig fn mods (IdeSlave.MakeWithBlock line name) =
  process fn (MakeWith False line (sUN name))
runIdeSlaveCommand h id orig fn mods (IdeSlave.ProofSearch r line name hints depth) =
  doProofSearch fn False r line (sUN name) (map sUN hints) depth
runIdeSlaveCommand h id orig fn mods (IdeSlave.MakeLemma line name) =
  case splitName name of
    Left err -> iPrintError err
    Right n -> process fn (MakeLemma False line n)
runIdeSlaveCommand h id orig fn mods (IdeSlave.Apropos a) =
  process fn (Apropos a)
runIdeSlaveCommand h id orig fn mods (IdeSlave.GetOpts) =
  do ist <- getIState
     let opts = idris_options ist
     let impshow = opt_showimp opts
     let errCtxt = opt_errContext opts
     let options = (IdeSlave.SymbolAtom "ok",
                    [(IdeSlave.SymbolAtom "show-implicits", impshow),
                     (IdeSlave.SymbolAtom "error-context", errCtxt)])
     runIO . hPutStrLn h $ IdeSlave.convSExp "return" options id
runIdeSlaveCommand h id orig fn mods (IdeSlave.SetOpt IdeSlave.ShowImpl b) =
  do setImpShow b
     let msg = (IdeSlave.SymbolAtom "ok", b)
     runIO . hPutStrLn h $ IdeSlave.convSExp "return" msg id
runIdeSlaveCommand h id orig fn mods (IdeSlave.SetOpt IdeSlave.ErrContext b) =
  do setErrContext b
     let msg = (IdeSlave.SymbolAtom "ok", b)
     runIO . hPutStrLn h $ IdeSlave.convSExp "return" msg id
runIdeSlaveCommand h id orig fn mods (IdeSlave.Metavariables cols) =
  do ist <- getIState
     let mvs = reverse $ map fst (idris_metavars ist) \\ primDefs
     let ppo = ppOptionIst ist
     -- splitMvs is a list of pairs of names and their split types
     let splitMvs = mapSnd (splitPi ist) (mvTys ist mvs)
     -- mvOutput is the pretty-printed version ready for conversion to SExpr
     let mvOutput = map (\(n, (hs, c)) -> (n, hs, c)) $
                    mapPair show
                            (\(hs, c, pc) ->
                             let bnd = [ n | (n,_,_) <- hs ] in
                             let bnds = inits bnd in
                             (map (\(bnd, h) -> processPremise ist bnd h)
                                  (zip bnds hs),
                              render ist bnd c pc))
                            splitMvs
     runIO . hPutStrLn h $
       IdeSlave.convSExp "return" (IdeSlave.SymbolAtom "ok", mvOutput) id
  where mapPair f g xs = zip (map (f . fst) xs) (map (g . snd) xs)
        mapSnd f xs = zip (map fst xs) (map (f . snd) xs)

        -- | Split a function type into a pair of premises, conclusion.
        -- Each maintains both the original and delaborated versions.
        splitPi :: IState -> Type -> ([(Name, Type, PTerm)], Type, PTerm)
        splitPi ist (Bind n (Pi t) rest) =
          let (hs, c, pc) = splitPi ist rest in
            ((n, t, delabTy' ist [] t False False):hs,
             c, delabTy' ist [] c False False)
        splitPi ist tm = ([], tm, delabTy' ist [] tm False False)

        -- | Get the types of a list of metavariable names
        mvTys :: IState -> [Name] -> [(Name, Type)]
        mvTys ist = mapSnd vToP . mapMaybe (flip lookupTyNameExact (tt_ctxt ist))

        -- | Show a type and its corresponding PTerm in a format suitable
        -- for the IDE - that is, pretty-printed and annotated.
        render :: IState -> [Name] -> Type -> PTerm -> (String, SpanList OutputAnnotation)
        render ist bnd t pt =
          let prettyT = pprintPTerm (ppOptionIst ist)
                                    (zip bnd (repeat False))
                                    []
                                    (idris_infixes ist)
                                    pt
          in
            displaySpans .
            renderPretty 0.9 cols .
            fmap (fancifyAnnots ist) .
            annotate (AnnTerm (zip bnd (take (length bnd) (repeat False))) t) $
              prettyT

        -- | Juggle the bits of a premise to prepare for output.
        processPremise :: IState
                       -> [Name] -- ^ the names to highlight as bound
                       -> (Name, Type, PTerm)
                       -> (String,
                           String,
                           SpanList OutputAnnotation)
        processPremise ist bnd (n, t, pt) =
          let (out, spans) = render ist bnd t pt in
          (show n , out, spans)

runIdeSlaveCommand h id orig fn mods (IdeSlave.WhoCalls n) =
  case splitName n of
       Left err -> iPrintError err
       Right n -> do calls <- whoCalls n
                     ist <- getIState
                     let msg = (IdeSlave.SymbolAtom "ok",
                                map (\ (n,ns) -> (pn ist n, map (pn ist) ns)) calls)
                     runIO . hPutStrLn h $ IdeSlave.convSExp "return" msg id
  where pn ist = displaySpans .
                 renderPretty 0.9 1000 .
                 fmap (fancifyAnnots ist) .
                 prettyName True True []
runIdeSlaveCommand h id orig fn mods (IdeSlave.CallsWho n) =
  case splitName n of
       Left err -> iPrintError err
       Right n -> do calls <- callsWho n
                     ist <- getIState
                     let msg = (IdeSlave.SymbolAtom "ok",
                                map (\ (n,ns) -> (pn ist n, map (pn ist) ns)) calls)
                     runIO . hPutStrLn h $ IdeSlave.convSExp "return" msg id
  where pn ist = displaySpans .
                 renderPretty 0.9 1000 .
                 fmap (fancifyAnnots ist) .
                 prettyName True True []

runIdeSlaveCommand h id orig fn modes (IdeSlave.TermNormalise bnd tm) =
  do ctxt <- getContext
     ist <- getIState
     let tm' = force (normaliseAll ctxt [] tm)
         ptm = annotate (AnnTerm bnd tm')
               (pprintPTerm (ppOptionIst ist)
                            bnd
                            []
                            (idris_infixes ist)
                            (delab ist tm'))
         msg = (IdeSlave.SymbolAtom "ok",
                displaySpans .
                renderPretty 0.9 80 .
                fmap (fancifyAnnots ist) $ ptm)
     runIO . hPutStrLn h $ IdeSlave.convSExp "return" msg id
runIdeSlaveCommand h id orig fn modes (IdeSlave.TermShowImplicits bnd tm) =
  ideSlaveForceTermImplicits h id bnd True tm
runIdeSlaveCommand h id orig fn modes (IdeSlave.TermNoImplicits bnd tm) =
  ideSlaveForceTermImplicits h id bnd False tm

-- | Show a term for IDESlave with the specified implicitness
ideSlaveForceTermImplicits :: Handle -> Integer -> [(Name, Bool)] -> Bool -> Term -> Idris ()
ideSlaveForceTermImplicits h id bnd impl tm =
  do ist <- getIState
     let expl = annotate (AnnTerm bnd tm)
                (pprintPTerm ((ppOptionIst ist) { ppopt_impl = impl })
                             bnd [] (idris_infixes ist)
                             (delab ist tm))
         msg = (IdeSlave.SymbolAtom "ok",
                displaySpans .
                renderPretty 0.9 80 .
                fmap (fancifyAnnots ist) $ expl)
     runIO . hPutStrLn h $ IdeSlave.convSExp "return" msg id

splitName :: String -> Either String Name
splitName s = case reverse $ splitOn "." s of
                [] -> Left ("Didn't understand name '" ++ s ++ "'")
                [n] -> Right $ sUN n
                (n:ns) -> Right $ sNS (sUN n) ns

ideslaveProcess :: FilePath -> Command -> Idris ()
ideslaveProcess fn Warranty = process fn Warranty
ideslaveProcess fn Help = process fn Help
ideslaveProcess fn (ChangeDirectory f) = do process fn (ChangeDirectory f)
                                            iPrintResult "changed directory to"
ideslaveProcess fn (Eval t) = process fn (Eval t)
ideslaveProcess fn (NewDefn decls) = do process fn (NewDefn decls)
                                        iPrintResult "defined"
ideslaveProcess fn (ExecVal t) = process fn (ExecVal t)
ideslaveProcess fn (Check (PRef x n)) = process fn (Check (PRef x n))
ideslaveProcess fn (Check t) = process fn (Check t)
ideslaveProcess fn (DocStr n) = process fn (DocStr n)
ideslaveProcess fn Universes = process fn Universes
ideslaveProcess fn (Defn n) = do process fn (Defn n)
                                 iPrintResult ""
ideslaveProcess fn (TotCheck n) = process fn (TotCheck n)
ideslaveProcess fn (DebugInfo n) = do process fn (DebugInfo n)
                                      iPrintResult ""
ideslaveProcess fn (Search t) = process fn (Search t)
ideslaveProcess fn (Spec t) = process fn (Spec t)
-- RmProof and AddProof not supported!
ideslaveProcess fn (ShowProof n') = process fn (ShowProof n')
ideslaveProcess fn (HNF t) = process fn (HNF t)
--ideslaveProcess fn TTShell = process fn TTShell -- need some prove mode!
ideslaveProcess fn (TestInline t) = process fn (TestInline t)

ideslaveProcess fn Execute = do process fn Execute
                                iPrintResult ""
ideslaveProcess fn (Compile codegen f) = do process fn (Compile codegen f)
                                            iPrintResult ""
ideslaveProcess fn (LogLvl i) = do process fn (LogLvl i)
                                   iPrintResult ""
ideslaveProcess fn (Pattelab t) = process fn (Pattelab t)
ideslaveProcess fn (Missing n) = process fn (Missing n)
ideslaveProcess fn (DynamicLink l) = do process fn (DynamicLink l)
                                        iPrintResult ""
ideslaveProcess fn ListDynamic = do process fn ListDynamic
                                    iPrintResult ""
ideslaveProcess fn Metavars = process fn Metavars
ideslaveProcess fn (SetOpt ErrContext) = do process fn (SetOpt ErrContext)
                                            iPrintResult ""
ideslaveProcess fn (UnsetOpt ErrContext) = do process fn (UnsetOpt ErrContext)
                                              iPrintResult ""
ideslaveProcess fn (SetOpt ShowImpl) = do process fn (SetOpt ShowImpl)
                                          iPrintResult ""
ideslaveProcess fn (UnsetOpt ShowImpl) = do process fn (UnsetOpt ShowImpl)
                                            iPrintResult ""
ideslaveProcess fn (SetOpt ShowOrigErr) = do process fn (SetOpt ShowOrigErr)
                                             iPrintResult ""
ideslaveProcess fn (UnsetOpt ShowOrigErr) = do process fn (UnsetOpt ShowOrigErr)
                                               iPrintResult ""
ideslaveProcess fn (SetOpt x) = process fn (SetOpt x)
ideslaveProcess fn (UnsetOpt x) = process fn (UnsetOpt x)
ideslaveProcess fn (CaseSplitAt False pos str) = process fn (CaseSplitAt False pos str)
ideslaveProcess fn (AddProofClauseFrom False pos str) = process fn (AddProofClauseFrom False pos str)
ideslaveProcess fn (AddClauseFrom False pos str) = process fn (AddClauseFrom False pos str)
ideslaveProcess fn (AddMissing False pos str) = process fn (AddMissing False pos str)
ideslaveProcess fn (MakeWith False pos str) = process fn (MakeWith False pos str)
ideslaveProcess fn (DoProofSearch False r pos str xs) = process fn (DoProofSearch False r pos str xs)
ideslaveProcess fn (SetConsoleWidth w) = do process fn (SetConsoleWidth w)
                                            iPrintResult ""
ideslaveProcess fn (Apropos a) = do process fn (Apropos a)
                                    iPrintResult ""
ideslaveProcess fn (WhoCalls n) = process fn (WhoCalls n)
ideslaveProcess fn (CallsWho n) = process fn (CallsWho n)
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
                   mods <- loadInputs inputs Nothing
                   return (Just inputs)
            Success (Load f toline) ->
                do putIState orig { idris_options = idris_options i
                                  , idris_colourTheme = idris_colourTheme i
                                  }
                   clearErr
                   mod <- loadInputs [f] toline
                   return (Just [f])
            Success (ModImport f) ->
                do clearErr
                   fmod <- loadModule f
                   return (Just (inputs ++ [fmod]))
            Success Edit -> do -- takeMVar stvar
                               edit fn orig
                               return (Just inputs)
            Success Proofs -> do proofs orig
                                 return (Just inputs)
            Success Quit -> do when (not quiet) (iputStrLn "Bye bye")
                               return Nothing
            Success cmd  -> do idrisCatch (process fn cmd)
                                          (\e -> do msg <- showErr e ; iputStrLn msg)
                               return (Just inputs)

resolveProof :: Name -> Idris Name
resolveProof n'
  = do i <- getIState
       ctxt <- getContext
       n <- case lookupNames n' ctxt of
                 [x] -> return x
                 [] -> return n'
                 ns -> ierror (CantResolveAlts ns)
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
         let line = case errSpan i of
                        Just l -> " +" ++ show (fst (fc_start l)) ++ " "
                        Nothing -> " "
         let cmd = editor ++ line ++ fixName f
         runIO $ system cmd
         clearErr
         putIState $ orig { idris_options = idris_options i
                          , idris_colourTheme = idris_colourTheme i
                          }
         loadInputs [f] Nothing
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

process :: FilePath -> Command -> Idris ()
process fn Help = iPrintResult displayHelp
process fn Warranty = iPrintResult warranty
process fn (ChangeDirectory f)
                 = do runIO $ setCurrentDirectory f
                      return ()
process fn (Eval t)
                 = withErrorReflection $ do logLvl 5 $ show t
                                            (tm, ty) <- elabVal recinfo ERHS t
                                            ctxt <- getContext
                                            let tm' = force (normaliseAll ctxt [] tm)
                                            let ty' = force (normaliseAll ctxt [] ty)
                                            -- Add value to context, call it "it"
                                            updateContext (addCtxtDef (sUN "it") (Function ty' tm'))
                                            ist <- getIState
                                            logLvl 3 $ "Raw: " ++ show (tm', ty')
                                            logLvl 10 $ "Debug: " ++ showEnvDbg [] tm'
                                            let tmDoc = pprintDelab ist tm'
                                                tyDoc = pprintDelab ist ty'
                                            iPrintTermWithType tmDoc tyDoc


process fn (NewDefn decls) = do
        logLvl 3 ("Defining names using these decls: " ++ show (showDecls verbosePPOption decls))
        mapM_ defineName namedGroups where
  namedGroups = groupBy (\d1 d2 -> getName d1 == getName d2) decls
  getName :: PDecl -> Maybe Name
  getName (PTy docs argdocs syn fc opts name ty) = Just name
  getName (PClauses fc opts name (clause:clauses)) = Just (getClauseName clause)
  getName (PData doc argdocs syn fc opts dataDecl) = Just (d_name dataDecl)
  getName (PClass doc syn fc constraints name parms parmdocs decls) = Just name
  getName _ = Nothing
  -- getClauseName is partial and I am not sure it's used safely! -- trillioneyes
  getClauseName (PClause fc name whole with rhs whereBlock) = name
  getClauseName (PWith fc name whole with rhs whereBlock) = name
  defineName :: [PDecl] -> Idris ()
  defineName (tyDecl@(PTy docs argdocs syn fc opts name ty) : decls) = do 
    elabDecl EAll recinfo tyDecl
    elabClauses recinfo fc opts name (concatMap getClauses decls)
    setReplDefined (Just name)
  defineName [PClauses fc opts _ [clause]] = do
    let pterm = getRHS clause
    (tm,ty) <- elabVal recinfo ERHS pterm
    ctxt <- getContext
    let tm' = force (normaliseAll ctxt [] tm)
    let ty' = force (normaliseAll ctxt [] ty)
    updateContext (addCtxtDef (getClauseName clause) (Function ty' tm'))
    setReplDefined (Just $ getClauseName clause)
  defineName (PClauses{} : _) = tclift $ tfail (Msg "Only one function body is allowed without a type declaration.")
  -- fixity and syntax declarations are ignored by elabDecls, so they'll have to be handled some other way
  defineName (PFix fc fixity strs : defns) = do
    fmodifyState idris_fixities (map (Fix fixity) strs ++)
    unless (null defns) $ defineName defns
  defineName (PSyntax{}:_) = tclift $ tfail (Msg "That kind of declaration is not supported. If you feel it should be supported, please submit an issue at https://github.com/idris-lang/Idris-dev.")
  defineName decls = do
    elabDecls toplevel (map fixClauses decls)
    setReplDefined (getName (head decls))
  getClauses (PClauses fc opts name clauses) = clauses
  getClauses _ = []
  getRHS :: PClause -> PTerm
  getRHS (PClause fc name whole with rhs whereBlock) = rhs
  getRHS (PWith fc name whole with rhs whereBlock) = rhs
  getRHS (PClauseR fc with rhs whereBlock) = rhs
  getRHS (PWithR fc with rhs whereBlock) = rhs
  setReplDefined :: Maybe Name -> Idris ()
  setReplDefined Nothing = return ()
  setReplDefined (Just n) = do
    oldState <- get
    fmodifyState repl_definitions (n:)
  -- the "name" field of PClauses seems to always be MN 2 "__", so we need to
  -- retrieve the actual name from deeper inside.
  -- This should really be a full recursive walk through the structure of PDecl, but
  -- I think it should work this way and I want to test sooner. Also lazy.
  fixClauses :: PDecl' t -> PDecl' t
  fixClauses (PClauses fc opts _ css@(clause:cs)) =
    PClauses fc opts (getClauseName clause) css
  fixClauses (PInstance syn fc constraints cls parms ty instName decls) = 
    PInstance syn fc constraints cls parms ty instName (map fixClauses decls)
  fixClauses decl = decl

process fn (Undefine names) = undefine names
  where
    undefine :: [Name] -> Idris ()
    undefine [] = do
      allDefined <- idris_repl_defs `fmap` get
      undefine' allDefined []
    -- Keep track of which names you've removed so you can 
    -- print them out to the user afterward
    undefine names = undefine' names []
    undefine' [] list = do iRenderOutput $ printUndefinedNames list 
                           return ()
    undefine' (n:names) already = do
      allDefined <- idris_repl_defs `fmap` get
      if n `elem` allDefined
         then do undefinedJustNow <- undefClosure n
                 undefine' names (undefinedJustNow ++ already)
         else do tclift $ tfail $ Msg ("Can't undefine " ++ show n ++ " because it wasn't defined at the repl")
                 undefine' names already
    undefOne n = do fputState (ctxt_lookup n . known_terms) Nothing
                    -- for now just assume it's a class. Eventually we'll want some kind of
                    -- smart detection of exactly what kind of name we're undefining.
                    fputState (ctxt_lookup n . known_classes) Nothing
                    fmodifyState repl_definitions (delete n)
    undefClosure n = 
      do replDefs <- idris_repl_defs `fmap` get
         callGraph <- whoCalls n
         let users = case lookup n callGraph of
                        Just ns -> nub ns
                        Nothing -> fail ("Tried to undefine nonexistent name" ++ show n) 
         undefinedJustNow <- concat `fmap` mapM undefClosure users
         undefOne n
         return (nub (n : undefinedJustNow))



process fn (ExecVal t)
                  = do ctxt <- getContext
                       ist <- getIState
                       (tm, ty) <- elabVal recinfo ERHS t
--                       let tm' = normaliseAll ctxt [] tm
                       let ty' = normaliseAll ctxt [] ty
                       res <- execute tm
                       let (resOut, tyOut) = (prettyIst ist (delab ist res),
                                              prettyIst ist (delab ist ty'))
                       iPrintTermWithType resOut tyOut

process fn (Check (PRef _ n))
   = do ctxt <- getContext
        ist <- getIState
        let ppo = ppOptionIst ist
        case lookupNames n ctxt of
          ts@(t:_) ->
            case lookup t (idris_metavars ist) of
                Just (_, i, _) -> iRenderResult . fmap (fancifyAnnots ist) $
                                  showMetavarInfo ppo ist n i
                Nothing -> iPrintFunTypes [] n (map (\n -> (n, delabTy ist n)) ts)
          [] -> iPrintError $ "No such variable " ++ show n
  where
    showMetavarInfo ppo ist n i
         = case lookupTy n (tt_ctxt ist) of
                (ty:_) -> putTy ppo ist i [] (delab ist (errReverse ist ty))
    putTy :: PPOption -> IState -> Int -> [(Name, Bool)] -> PTerm -> Doc OutputAnnotation
    putTy ppo ist 0 bnd sc = putGoal ppo ist bnd sc
    putTy ppo ist i bnd (PPi _ n t sc)
               = let current = text "  " <>
                               (case n of
                                   MN _ _ -> text "_"
                                   UN nm | ('_':'_':_) <- str nm -> text "_"
                                   _ -> bindingOf n False) <+>
                               colon <+> align (tPretty bnd ist t) <> line
                 in
                    current <> putTy ppo ist (i-1) ((n,False):bnd) sc
    putTy ppo ist _ bnd sc = putGoal ppo ist ((n,False):bnd) sc
    putGoal ppo ist bnd g
               = text "--------------------------------------" <$>
                 annotate (AnnName n Nothing Nothing Nothing) (text $ show n) <+> colon <+>
                 align (tPretty bnd ist g)

    tPretty bnd ist t = pprintPTerm (ppOptionIst ist) bnd [] (idris_infixes ist) t


process fn (Check t)
   = do (tm, ty) <- elabVal recinfo ERHS t
        ctxt <- getContext
        ist <- getIState
        let ppo = ppOptionIst ist
            ty' = normaliseC ctxt [] ty
        case tm of
           TType _ ->
             iPrintTermWithType (prettyIst ist PType) type1Doc
           _ -> iPrintTermWithType (pprintDelab ist tm)
                                   (pprintDelab ist ty)

process fn (DocStr (Left n))
   = do ist <- getIState
        case lookupCtxtName n (idris_docstrings ist) of
          [] -> iPrintError $ "No documentation for " ++ show n
          ns -> do toShow <- mapM (showDoc ist) ns
                   iRenderResult (vsep toShow)
    where showDoc ist (n, d) = do doc <- getDocs n
                                  return $ pprintDocs ist doc

process fn (DocStr (Right c))
   = do ist <- getIState
        iRenderResult $ pprintConstDocs ist c (constDocs c)

process fn Universes
                     = do i <- getIState
                          let cs = idris_constraints i
--                        iputStrLn $ showSep "\n" (map show cs)
                          iputStrLn $ show (map fst cs)
                          let n = length cs
                          iputStrLn $ "(" ++ show n ++ " constraints)"
                          case ucheck cs of
                            Error e -> iPrintError $ pshow i e
                            OK _ -> iPrintResult "Universes OK"
process fn (Defn n)
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
process fn (TotCheck n)
                        = do i <- getIState
                             case lookupNameTotal n (tt_ctxt i) of
                                []  -> iPrintError $ "Unknown operator " ++ show n
                                ts  -> do ist <- getIState
                                          c <- colourise
                                          let ppo =  ppOptionIst ist
                                          let showN = showName (Just ist) [] ppo c
                                          iPrintResult . concat . intersperse "\n" .
                                            map (\(n, t) -> showN n ++ " is " ++ showTotal t i) $
                                            ts


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
        i <- getIState
        let cg' = lookupCtxtName n (idris_callgraph i)
        sc <- checkSizeChange n
        iputStrLn $ "Size change: " ++ show sc
        let fn = lookupCtxtName n (idris_fninfo i)
        when (not (null cg')) $ do iputStrLn "Call graph:\n"
                                   iputStrLn (show cg')
        when (not (null fn)) $ iputStrLn (show fn)
process fn (Search t) = searchByType t
process fn (CaseSplitAt updatefile l n)
    = caseSplitAt fn updatefile l n
process fn (AddClauseFrom updatefile l n)
    = addClauseFrom fn updatefile l n
process fn (AddProofClauseFrom updatefile l n)
    = addProofClauseFrom fn updatefile l n
process fn (AddMissing updatefile l n)
    = addMissing fn updatefile l n
process fn (MakeWith updatefile l n)
    = makeWith fn updatefile l n
process fn (MakeLemma updatefile l n)
    = makeLemma fn updatefile l n
process fn (DoProofSearch updatefile rec l n hints)
    = doProofSearch fn updatefile rec l n hints Nothing
process fn (Spec t)
                    = do (tm, ty) <- elabVal recinfo ERHS t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = simplify ctxt [] {- (idris_statics ist) -} tm
                         iPrintResult (show (delab ist tm'))

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
                                 putIState $ i { idris_metavars = (n, (Nothing, 0, False)) : ms }

process fn' (AddProof prf)
  = do fn <- do
         let fn'' = takeWhile (/= ' ') fn'
         ex <- runIO $ doesFileExist fn''
         let fnExt = fn'' <.> "idr"
         exExt <- runIO $ doesFileExist fnExt
         if ex
            then return fn''
            else if exExt
                    then return fnExt
                    else ifail $ "Neither \""++fn''++"\" nor \""++fnExt++"\" exist"
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

process fn (ShowProof n')
  = do i <- getIState
       n <- resolveProof n'
       let proofs = proof_list i
       case lookup n proofs of
            Nothing -> iPrintError "No proof to show"
            Just p  -> iPrintResult $ showProof False n p

process fn (Prove n')
     = do ctxt <- getContext
          ist <- getIState
          let ns = lookupNames n' ctxt
          let metavars = mapMaybe (\n -> do c <- lookup n (idris_metavars ist); return (n, c)) ns
          n <- case metavars of
              [] -> ierror (Msg $ "Cannot find metavariable " ++ show n')
              [(n, (_,_,False))] -> return n
              [(_, (_,_,True))]  -> ierror (Msg $ "Declarations not solvable using prover")
              ns -> ierror (CantResolveAlts (map fst ns))
          prover (lit fn) n
          -- recheck totality
          i <- getIState
          totcheck (fileFC "(input)", n)
          mapM_ (\ (f,n) -> setTotality n Unchecked) (idris_totcheck i)
          mapM_ checkDeclTotality (idris_totcheck i)
          warnTotality

process fn (HNF t)
                    = do (tm, ty) <- elabVal recinfo ERHS t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = hnf ctxt [] tm
                         iPrintResult (show (delab ist tm'))
process fn (TestInline t)
                           = do (tm, ty) <- elabVal recinfo ERHS t
                                ctxt <- getContext
                                ist <- getIState
                                let tm' = inlineTerm ist tm
                                c <- colourise
                                iPrintResult (showTm ist (delab ist tm'))
process fn Execute
                   = idrisCatch
                       (do ist <- getIState
                           (m, _) <- elabVal recinfo ERHS
                                           (PApp fc
                                              (PRef fc (sUN "run__IO"))
                                              [pexp $ PRef fc (sNS (sUN "main") ["Main"])])
                           (tmpn, tmph) <- runIO tempfile
                           runIO $ hClose tmph
                           t <- codegen
                           ir <- compile t tmpn m
                           runIO $ generate t (head (idris_imported ist)) ir
                           case idris_outputmode ist of
                             RawOutput h -> do runIO $ system tmpn
                                               return ()
                             IdeSlave n h -> runIO . hPutStrLn h $
                                             IdeSlave.convSExp "run-program" tmpn n)
                       (\e -> getIState >>= iRenderError . flip pprintErr e)
  where fc = fileFC "main"
process fn (Compile codegen f)
      = do (m, _) <- elabVal recinfo ERHS
                       (PApp fc (PRef fc (sUN "run__IO"))
                       [pexp $ PRef fc (sNS (sUN "main") ["Main"])])
           ir <- compile codegen f m
           i <- getIState
           runIO $ generate codegen (head (idris_imported i)) ir
  where fc = fileFC "main"
process fn (LogLvl i) = setLogLevel i
-- Elaborate as if LHS of a pattern (debug command)
process fn (Pattelab t)
     = do (tm, ty) <- elabVal recinfo ELHS t
          iPrintResult $ show tm ++ "\n\n : " ++ show ty

process fn (Missing n)
    = do i <- getIState
         let i' = i { idris_options = (idris_options i) { opt_showimp = True } }
         case lookupCtxt n (idris_patdefs i) of
                  [] -> iPrintError $ "Unknown operator " ++ show n
                  [(_, tms)] ->
                       iPrintResult (showSep "\n" (map (showTm i') tms))
                  _ -> iPrintError $ "Ambiguous name"
process fn (DynamicLink l)
                           = do i <- getIState
                                let importdirs = opt_importdirs (idris_options i)
                                    lib = trim l
                                handle <- lift . lift $ tryLoadLib importdirs lib
                                case handle of
                                  Nothing -> iPrintError $ "Could not load dynamic lib \"" ++ l ++ "\""
                                  Just x -> do let libs = idris_dynamic_libs i
                                               if x `elem` libs
                                                  then do iLOG ("Tried to load duplicate library " ++ lib_name x)
                                                          return ()
                                                  else putIState $ i { idris_dynamic_libs = x:libs }
    where trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
process fn ListDynamic
                       = do i <- getIState
                            iputStrLn "Dynamic libraries:"
                            showLibs $ idris_dynamic_libs i
    where showLibs []                = return ()
          showLibs ((Lib name _):ls) = do iputStrLn $ "\t" ++ name; showLibs ls
process fn Metavars
                 = do ist <- getIState
                      let mvs = map fst (idris_metavars ist) \\ primDefs
                      case mvs of
                        [] -> iPrintError "No global metavariables to solve"
                        _ -> iPrintResult $ "Global metavariables:\n\t" ++ show mvs
process fn NOP      = return ()

process fn (SetOpt   ErrContext)  = setErrContext True
process fn (UnsetOpt ErrContext)  = setErrContext False
process fn (SetOpt ShowImpl)      = setImpShow True
process fn (UnsetOpt ShowImpl)    = setImpShow False
process fn (SetOpt ShowOrigErr)   = setShowOrigErr True
process fn (UnsetOpt ShowOrigErr) = setShowOrigErr False
process fn (SetOpt AutoSolve)     = setAutoSolve True
process fn (UnsetOpt AutoSolve)   = setAutoSolve False
process fn (SetOpt NoBanner)      = setNoBanner True
process fn (UnsetOpt NoBanner)    = setNoBanner False
process fn (SetOpt WarnReach)     = fmodifyState opts_idrisCmdline $ nub . (WarnReach:)
process fn (UnsetOpt WarnReach)   = fmodifyState opts_idrisCmdline $ delete WarnReach

process fn (SetOpt _) = iPrintError "Not a valid option"
process fn (UnsetOpt _) = iPrintError "Not a valid option"
process fn (SetColour ty c) = setColour ty c
process fn ColourOn
                    = do ist <- getIState
                         putIState $ ist { idris_colourRepl = True }
process fn ColourOff
                     = do ist <- getIState
                          putIState $ ist { idris_colourRepl = False }
process fn ListErrorHandlers =
  do ist <- getIState
     iPrintResult $ case idris_errorhandlers ist of
       []       -> "No registered error handlers"
       handlers -> "Registered error handlers: " ++ (concat . intersperse ", " . map show) handlers
process fn (SetConsoleWidth w) = setWidth w

process fn (Apropos a) =
  do ist <- getIState
     let names = apropos ist (T.pack a)
     let aproposInfo = [ (n,
                          delabTy ist n,
                          fmap (overview . fst) (lookupCtxtExact n (idris_docstrings ist)))
                       | n <- sort names, isUN n ]
     iRenderResult $ vsep (map (prettyDocumentedIst ist) aproposInfo)
  where isUN (UN _) = True
        isUN (NS n _) = isUN n
        isUN _ = False

process fn (WhoCalls n) =
  do calls <- whoCalls n
     ist <- getIState
     iRenderResult . vsep $
       map (\(n, ns) ->
             text "Callers of" <+> prettyName True True [] n <$>
             indent 1 (vsep (map ((text "*" <+>) . align . prettyName True True []) ns)))
           calls

process fn (CallsWho n) =
  do calls <- callsWho n
     ist <- getIState
     iRenderResult . vsep $
       map (\(n, ns) ->
             prettyName True True [] n <+> text "calls:" <$>
             indent 1 (vsep (map ((text "*" <+>) . align . prettyName True True []) ns)))
           calls
-- IdrisDoc
process fn (MakeDoc s) =
  do     istate        <- getIState
         let names      = words s
             parse n    | Success x <- runparser name istate fn n = Right x
             parse n    = Left n
             (bad, nss) = partitionEithers $ map parse names
         cd            <- runIO $ getCurrentDirectory
         let outputDir  = cd </> "doc"
         result        <- if null bad then runIO $ generateDocs istate nss outputDir
                                      else return . Left $ "Illegal name: " ++ head bad
         case result of Right _   -> iputStrLn "IdrisDoc generated"
                        Left  err -> iPrintError err


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

helphead =
  [ (["Command"], SpecialHeaderArg, "Purpose"),
    ([""], NoArg, "")
  ]


replSettings :: Maybe FilePath -> Settings Idris
replSettings hFile = setComplete replCompletion $ defaultSettings {
                       historyFile = hFile
                     }

-- | Invoke as if from command line. It is an error if there are unresolved totality problems.
idris :: [Opt] -> IO (Maybe IState)
idris opts = do res <- runErrorT $ execStateT totalMain idrisInit
                case res of
                  Left err -> do putStrLn $ pshow idrisInit err
                                 return Nothing
                  Right ist -> return (Just ist)
    where totalMain = do idrisMain opts
                         ist <- getIState
                         case idris_totcheckfail ist of
                           ((fc, msg):_) -> ierror . At fc . Msg $ "Could not build: "++  msg
                           [] -> return ()


loadInputs :: [FilePath] -> Maybe Int -> Idris ()
loadInputs inputs toline -- furthest line to read in input source files
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
                   modTree <- buildTree
                                   (map snd (take (num-1) ninputs))
                                   input
                   let ifiles = getModuleFiles modTree
                   iLOG ("MODULE TREE : " ++ show modTree)
                   iLOG ("RELOAD: " ++ show ifiles)
                   when (not (all ibc ifiles) || loadCode) $
                        tryLoad False (filter (not . ibc) ifiles)
                   -- return the files that need rechecking
                   return ifiles)
                      ninputs
           inew <- getIState
           let tidata = idris_tyinfodata inew
           let patdefs = idris_patdefs inew
           -- If it worked, load the whole thing from all the ibcs together
           case errSpan inew of
              Nothing ->
                do putIState (ist { idris_tyinfodata = tidata })
                   ibcfiles <- mapM findNewIBC (nub (concat ifiles))
                   tryLoad True (mapMaybe id ibcfiles)
              _ -> return ()
           ist <- getIState
           putIState (ist { idris_tyinfodata = tidata,
                            idris_patdefs = patdefs })

           case opt getOutput opts of
               [] -> performUsageAnalysis  -- interactive
               _  -> return []  -- batch, will be checked by the compiler

           return ())
        (\e -> do i <- getIState
                  case e of
                    At f e' -> do setErrSpan f
                                  iWarn f $ pprintErr i e'
                    ProgramLineComment -> return () -- fail elsewhere
                    _ -> do setErrSpan emptyFC -- FIXME! Propagate it
                            iWarn emptyFC $ pprintErr i e)
   where -- load all files, stop if any fail
         tryLoad :: Bool -> [IFileType] -> Idris ()
         tryLoad keepstate [] = warnTotality >> return ()
         tryLoad keepstate (f : fs)
                 = do ist <- getIState
                      let maxline
                            = case toline of
                                Nothing -> Nothing
                                Just l -> case f of
                                            IDR fn -> if any (fmatch fn) inputs
                                                         then Just l
                                                         else Nothing
                                            LIDR fn -> if any (fmatch fn) inputs
                                                          then Just l
                                                          else Nothing
                                            _ -> Nothing
                      loadFromIFile f maxline
                      inew <- getIState
                      -- FIXME: Save these in IBC to avoid this hack! Need to
                      -- preserve it all from source inputs
                      let tidata = idris_tyinfodata inew
                      let patdefs = idris_patdefs inew
                      ok <- noErrors
                      when ok $ do when (not keepstate) $ putIState ist
                                   ist <- getIState
                                   putIState (ist { idris_tyinfodata = tidata,
                                                    idris_patdefs = patdefs })
                                   tryLoad keepstate fs

         ibc (IBC _ _) = True
         ibc _ = False

         fmatch ('.':'/':xs) ys = fmatch xs ys
         fmatch xs ('.':'/':ys) = fmatch xs ys
         fmatch xs ys = xs == ys

         findNewIBC :: IFileType -> Idris (Maybe IFileType)
         findNewIBC i@(IBC _ _) = return (Just i)
         findNewIBC s@(IDR f) = do ist <- get
                                   ibcsd <- valIBCSubDir ist
                                   let ibc = ibcPathNoFallback ibcsd f
                                   ok <- runIO $ doesFileExist ibc
                                   if ok then return (Just (IBC ibc s))
                                         else return Nothing
         findNewIBC s@(LIDR f) = do ist <- get
                                    ibcsd <- valIBCSubDir ist
                                    let ibc = ibcPathNoFallback ibcsd f
                                    ok <- runIO $ doesFileExist ibc
                                    if ok then return (Just (IBC ibc s))
                                          else return Nothing

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
       let idesl = Ideslave `elem` opts || IdeslaveSocket `elem` opts
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
       let outty = case opt getOutputTy opts of
                     [] -> Executable
                     xs -> last xs
       let cgn = case opt getCodegen opts of
                   [] -> Via "c"
                   xs -> last xs
       script <- case opt getExecScript opts of
                   []     -> return Nothing
                   x:y:xs -> do iputStrLn "More than one interpreter expression found."
                                runIO $ exitWith (ExitFailure 1)
                   [expr] -> return (Just expr)
       let immediate = opt getEvalExpr opts

       when (DefaultTotal `elem` opts) $ do i <- getIState
                                            putIState (i { default_total = True })
       setColourise $ not quiet && last (True : opt getColour opts)
       when (not runrepl) $ setWidth InfinitelyWide
       mapM_ addLangExt (opt getLanguageExt opts)
       setREPL runrepl
       setQuiet (quiet || isJust script || not (null immediate))
       setVerbose verbose
       setCmdLine opts
       setOutputTy outty
       setNoBanner nobanner
       setCodegen cgn
       mapM_ makeOption opts
       -- if we have the --bytecode flag, drop into the bytecode assembler
       case bcs of
         [] -> return ()
         xs -> return () -- runIO $ mapM_ bcAsm xs
       case ibcsubdir of
         [] -> setIBCSubDir ""
         (d:_) -> setIBCSubDir d
       setImportDirs importdirs

       setNoBanner nobanner

       when (not (NoBasePkgs `elem` opts)) $ do
           addPkgDir "prelude"
           addPkgDir "base"
       mapM_ addPkgDir pkgdirs
       elabPrims
       when (not (NoBuiltins `elem` opts)) $ do x <- loadModule "Builtins"
                                                addAutoImport "Builtins"
                                                return ()
       when (not (NoPrelude `elem` opts)) $ do x <- loadModule "Prelude"
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
       when (not idesl) $ loadInputs inputs Nothing

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
                                         Failure err -> do iputStrLn $ show (fixColour c err)
                                                           runIO $ exitWith (ExitFailure 1)
                                         Success e -> process "" (Eval e))
                           exprs
                     runIO $ exitWith ExitSuccess


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
         startServer orig inputs
         runInputT (replSettings (Just historyFile)) $ repl orig inputs
       let idesock = IdeslaveSocket `elem` opts
       when (idesl) $ ideslaveStart idesock orig inputs
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
                     addIBC (IBCImportDir (ddir </> p))

runMain :: Idris () -> IO ()
runMain prog = do res <- runErrorT $ execStateT prog idrisInit
                  case res of
                       Left err -> putStrLn $ "Uncaught error: " ++ show err
                       Right _ -> return ()

execScript :: String -> Idris ()
execScript expr = do i <- getIState
                     c <- colourise
                     case parseExpr i expr of
                          Failure err -> do iputStrLn $ show (fixColour c err)
                                            runIO $ exitWith (ExitFailure 1)
                          Success term -> do ctxt <- getContext
                                             (tm, _) <- elabVal recinfo ERHS term
                                             res <- execute tm
                                             runIO $ exitWith ExitSuccess

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
                   Success (Load f _) -> iPrintError "Init scripts cannot load files"
                   Success (ModImport f) -> iPrintError "Init scripts cannot import modules"
                   Success Edit -> iPrintError "Init scripts cannot invoke the editor"
                   Success Proofs -> proofs i
                   Success Quit -> iPrintError "Init scripts cannot quit Idris"
                   Success cmd  -> process [] cmd

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

-- | Returns None if given an Opt which is not PkgMkDoc
--   Otherwise returns Just x, where x is the contents of PkgMkDoc
getPkgMkDoc :: Opt          -- ^ Opt to extract
            -> Maybe String -- ^ Result
getPkgMkDoc (PkgMkDoc str) = Just str
getPkgMkDoc _              = Nothing

getPkgTest :: Opt          -- ^ the option to extract
           -> Maybe String -- ^ the package file to test
getPkgTest (PkgTest f) = Just f
getPkgTest _ = Nothing

getCodegen :: Opt -> Maybe Codegen
getCodegen (UseCodegen x) = Just x
getCodegen _ = Nothing

getExecScript :: Opt -> Maybe String
getExecScript (InterpretScript expr) = Just expr
getExecScript _ = Nothing

getEvalExpr :: Opt -> Maybe String
getEvalExpr (EvalExpr expr) = Just expr
getEvalExpr _ = Nothing

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
         " /___/\\__,_/_/  /_/____/       Type :? for help               \n" ++
         "\n" ++
         "Idris is free software with ABSOLUTELY NO WARRANTY.            \n" ++
         "For details type :warranty."

warranty = "\n"                                                                          ++
           "\t THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS ``AS IS'' AND ANY  \n" ++
           "\t EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE     \n" ++
           "\t IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR    \n" ++
           "\t PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT HOLDERS BE   \n" ++
           "\t LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR   \n" ++
           "\t CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF  \n" ++
           "\t SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR       \n" ++
           "\t BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, \n" ++
           "\t WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE  \n" ++
           "\t OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN\n" ++
           "\t IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.\n"

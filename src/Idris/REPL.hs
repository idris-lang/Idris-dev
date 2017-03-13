{-|
Module      : Idris.REPL
Description : Entry Point for the Idris REPL and CLI.
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE PatternGuards #-}

module Idris.REPL
  ( idemodeStart
  , startServer
  , runClient
  , process
  , replSettings
  , repl
  , proofs
  ) where

import Control.Category
import Control.Concurrent
import Control.Concurrent.Async (race)
import Control.DeepSeq
import qualified Control.Exception as X
import Control.Monad
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.State.Strict (evalStateT, get, put)
import Data.Char
import Data.Either (partitionEithers)
import Data.List hiding (group)
import Data.List.Split (splitOn)
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Version
import Idris.AbsSyntax
import Idris.Apropos (apropos, aproposModules)
import Idris.ASTUtils
import Idris.Colours hiding (colourise)
import Idris.Completion
import Idris.Core.Constraints
import Idris.Core.Evaluate
import Idris.Core.Execute (execute)
import Idris.Core.TT
import Idris.Core.Unify
import Idris.Core.WHNF
import Idris.Coverage
import Idris.DataOpts
import Idris.Delaborate
import Idris.Docs
import Idris.Docstrings (overview, renderDocTerm, renderDocstring)
import Idris.Elab.Clause
import Idris.Elab.Term
import Idris.Elab.Value
import Idris.ElabDecls
import Idris.Error
import Idris.ErrReverse
import Idris.Help
import Idris.IBC
import qualified Idris.IdeMode as IdeMode
import Idris.IdrisDoc
import Idris.Info
import Idris.Inliner
import Idris.Interactive
import Idris.ModeCommon
import Idris.Output
import Idris.Parser hiding (indent)
import Idris.Prover
import Idris.REPL.Browse (namesInNS, namespacesInNS)
import Idris.REPL.Commands
import Idris.REPL.Parser
import Idris.Termination
import Idris.TypeSearch (searchByType)
import Idris.WhoCalls
import IRTS.Compiler
import Network
import Prelude hiding (id, (.), (<$>))
import System.Console.Haskeline as H
import System.Directory
import System.Environment
import System.Exit
import System.FilePath (addExtension, dropExtension, splitExtension,
                        takeDirectory, takeExtension, (<.>), (</>))
import System.FSNotify (watchDir, withManager)
import System.FSNotify.Devel (allEvents, doAllEvents)
import System.IO
import System.Process
import Text.Trifecta.Result (ErrInfo(..), Result(..))
import Util.DynamicLinker
import Util.Net (listenOnLocalhost, listenOnLocalhostAnyPort)
import Util.Pretty hiding ((</>))
import Util.System
import Version_idris (gitHash)

import Debug.Trace

-- | Run the REPL
repl :: IState -- ^ The initial state
     -> [FilePath] -- ^ The loaded modules
     -> FilePath -- ^ The file to edit (with :e)
     -> InputT Idris ()
repl orig mods efile
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
                             (if colour && not isWindows
                                then colourisePrompt theme str
                                else str) ++ " "
        x <- H.catch (H.withInterrupt $ getInputLine prompt)
                     (ctrlC (return $ Just ""))
        case x of
            Nothing -> do lift $ when (not quiet) (iputStrLn "Bye bye")
                          return ()
            Just input -> -- H.catch
                do ms <- H.catch (H.withInterrupt $ lift $ processInput input orig mods efile)
                                 (ctrlC (return (Just mods)))
                   case ms of
                        Just mods -> let efile' = fromMaybe efile (listToMaybe mods)
                                     in repl orig mods efile'
                        Nothing -> return ()
--                             ctrlC)
--       ctrlC
   where ctrlC :: InputT Idris a -> SomeException -> InputT Idris a
         ctrlC act e = do lift $ iputStrLn (show e)
                          act -- repl orig mods

         showMVs c thm [] = ""
         showMVs c thm ms = "Holes: " ++
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
startServer :: PortNumber -> IState -> [FilePath] -> Idris ()
startServer port orig fn_in = do tid <- runIO $ forkIO (serverLoop port)
                                 return ()
  where serverLoop port = withSocketsDo $
                              do sock <- listenOnLocalhost port
                                 loop fn orig { idris_colourRepl = False } sock

        fn = fromMaybe "" (listToMaybe fn_in)

        loop fn ist sock
            = do (h,_,_) <- accept sock
                 hSetEncoding h utf8
                 cmd <- hGetLine h
                 let isth = case idris_outputmode ist of
                              RawOutput _ -> ist {idris_outputmode = RawOutput h}
                              IdeMode n _ -> ist {idris_outputmode = IdeMode n h}
                 (ist', fn) <- processNetCmd orig isth h fn cmd
                 hClose h
                 loop fn ist' sock

processNetCmd :: IState -> IState -> Handle -> FilePath -> String ->
                 IO (IState, FilePath)
processNetCmd orig i h fn cmd
    = do res <- case parseCmd i "(net)" cmd of
                  Failure (ErrInfo err _) -> return (Left (Msg " invalid command"))
                  Success (Right c) -> runExceptT $ evalStateT (processNet fn c) i
                  Success (Left err) -> return (Left (Msg err))
         case res of
              Right x -> return x
              Left err -> do hPutStrLn h (show err)
                             return (i, fn)
  where
    processNet fn Reload = processNet fn (Load fn Nothing)
    processNet fn (Load f toline) =
  -- The $!! here prevents a space leak on reloading.
  -- This isn't a solution - but it's a temporary stopgap.
  -- See issue #2386
        do putIState $!! orig { idris_options = idris_options i
                              , idris_colourTheme = idris_colourTheme i
                              , idris_colourRepl = False
                              }
           setErrContext True
           setOutH h
           setQuiet True
           setVerbose 0
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
           IdeMode n _ -> ist {idris_outputmode = IdeMode n h}

-- | Run a command on the server on localhost
runClient :: Maybe PortNumber -> String -> IO ()
runClient port str = withSocketsDo $ do
              let port' = fromMaybe defaultPort port
              res <- X.try (connectTo "localhost" $ PortNumber port')
              case res of
                Right h -> do
                  hSetEncoding h utf8
                  hPutStrLn h str
                  resp <- hGetResp "" h
                  putStr resp
                  hClose h

                Left err -> do
                  connectionError err
                  exitWith (ExitFailure 1)

    where hGetResp acc h = do eof <- hIsEOF h
                              if eof then return acc
                                     else do l <- hGetLine h
                                             hGetResp (acc ++ l ++ "\n") h

          connectionError :: X.SomeException -> IO ()
          connectionError _ =
            putStrLn "Unable to connect to a running Idris repl"


initIdemodeSocket :: IO Handle
initIdemodeSocket = do
  (sock, port) <- listenOnLocalhostAnyPort
  putStrLn $ show port
  (h, _, _) <- accept sock
  hSetEncoding h utf8
  return h

-- | Run the IdeMode
idemodeStart :: Bool -> IState -> [FilePath] -> Idris ()
idemodeStart s orig mods
  = do h <- runIO $ if s then initIdemodeSocket else return stdout
       setIdeMode True h
       i <- getIState
       case idris_outputmode i of
         IdeMode n h ->
           do runIO $ hPutStrLn h $ IdeMode.convSExp "protocol-version" IdeMode.ideModeEpoch n
              case mods of
                a:_ -> runIdeModeCommand h n i "" [] (IdeMode.LoadFile a Nothing)
                _   -> return ()
       idemode h orig mods

idemode :: Handle -> IState -> [FilePath] -> Idris ()
idemode h orig mods
  = do idrisCatch
         (do let inh = if h == stdout then stdin else h
             len' <- runIO $ IdeMode.getLen inh
             len <- case len' of
               Left err -> ierror err
               Right n  -> return n
             l <- runIO $ IdeMode.getNChar inh len ""
             (sexp, id) <- case IdeMode.parseMessage l of
                             Left err -> ierror err
                             Right (sexp, id) -> return (sexp, id)
             i <- getIState
             putIState $ i { idris_outputmode = (IdeMode id h) }
             idrisCatch -- to report correct id back!
               (do let fn = fromMaybe "" (listToMaybe mods)
                   case IdeMode.sexpToCommand sexp of
                     Just cmd -> runIdeModeCommand h id orig fn mods cmd
                     Nothing  -> iPrintError "did not understand" )
               (\e -> do iPrintError $ show e))
         (\e -> do iPrintError $ show e)
       idemode h orig mods

-- | Run IDEMode commands
runIdeModeCommand :: Handle -- ^^ The handle for communication
                   -> Integer -- ^^ The continuation ID for the client
                   -> IState -- ^^ The original IState
                   -> FilePath -- ^^ The current open file
                   -> [FilePath] -- ^^ The currently loaded modules
                   -> IdeMode.IdeModeCommand -- ^^ The command to process
                   -> Idris ()
runIdeModeCommand h id orig fn mods (IdeMode.Interpret cmd) =
  do c <- colourise
     i <- getIState
     case parseCmd i "(input)" cmd of
       Failure (ErrInfo err _) -> iPrintError $ show (fixColour False err)
       Success (Right (Prove mode n')) ->
         idrisCatch
           (do process fn (Prove mode n')
               isetPrompt (mkPrompt mods)
               case idris_outputmode i of
                 IdeMode n h -> -- signal completion of proof to ide
                   runIO . hPutStrLn h $
                     IdeMode.convSExp "return"
                       (IdeMode.SymbolAtom "ok", "")
                       n
                 _ -> return ())
           (\e -> do ist <- getIState
                     isetPrompt (mkPrompt mods)
                     case idris_outputmode i of
                       IdeMode n h ->
                         runIO . hPutStrLn h $
                           IdeMode.convSExp "abandon-proof" "Abandoned" n
                       _ -> return ()
                     iRenderError $ pprintErr ist e)
       Success (Right cmd) -> idrisCatch
                        (idemodeProcess fn cmd)
                        (\e -> getIState >>= iRenderError . flip pprintErr e)
       Success (Left err) -> iPrintError err
runIdeModeCommand h id orig fn mods (IdeMode.REPLCompletions str) =
  do (unused, compls) <- replCompletion (reverse str, "")
     let good = IdeMode.SexpList [IdeMode.SymbolAtom "ok",
                                   IdeMode.toSExp (map replacement compls,
                                   reverse unused)]
     runIO . hPutStrLn h $ IdeMode.convSExp "return" good id
runIdeModeCommand h id orig fn mods (IdeMode.LoadFile filename toline) =
  -- The $!! here prevents a space leak on reloading.
  -- This isn't a solution - but it's a temporary stopgap.
  -- See issue #2386
  do i <- getIState
     clearErr
     putIState $!! orig { idris_options = idris_options i,
                          idris_outputmode = (IdeMode id h) }
     mods <- loadInputs [filename] toline
     isetPrompt (mkPrompt mods)
     -- Report either success or failure
     i <- getIState
     case (errSpan i) of
       Nothing -> let msg = maybe (IdeMode.SexpList [IdeMode.SymbolAtom "ok",
                                                      IdeMode.SexpList []])
                                  (\fc -> IdeMode.SexpList [IdeMode.SymbolAtom "ok",
                                                             IdeMode.toSExp fc])
                                  (idris_parsedSpan i)
                  in runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
       Just x -> iPrintError $ "didn't load " ++ filename
     idemode h orig mods
runIdeModeCommand h id orig fn mods (IdeMode.TypeOf name) =
  case splitName name of
    Left err -> iPrintError err
    Right n -> process "(idemode)"
                 (Check (PRef (FC "(idemode)" (0,0) (0,0)) [] n))
runIdeModeCommand h id orig fn mods (IdeMode.DocsFor name w) =
  case parseConst orig name of
    Success c -> process "(idemode)" (DocStr (Right c) (howMuch w))
    Failure _ ->
     case splitName name of
       Left err -> iPrintError err
       Right n -> process "(idemode)" (DocStr (Left n) (howMuch w))
  where howMuch IdeMode.Overview = OverviewDocs
        howMuch IdeMode.Full     = FullDocs
runIdeModeCommand h id orig fn mods (IdeMode.CaseSplit line name) =
  process fn (CaseSplitAt False line (sUN name))
runIdeModeCommand h id orig fn mods (IdeMode.AddClause line name) =
  process fn (AddClauseFrom False line (sUN name))
runIdeModeCommand h id orig fn mods (IdeMode.AddProofClause line name) =
  process fn (AddProofClauseFrom False line (sUN name))
runIdeModeCommand h id orig fn mods (IdeMode.AddMissing line name) =
  process fn (AddMissing False line (sUN name))
runIdeModeCommand h id orig fn mods (IdeMode.MakeWithBlock line name) =
  process fn (MakeWith False line (sUN name))
runIdeModeCommand h id orig fn mods (IdeMode.MakeCaseBlock line name) =
  process fn (MakeCase False line (sUN name))
runIdeModeCommand h id orig fn mods (IdeMode.ProofSearch r line name hints depth) =
  doProofSearch fn False r line (sUN name) (map sUN hints) depth
runIdeModeCommand h id orig fn mods (IdeMode.MakeLemma line name) =
  case splitName name of
    Left err -> iPrintError err
    Right n -> process fn (MakeLemma False line n)
runIdeModeCommand h id orig fn mods (IdeMode.Apropos a) =
  process fn (Apropos [] a)
runIdeModeCommand h id orig fn mods (IdeMode.GetOpts) =
  do ist <- getIState
     let opts = idris_options ist
     let impshow = opt_showimp opts
     let errCtxt = opt_errContext opts
     let options = (IdeMode.SymbolAtom "ok",
                    [(IdeMode.SymbolAtom "show-implicits", impshow),
                     (IdeMode.SymbolAtom "error-context", errCtxt)])
     runIO . hPutStrLn h $ IdeMode.convSExp "return" options id
runIdeModeCommand h id orig fn mods (IdeMode.SetOpt IdeMode.ShowImpl b) =
  do setImpShow b
     let msg = (IdeMode.SymbolAtom "ok", b)
     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
runIdeModeCommand h id orig fn mods (IdeMode.SetOpt IdeMode.ErrContext b) =
  do setErrContext b
     let msg = (IdeMode.SymbolAtom "ok", b)
     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
runIdeModeCommand h id orig fn mods (IdeMode.Metavariables cols) =
  do ist <- getIState
     let mvs = reverse $ [ (n, i)
                         | (n, (_, i, _, _, _)) <- idris_metavars ist
                         , not (n `elem` primDefs)
                         ]
     let ppo = ppOptionIst ist
     -- splitMvs is a list of pairs of names and their split types
     let splitMvs = [ (n, (premises, concl, tm))
                    | (n, i, ty) <- mvTys ist mvs
                    , let (premises, concl, tm) = splitPi ist i ty]
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
       IdeMode.convSExp "return" (IdeMode.SymbolAtom "ok", mvOutput) id
  where mapPair f g xs = zip (map (f . fst) xs) (map (g . snd) xs)
        firstOfThree (x, y, z) = x
        mapThird f xs = map (\(x, y, z) -> (x, y, f z)) xs

        -- | Split a function type into a pair of premises, conclusion.
        -- Each maintains both the original and delaborated versions.
        splitPi :: IState -> Int -> Type -> ([(Name, Type, PTerm)], Type, PTerm)
        splitPi ist i (Bind n (Pi _ _ t _) rest) | i > 0 =
          let (hs, c, pc) = splitPi ist (i - 1) rest in
            ((n, t, delabTy' ist [] [] t False False True):hs,
             c, delabTy' ist [] [] c False False True)
        splitPi ist i tm = ([], tm, delabTy' ist [] [] tm False False True)

        -- | Get the types of a list of metavariable names
        mvTys :: IState -> [(Name, Int)] -> [(Name, Int, Type)]
        mvTys ist mvs = [ (n, i, ty)
                        | (n, i) <- mvs
                        , ty <- maybeToList (fmap (vToP . snd) (lookupTyNameExact n (tt_ctxt ist)))
                        ]

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
            fmap (fancifyAnnots ist True) .
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

runIdeModeCommand h id orig fn mods (IdeMode.WhoCalls n) =
  case splitName n of
       Left err -> iPrintError err
       Right n -> do calls <- whoCalls n
                     ist <- getIState
                     let msg = (IdeMode.SymbolAtom "ok",
                                map (\ (n,ns) -> (pn ist n, map (pn ist) ns)) calls)
                     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
  where pn ist = displaySpans .
                 renderPretty 0.9 1000 .
                 fmap (fancifyAnnots ist True) .
                 prettyName True True []

runIdeModeCommand h id orig fn mods (IdeMode.CallsWho n) =
  case splitName n of
       Left err -> iPrintError err
       Right n -> do calls <- callsWho n
                     ist <- getIState
                     let msg = (IdeMode.SymbolAtom "ok",
                                map (\ (n,ns) -> (pn ist n, map (pn ist) ns)) calls)
                     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
  where pn ist = displaySpans .
                 renderPretty 0.9 1000 .
                 fmap (fancifyAnnots ist True) .
                 prettyName True True []

runIdeModeCommand h id orig fn modes (IdeMode.BrowseNS ns) =
  case splitOn "." ns of
    [] -> iPrintError "No namespace provided"
    ns -> do underNSs <- fmap (map $ concat . intersperse ".") $ namespacesInNS ns
             names <- namesInNS ns
             if null underNSs && null names
                then iPrintError "Invalid or empty namespace"
                else do ist <- getIState
                        underNs <- mapM pn names
                        let msg = (IdeMode.SymbolAtom "ok", (underNSs, underNs))
                        runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
  where pn n =
          do ctxt <- getContext
             ist <- getIState
             return $
               displaySpans .
               renderPretty 0.9 1000 .
               fmap (fancifyAnnots ist True) $
                 prettyName True False [] n <>
                 case lookupTyExact n ctxt of
                   Just t ->
                     space <> colon <> space <> align (group (pprintDelab ist t))
                   Nothing ->
                     empty

runIdeModeCommand h id orig fn modes (IdeMode.TermNormalise bnd tm) =
  do ctxt <- getContext
     ist <- getIState
     let tm' = normaliseAll ctxt [] tm
         ptm = annotate (AnnTerm bnd tm')
               (pprintPTerm (ppOptionIst ist)
                            bnd
                            []
                            (idris_infixes ist)
                            (delab ist tm'))
         msg = (IdeMode.SymbolAtom "ok",
                displaySpans .
                renderPretty 0.9 80 .
                fmap (fancifyAnnots ist True) $ ptm)
     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
runIdeModeCommand h id orig fn modes (IdeMode.TermShowImplicits bnd tm) =
  ideModeForceTermImplicits h id bnd True tm
runIdeModeCommand h id orig fn modes (IdeMode.TermNoImplicits bnd tm) =
  ideModeForceTermImplicits h id bnd False tm
runIdeModeCommand h id orig fn modes (IdeMode.TermElab bnd tm) =
  do ist <- getIState
     let ptm = annotate (AnnTerm bnd tm)
                 (pprintTT (map fst bnd) tm)
         msg = (IdeMode.SymbolAtom "ok",
                displaySpans .
                renderPretty 0.9 70 .
                fmap (fancifyAnnots ist True) $ ptm)
     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
runIdeModeCommand h id orig fn mods (IdeMode.PrintDef name) =
  case splitName name of
    Left err -> iPrintError err
    Right n -> process "(idemode)" (PrintDef n)
runIdeModeCommand h id orig fn modes (IdeMode.ErrString e) =
  do ist <- getIState
     let out = displayS . renderPretty 1.0 60 $ pprintErr ist e
         msg = (IdeMode.SymbolAtom "ok", IdeMode.StringAtom $ out "")
     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
runIdeModeCommand h id orig fn modes (IdeMode.ErrPPrint e) =
  do ist <- getIState
     let (out, spans) =
           displaySpans .
           renderPretty 0.9 80 .
           fmap (fancifyAnnots ist True) $ pprintErr ist e
         msg = (IdeMode.SymbolAtom "ok", out, spans)
     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id
runIdeModeCommand h id orig fn modes IdeMode.GetIdrisVersion =
  let idrisVersion = (versionBranch getIdrisVersionNoGit,
                      if not (null gitHash)
                        then [gitHash]
                        else [])
      msg = (IdeMode.SymbolAtom "ok", idrisVersion)
  in runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id


-- | Show a term for IDEMode with the specified implicitness
ideModeForceTermImplicits :: Handle -> Integer -> [(Name, Bool)] -> Bool -> Term -> Idris ()
ideModeForceTermImplicits h id bnd impl tm =
  do ist <- getIState
     let expl = annotate (AnnTerm bnd tm)
                (pprintPTerm ((ppOptionIst ist) { ppopt_impl = impl })
                             bnd [] (idris_infixes ist)
                             (delab ist tm))
         msg = (IdeMode.SymbolAtom "ok",
                displaySpans .
                renderPretty 0.9 80 .
                fmap (fancifyAnnots ist True) $ expl)
     runIO . hPutStrLn h $ IdeMode.convSExp "return" msg id

splitName :: String -> Either String Name
splitName s = case reverse $ splitOn "." s of
                [] -> Left ("Didn't understand name '" ++ s ++ "'")
                [n] -> Right . sUN $ unparen n
                (n:ns) -> Right $ sNS (sUN (unparen n)) ns
  where unparen "" = ""
        unparen ('(':x:xs) | last xs == ')' = init (x:xs)
        unparen str = str

idemodeProcess :: FilePath -> Command -> Idris ()
idemodeProcess fn Warranty = process fn Warranty
idemodeProcess fn Help = process fn Help
idemodeProcess fn (RunShellCommand cmd) =
  iPrintError ":! is not currently supported in IDE mode."
idemodeProcess fn (ChangeDirectory f) =
  do process fn (ChangeDirectory f)
     dir <- runIO $ getCurrentDirectory
     iPrintResult $ "changed directory to " ++ dir
idemodeProcess fn (ModImport f) = process fn (ModImport f)
idemodeProcess fn (Eval t) = process fn (Eval t)
idemodeProcess fn (NewDefn decls) = do process fn (NewDefn decls)
                                       iPrintResult "defined"
idemodeProcess fn (Undefine n) = process fn (Undefine n)
idemodeProcess fn (ExecVal t) = process fn (ExecVal t)
idemodeProcess fn (Check (PRef x hls n)) = process fn (Check (PRef x hls n))
idemodeProcess fn (Check t) = process fn (Check t)
idemodeProcess fn (Core t) = process fn (Core t)
idemodeProcess fn (DocStr n w) = process fn (DocStr n w)
idemodeProcess fn Universes = process fn Universes
idemodeProcess fn (Defn n) = do process fn (Defn n)
                                iPrintResult ""
idemodeProcess fn (TotCheck n) = process fn (TotCheck n)
idemodeProcess fn (DebugInfo n) = do process fn (DebugInfo n)
                                     iPrintResult ""
idemodeProcess fn (Search ps t) = process fn (Search ps t)
idemodeProcess fn (Spec t) = process fn (Spec t)
-- RmProof and AddProof not supported!
idemodeProcess fn (ShowProof n') = process fn (ShowProof n')
idemodeProcess fn (WHNF t) = process fn (WHNF t)
--idemodeProcess fn TTShell = process fn TTShell -- need some prove mode!
idemodeProcess fn (TestInline t) = process fn (TestInline t)

idemodeProcess fn (Execute t) = do process fn (Execute t)
                                   iPrintResult ""
idemodeProcess fn (Compile codegen f) = do process fn (Compile codegen f)
                                           iPrintResult ""
idemodeProcess fn (LogLvl i) = do process fn (LogLvl i)
                                  iPrintResult ""
idemodeProcess fn (Pattelab t) = process fn (Pattelab t)
idemodeProcess fn (Missing n) = process fn (Missing n)
idemodeProcess fn (DynamicLink l) = do process fn (DynamicLink l)
                                       iPrintResult ""
idemodeProcess fn ListDynamic = do process fn ListDynamic
                                   iPrintResult ""
idemodeProcess fn Metavars = process fn Metavars
idemodeProcess fn (SetOpt ErrContext) = do process fn (SetOpt ErrContext)
                                           iPrintResult ""
idemodeProcess fn (UnsetOpt ErrContext) = do process fn (UnsetOpt ErrContext)
                                             iPrintResult ""
idemodeProcess fn (SetOpt ShowImpl) = do process fn (SetOpt ShowImpl)
                                         iPrintResult ""
idemodeProcess fn (UnsetOpt ShowImpl) = do process fn (UnsetOpt ShowImpl)
                                           iPrintResult ""
idemodeProcess fn (SetOpt ShowOrigErr) = do process fn (SetOpt ShowOrigErr)
                                            iPrintResult ""
idemodeProcess fn (UnsetOpt ShowOrigErr) = do process fn (UnsetOpt ShowOrigErr)
                                              iPrintResult ""
idemodeProcess fn (SetOpt x) = process fn (SetOpt x)
idemodeProcess fn (UnsetOpt x) = process fn (UnsetOpt x)
idemodeProcess fn (CaseSplitAt False pos str) = process fn (CaseSplitAt False pos str)
idemodeProcess fn (AddProofClauseFrom False pos str) = process fn (AddProofClauseFrom False pos str)
idemodeProcess fn (AddClauseFrom False pos str) = process fn (AddClauseFrom False pos str)
idemodeProcess fn (AddMissing False pos str) = process fn (AddMissing False pos str)
idemodeProcess fn (MakeWith False pos str) = process fn (MakeWith False pos str)
idemodeProcess fn (MakeCase False pos str) = process fn (MakeCase False pos str)
idemodeProcess fn (DoProofSearch False r pos str xs) = process fn (DoProofSearch False r pos str xs)
idemodeProcess fn (SetConsoleWidth w) = do process fn (SetConsoleWidth w)
                                           iPrintResult ""
idemodeProcess fn (SetPrinterDepth d) = do process fn (SetPrinterDepth d)
                                           iPrintResult ""
idemodeProcess fn (Apropos pkg a) = do process fn (Apropos pkg a)
                                       iPrintResult ""
idemodeProcess fn (WhoCalls n) = process fn (WhoCalls n)
idemodeProcess fn (CallsWho n) = process fn (CallsWho n)
idemodeProcess fn (PrintDef n) = process fn (PrintDef n)
idemodeProcess fn (PPrint fmt n tm) = process fn (PPrint fmt n tm)
idemodeProcess fn _ = iPrintError "command not recognized or not supported"


-- | The prompt consists of the currently loaded modules, or "Idris" if there are none
mkPrompt [] = "Idris"
mkPrompt [x] = "*" ++ dropExtension x
mkPrompt (x:xs) = "*" ++ dropExtension x ++ " " ++ mkPrompt xs

-- | Determine whether a file uses literate syntax
lit f = case splitExtension f of
            (_, ".lidr") -> True
            _ -> False

reload :: IState -> [FilePath] -> Idris (Maybe [FilePath])
reload orig inputs = do
  i <- getIState
  -- The $!! here prevents a space leak on reloading.
  -- This isn't a solution - but it's a temporary stopgap.
  -- See issue #2386
  putIState $!! orig { idris_options = idris_options i
    , idris_colourTheme = idris_colourTheme i
    , imported = imported i
  }
  clearErr
  fmap Just $ loadInputs inputs Nothing

watch :: IState -> [FilePath] -> Idris (Maybe [FilePath])
watch orig inputs = do
  resp <- runIO $ do
    let dirs = nub $ map takeDirectory inputs
    inputSet <- fmap S.fromList $ mapM canonicalizePath inputs
    signal <- newEmptyMVar
    withManager $ \mgr -> do
      forM_ dirs $ \dir ->
        watchDir mgr dir (allEvents $ flip S.member inputSet) (doAllEvents $ putMVar signal)
      race getLine (takeMVar signal)
  case resp of
    Left _ -> return (Just inputs) -- canceled, so nop
    Right _ -> reload orig inputs >> watch orig inputs

processInput :: String ->
                IState -> [FilePath] -> FilePath -> Idris (Maybe [FilePath])
processInput cmd orig inputs efile
    = do i <- getIState
         let opts = idris_options i
         let quiet = opt_quiet opts
         let fn = fromMaybe "" (listToMaybe inputs)
         c <- colourise
         case parseCmd i "(input)" cmd of
            Failure (ErrInfo err _) ->   do iputStrLn $ show (fixColour c err)
                                            return (Just inputs)
            Success (Right Reload) ->
                reload orig inputs
            Success (Right Watch) ->
                if null inputs then
                  do iputStrLn "No loaded files to watch."
                     return (Just inputs)
                else
                  do iputStrLn efile
                     iputStrLn $ "Watching for .idr changes in " ++ show inputs ++ ", press enter to cancel."
                     watch orig inputs
            Success (Right (Load f toline)) ->
                -- The $!! here prevents a space leak on reloading.
                -- This isn't a solution - but it's a temporary stopgap.
                -- See issue #2386
                do putIState $!! orig { idris_options = idris_options i
                                      , idris_colourTheme = idris_colourTheme i
                                      }
                   clearErr
                   mod <- loadInputs [f] toline
                   return (Just mod)
            Success (Right (ModImport f)) ->
                do clearErr
                   fmod <- loadModule f (IBC_REPL True)
                   return (Just (inputs ++ maybe [] (:[]) fmod))
            Success (Right Edit) -> do -- takeMVar stvar
                               edit efile orig
                               return (Just inputs)
            Success (Right Proofs) -> do proofs orig
                                         return (Just inputs)
            Success (Right Quit) -> do when (not quiet) (iputStrLn "Bye bye")
                                       return Nothing
            Success (Right cmd ) -> do idrisCatch (process fn cmd)
                                          (\e -> do msg <- showErr e ; iputStrLn msg)
                                       return (Just inputs)
            Success (Left err) -> do runIO $ putStrLn err
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
         env <- runIO getEnvironment
         let editor = getEditor env
         let line = case errSpan i of
                        Just l -> '+' : show (fst (fc_start l))
                        Nothing -> ""
         let cmdLine = intercalate " " [editor, line, fixName f]
         runIO $ system cmdLine
         clearErr
  -- The $!! here prevents a space leak on reloading.
  -- This isn't a solution - but it's a temporary stopgap.
  -- See issue #2386
         putIState $!! orig { idris_options = idris_options i
                            , idris_colourTheme = idris_colourTheme i
                            }
         loadInputs [f] Nothing
--          clearOrigPats
         iucheck
         return ()
   where getEditor env | Just ed <- lookup "EDITOR" env = ed
                       | Just ed <- lookup "VISUAL" env = ed
                       | otherwise = "vi"
         fixName file | map toLower (takeExtension file) `elem` [".lidr", ".idr"] = quote file
                      | otherwise = quote $ addExtension file "idr"
            where
                quoteChar = if isWindows then '"' else '\''
                quote s = [quoteChar] ++ s ++ [quoteChar]



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
process fn (RunShellCommand cmd) = runIO $ system cmd >> return ()
process fn (ChangeDirectory f)
                 = do runIO $ setCurrentDirectory f
                      return ()
process fn (ModImport f) = do fmod <- loadModule f (IBC_REPL True)
                              case fmod of
                                Just pr -> isetPrompt pr
                                Nothing -> iPrintError $ "Can't find import " ++ f
process fn (Eval t)
                 = withErrorReflection $
                   do logParser 5 $ show t
                      getIState >>= flip warnDisamb t
                      (tm, ty) <- elabREPL (recinfo (fileFC "toplevel")) ERHS t
                      ctxt <- getContext
                      let tm' = perhapsForce $ normaliseBlocking ctxt []
                                                  [sUN "foreign",
                                                   sUN "prim_read",
                                                   sUN "prim_write"]
                                                 tm
                      let ty' = perhapsForce $ normaliseAll ctxt [] ty
                      -- Add value to context, call it "it"
                      updateContext (addCtxtDef (sUN "it") (Function ty' tm'))
                      ist <- getIState
                      logParser 3 $ "Raw: " ++ show (tm', ty')
                      logParser 10 $ "Debug: " ++ showEnvDbg [] tm'
                      let tmDoc = pprintDelab ist tm'
                          -- errReverse to make type more readable
                          tyDoc =  pprintDelab ist (errReverse ist ty')
                      iPrintTermWithType tmDoc tyDoc
  where perhapsForce tm | termSmallerThan 100 tm = force tm
                        | otherwise = tm

process fn (NewDefn decls) = do
        logParser 3 ("Defining names using these decls: " ++ show (showDecls verbosePPOption decls))
        mapM_ defineName namedGroups where
  namedGroups = groupBy (\d1 d2 -> getName d1 == getName d2) decls
  getName :: PDecl -> Maybe Name
  getName (PTy docs argdocs syn fc opts name _ ty) = Just name
  getName (PClauses fc opts name (clause:clauses)) = Just (getClauseName clause)
  getName (PData doc argdocs syn fc opts dataDecl) = Just (d_name dataDecl)
  getName (PInterface doc syn fc constraints name nfc parms parmdocs fds decls _ _) = Just name
  getName _ = Nothing
  -- getClauseName is partial and I am not sure it's used safely! -- trillioneyes
  getClauseName (PClause fc name whole with rhs whereBlock) = name
  getClauseName (PWith fc name whole with rhs pn whereBlock) = name
  defineName :: [PDecl] -> Idris ()
  defineName (tyDecl@(PTy docs argdocs syn fc opts name _ ty) : decls) = do
    elabDecl EAll info tyDecl
    elabClauses info fc opts name (concatMap getClauses decls)
    setReplDefined (Just name)
  defineName [PClauses fc opts _ [clause]] = do
    let pterm = getRHS clause
    (tm,ty) <- elabVal info ERHS pterm
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
  defineName (PSyntax _ syntax:_) = do
    i <- get
    put (addReplSyntax i syntax)
  defineName decls = do
    elabDecls (toplevelWith fn) (map fixClauses decls)
    setReplDefined (getName (head decls))
  getClauses (PClauses fc opts name clauses) = clauses
  getClauses _ = []
  getRHS :: PClause -> PTerm
  getRHS (PClause fc name whole with rhs whereBlock) = rhs
  getRHS (PWith fc name whole with rhs pn whereBlock) = rhs
  getRHS (PClauseR fc with rhs whereBlock) = rhs
  getRHS (PWithR fc with rhs pn whereBlock) = rhs
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
  fixClauses (PImplementation doc argDocs syn fc constraints pnames acc opts cls nfc parms pextra ty implName decls) =
    PImplementation doc argDocs syn fc constraints pnames acc opts cls nfc parms pextra ty implName (map fixClauses decls)
  fixClauses decl = decl

  info = recinfo (fileFC "toplevel")

process fn (Undefine names) = undefine names
  where
    undefine :: [Name] -> Idris ()
    undefine [] = do
      allDefined <- idris_repl_defs `fmap` get
      undefine' allDefined []
    -- Keep track of which names you've removed so you can
    -- print them out to the user afterward
    undefine names = undefine' names []
    undefine' [] list = do iRenderResult $ printUndefinedNames list
                           return ()
    undefine' (n:names) already = do
      allDefined <- idris_repl_defs `fmap` get
      if n `elem` allDefined
         then do undefinedJustNow <- undefClosure n
                 undefine' names (undefinedJustNow ++ already)
         else do tclift $ tfail $ Msg ("Can't undefine " ++ show n ++ " because it wasn't defined at the repl")
                 undefine' names already
    undefOne n = do fputState (ctxt_lookup n . known_terms) Nothing
                    -- for now just assume it's an interface. Eventually we'll want some kind of
                    -- smart detection of exactly what kind of name we're undefining.
                    fputState (ctxt_lookup n . known_interfaces) Nothing
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
                       (tm, ty) <- elabVal (recinfo (fileFC "toplevel")) ERHS t
--                       let tm' = normaliseAll ctxt [] tm
                       let ty' = normaliseAll ctxt [] ty
                       res <- execute tm
                       let (resOut, tyOut) = (prettyIst ist (delab ist res),
                                              prettyIst ist (delab ist ty'))
                       iPrintTermWithType resOut tyOut

process fn (Check (PRef _ _ n))
   = do ctxt <- getContext
        ist <- getIState
        let ppo = ppOptionIst ist
        case lookupNames n ctxt of
          ts@(t:_) ->
            case lookup t (idris_metavars ist) of
                Just (_, i, _, _, _) -> iRenderResult . fmap (fancifyAnnots ist True) $
                                        showMetavarInfo ppo ist n i
                Nothing -> iPrintFunTypes [] n (map (\n -> (n, pprintDelabTy ist n)) ts)
          [] -> iPrintError $ "No such variable " ++ show n
  where
    showMetavarInfo ppo ist n i
         = case lookupTy n (tt_ctxt ist) of
                (ty:_) -> let ty' = normaliseC (tt_ctxt ist) [] ty in
                              putTy ppo ist i [] (delab ist (errReverse ist ty'))
    putTy :: PPOption -> IState -> Int -> [(Name, Bool)] -> PTerm -> Doc OutputAnnotation
    putTy ppo ist 0 bnd sc = putGoal ppo ist bnd sc
    putTy ppo ist i bnd (PPi _ n _ t sc)
               = let current = case n of
                                   MN _ _ -> text ""
                                   UN nm | ('_':'_':_) <- str nm -> text ""
                                   _ -> text "  " <>
                                        bindingOf n False
                                            <+> colon
                                            <+> align (tPretty bnd ist t)
                                            <> line
                 in
                    current <> putTy ppo ist (i-1) ((n,False):bnd) sc
    putTy ppo ist _ bnd sc = putGoal ppo ist ((n,False):bnd) sc
    putGoal ppo ist bnd g
               = text "--------------------------------------" <$>
                 annotate (AnnName n Nothing Nothing Nothing) (text $ show n) <+> colon <+>
                 align (tPretty bnd ist g)

    tPretty bnd ist t = pprintPTerm (ppOptionIst ist) bnd [] (idris_infixes ist) t


process fn (Check t)
   = do (tm, ty) <- elabREPL (recinfo (fileFC "toplevel")) ERHS t
        ctxt <- getContext
        ist <- getIState
        let ppo = ppOptionIst ist
            ty' = if opt_evaltypes (idris_options ist)
                     then normaliseC ctxt [] ty
                     else ty
        case tm of
           TType _ ->
             iPrintTermWithType (prettyIst ist (PType emptyFC)) type1Doc
           _ -> iPrintTermWithType (pprintDelab ist tm)
                                   (pprintDelab ist ty')

process fn (Core t)
   = case t of
       PRef _ _ n ->
         do ist <- getIState
            case lookupDef n (tt_ctxt ist) of
              [CaseOp _ _ _ _ _ _] -> pprintDef True n >>= iRenderResult . vsep
              _ -> coreTerm t
       t -> coreTerm t
   where coreTerm t =
           do (tm, ty) <- elabREPL (recinfo (fileFC "toplevel")) ERHS t
              iPrintTermWithType (pprintTT [] tm) (pprintTT [] ty)

process fn (DocStr (Left n) w)
  | UN ty <- n, ty == T.pack "Type" = getIState >>= iRenderResult . pprintTypeDoc
  | otherwise = do
        ist <- getIState
        let docs = lookupCtxtName n (idris_docstrings ist) ++
                   map (\(n,d)-> (n, (d, [])))
                       (lookupCtxtName (modDocN n) (idris_moduledocs ist))
        case docs of
          [] -> iPrintError $ "No documentation for " ++ show n
          ns -> do toShow <- mapM (showDoc ist) ns
                   iRenderResult (vsep toShow)
    where showDoc ist (n, d) = do doc <- getDocs n w
                                  return $ pprintDocs ist doc

          modDocN (NS (UN n) ns) = NS modDocName (n:ns)
          modDocN (UN n)         = NS modDocName [n]
          modDocN _              = sMN 1 "NotFoundForSure"

process fn (DocStr (Right c) _) -- constants only have overviews
   = do ist <- getIState
        iRenderResult $ pprintConstDocs ist c (constDocs c)

process fn Universes
                     = do i <- getIState
                          let cs = idris_constraints i
                          let cslist = S.toAscList cs
--                        iputStrLn $ showSep "\n" (map show cs)
                          iputStrLn $ showSep "\n" (map show cslist)
                          let n = length cslist
                          iputStrLn $ "(" ++ show n ++ " constraints)"
                          case ucheck cs of
                            Error e -> iPrintError $ pshow i e
                            OK _ -> iPrintResult "Universes OK"
process fn (Defn n)
                    = do i <- getIState
                         let head = text "Compiled patterns:" <$>
                                    text (show (lookupDef n (tt_ctxt i)))
                         let defs =
                              case lookupCtxt n (idris_patdefs i) of
                                [] -> empty
                                [(d, _)] -> text "Original definiton:" <$>
                                            vsep (map (printCase i) d)
                         let tot =
                              case lookupTotal n (tt_ctxt i) of
                                 [t] -> showTotal t i
                                 _ -> empty
                         iRenderResult $ vsep [head, defs, tot]
    where printCase i (_, lhs, rhs)
             = let i' = i { idris_options = (idris_options i) { opt_showimp = True } }
               in text (showTm i' (delab i lhs)) <+> text "=" <+>
                  text (showTm i' (delab i rhs))
process fn (TotCheck n)
   = do i <- getIState
        case lookupNameTotal n (tt_ctxt i) of
           []  -> iPrintError $ "Unknown operator " ++ show n
           ts  -> do ist <- getIState
                     c <- colourise
                     let ppo =  ppOptionIst ist
                     let showN n = annotate (AnnName n Nothing Nothing Nothing) . text $
                                   showName (Just ist) [] ppo False n
                     iRenderResult . vsep .
                      map (\(n, t) -> hang 4 $ showN n <+> text "is" <+> showTotal t i) $
                      ts

process fn (DebugUnify l r)
   = do (ltm, _) <- elabVal (recinfo (fileFC "toplevel")) ERHS l
        (rtm, _) <- elabVal (recinfo (fileFC "toplevel")) ERHS r
        ctxt <- getContext
        case unify ctxt [] (ltm, Nothing) (rtm, Nothing) [] [] [] [] of
             OK ans -> iputStrLn (show ans)
             Error e -> iputStrLn (show e)

process fn (DebugInfo n)
   = do i <- getIState
        let oi = lookupCtxtName n (idris_optimisation i)
        when (not (null oi)) $ iputStrLn (show oi)
        let si = lookupCtxt n (idris_statics i)
        when (not (null si)) $ iputStrLn (show si)
        let di = lookupCtxt n (idris_datatypes i)
        when (not (null di)) $ iputStrLn (show di)
        let imps = lookupCtxt n (idris_implicits i)
        when (not (null imps)) $ iputStrLn (show imps)
        let d = lookupDefAcc n False (tt_ctxt i)
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
process fn (Search pkgs t) = searchByType pkgs t
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
process fn (MakeCase updatefile l n)
    = makeCase fn updatefile l n
process fn (MakeLemma updatefile l n)
    = makeLemma fn updatefile l n
process fn (DoProofSearch updatefile rec l n hints)
    = doProofSearch fn updatefile rec l n hints Nothing
process fn (Spec t)
                    = do (tm, ty) <- elabVal (recinfo (fileFC "toplevel")) ERHS t
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
                                 putIState $ i { idris_metavars = (n, (Nothing, 0, [], False, False)) : ms }

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
       prog <- runIO $ readSource fb
       i <- getIState
       let proofs = proof_list i
       n' <- case prf of
                Nothing -> case proofs of
                             [] -> ifail "No proof to add"
                             ((x, _) : _) -> return x
                Just nm -> return nm
       n <- resolveProof n'
       case lookup n proofs of
            Nothing -> iputStrLn "No proof to add"
            Just (mode, prf) ->
              do let script = if mode
                                 then showRunElab (lit fn) n prf
                                 else showProof (lit fn) n prf
                 let prog' = insertScript script ls
                 runIO $ writeSource fn (unlines prog')
                 removeProof n
                 iputStrLn $ "Added proof " ++ show n
             where ls = (lines prog)

process fn (ShowProof n')
  = do i <- getIState
       n <- resolveProof n'
       let proofs = proof_list i
       case lookup n proofs of
            Nothing -> iPrintError "No proof to show"
            Just (m, p)  -> iPrintResult $ if m
                                             then showRunElab False n p
                                             else showProof False n p

process fn (Prove mode n')
     = do ctxt <- getContext
          ist <- getIState
          let ns = lookupNames n' ctxt
          let metavars = mapMaybe (\n -> do c <- lookup n (idris_metavars ist); return (n, c)) ns
          n <- case metavars of
              [] -> ierror (Msg $ "Cannot find metavariable " ++ show n')
              [(n, (_,_,_,False,_))] -> return n
              [(_, (_,_,_,_,False))]  -> ierror (Msg "Can't prove this hole as it depends on other holes")
              [(_, (_,_,_,True,_))]  -> ierror (Msg "Declarations not solvable using prover")
              ns -> ierror (CantResolveAlts (map fst ns))
          prover (toplevelWith fn) mode (lit fn) n
          -- recheck totality
          i <- getIState
          totcheck (fileFC "(input)", n)
          mapM_ (\ (f,n) -> setTotality n Unchecked) (idris_totcheck i)
          mapM_ checkDeclTotality (idris_totcheck i)
          warnTotality
process fn (WHNF t)
                    = do (tm, ty) <- elabVal (recinfo (fileFC "toplevel")) ERHS t
                         ctxt <- getContext
                         ist <- getIState
                         let tm' = whnf ctxt [] tm
                         let tmArgs' = whnfArgs ctxt [] tm
                         iPrintResult $ "WHNF: " ++ (show (delab ist tm'))
                         iPrintResult $ "WHNF args: " ++ (show (delab ist tmArgs'))
process fn (TestInline t)
                           = do (tm, ty) <- elabVal (recinfo (fileFC "toplevel")) ERHS t
                                ctxt <- getContext
                                ist <- getIState
                                let tm' = inlineTerm ist tm
                                c <- colourise
                                iPrintResult (showTm ist (delab ist tm'))
process fn (Execute tm)
                   = idrisCatch
                       (do ist <- getIState
                           (m_in, _) <- elabVal (recinfo (fileFC "toplevel")) ERHS (elabExec fc tm)
                           m <- applyOpts m_in
                           (tmpn, tmph) <- runIO $ tempfile ""
                           runIO $ hClose tmph
                           t <- codegen
                           -- gcc adds .exe when it builds windows programs
                           progName <- return $ if isWindows then tmpn ++ ".exe" else tmpn
                           ir <- compile t tmpn (Just m)
                           runIO $ generate t (fst (head (idris_imported ist))) ir
                           case idris_outputmode ist of
                             RawOutput h -> do runIO $ rawSystem progName []
                                               return ()
                             IdeMode n h -> runIO . hPutStrLn h $
                                             IdeMode.convSExp "run-program" tmpn n)
                       (\e -> getIState >>= iRenderError . flip pprintErr e)
  where fc = fileFC "main"
process fn (Compile codegen f)
      | map toLower (takeExtension f) `elem` [".idr", ".lidr", ".idc"] =
          iPrintError $ "Invalid filename for compiler output \"" ++ f ++"\""
      | otherwise = do opts <- getCmdLine
                       let iface = Interface `elem` opts
                       let mainname = sNS (sUN "main") ["Main"]

                       m <- if iface then return Nothing else
                            do (m', _) <- elabVal (recinfo (fileFC "compiler")) ERHS
                                            (PApp fc (PRef fc [] (sUN "run__IO"))
                                            [pexp $ PRef fc [] mainname])
                               return (Just m')
                       ir <- compile codegen f m
                       i <- getIState
                       runIO $ generate codegen (fst (head (idris_imported i))) ir
  where fc = fileFC "main"
process fn (LogLvl i) = setLogLevel i
process fn (LogCategory cs) = setLogCats cs
-- Elaborate as if LHS of a pattern (debug command)
process fn (Pattelab t)
     = do (tm, ty) <- elabVal (recinfo (fileFC "toplevel")) ELHS t
          iPrintResult $ show tm ++ "\n\n : " ++ show ty

process fn (Missing n)
    = do i <- getIState
         ppOpts <- fmap ppOptionIst getIState
         case lookupCtxt n (idris_patdefs i) of
           [] -> iPrintError $ "Unknown name " ++ show n
           [(_, tms)] ->
             iRenderResult (vsep (map (pprintPTerm ppOpts
                                                   []
                                                   []
                                                   (idris_infixes i))
                                      tms))
           _ -> iPrintError "Ambiguous name"
process fn (DynamicLink l)
                           = do i <- getIState
                                let importdirs = opt_importdirs (idris_options i)
                                    lib = trim l
                                handle <- lift . lift $ tryLoadLib importdirs lib
                                case handle of
                                  Nothing -> iPrintError $ "Could not load dynamic lib \"" ++ l ++ "\""
                                  Just x -> do let libs = idris_dynamic_libs i
                                               if x `elem` libs
                                                  then do logParser 1 ("Tried to load duplicate library " ++ lib_name x)
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
                        [] -> iPrintError "No global holes to solve"
                        _ -> iPrintResult $ "Global holes:\n\t" ++ show mvs
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
process fn (SetOpt EvalTypes)     = setEvalTypes True
process fn (UnsetOpt EvalTypes)   = setEvalTypes False

process fn (SetOpt DesugarNats)   = setDesugarNats True
process fn (UnsetOpt DesugarNats) = setDesugarNats False

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
process fn (SetPrinterDepth d) = setDepth d
process fn (Apropos pkgs a) =
  do orig <- getIState
     when (not (null pkgs)) $
       iputStrLn $ "Searching packages: " ++ showSep ", " pkgs
     mapM_ loadPkgIndex pkgs
     ist <- getIState
     let mods = aproposModules ist (T.pack a)
     let names = apropos ist (T.pack a)
     let aproposInfo = [ (n,
                          delabTy ist n,
                          fmap (overview . fst) (lookupCtxtExact n (idris_docstrings ist)))
                       | n <- sort names, isUN n ]
     if (not (null mods)) || (not (null aproposInfo))
        then iRenderResult $ vsep (map (\(m, d) -> text "Module" <+> text m <$>
                                                   ppD ist d <> line) mods) <$>
                             vsep (map (prettyDocumentedIst ist) aproposInfo)
        else iRenderError $ text "No results found"
  where isUN (UN _) = True
        isUN (NS n _) = isUN n
        isUN _ = False
        ppD ist = renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) []))


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

process fn (Browse ns) =
  do underNSs <- namespacesInNS ns
     names <- namesInNS ns
     if null underNSs && null names
        then iPrintError "Invalid or empty namespace"
        else do ist <- getIState
                iRenderResult $
                  text "Namespaces:" <$>
                  indent 2 (vsep (map (text . showSep ".") underNSs)) <$>
                  text "Names:" <$>
                  indent 2 (vsep (map (\n -> prettyName True False [] n <+> colon <+>
                                             (group . align $ pprintDelabTy ist n))
                                      names))

-- IdrisDoc
process fn (MakeDoc s) =
  do     istate        <- getIState
         let names      = words s
             parse n    | Success x <- runparser (fmap fst name) istate fn n = Right x
             parse n    = Left n
             (bad, nss) = partitionEithers $ map parse names
         cd            <- runIO getCurrentDirectory
         let outputDir  = cd </> "doc"
         result        <- if null bad then runIO $ generateDocs istate nss outputDir
                                      else return . Left $ "Illegal name: " ++ head bad
         case result of Right _   -> iputStrLn "IdrisDoc generated"
                        Left  err -> iPrintError err
process fn (PrintDef n) =
  do result <- pprintDef False n
     case result of
       [] -> iPrintError "Not found"
       outs -> iRenderResult . vsep $ outs

-- Show relevant transformation rules for the name 'n'
process fn (TransformInfo n)
   = do i <- getIState
        let ts = lookupCtxt n (idris_transforms i)
        let res = map (showTrans i) ts
        iRenderResult . vsep $ concat res
    where showTrans :: IState -> [(Term, Term)] -> [Doc OutputAnnotation]
          showTrans i [] = []
          showTrans i ((lhs, rhs) : ts)
              = let ppTm tm = annotate (AnnTerm [] tm) .
                                 pprintPTerm (ppOptionIst i) [] [] [] .
                                 delab i $ tm
                    ts' = showTrans i ts in
                    ppTm lhs <+> text " ==> " <+> ppTm rhs : ts'

--               iRenderOutput (pretty lhs)
--                    iputStrLn "  ==>  "
--                    iPrintTermWithType (pprintDelab i rhs)
--                    iputStrLn "---------------"
--                    showTrans i ts

process fn (PPrint fmt width (PRef _ _ n))
   = do outs <- pprintDef False n
        iPrintResult =<< renderExternal fmt width (vsep outs)


process fn (PPrint fmt width t)
   = do (tm, ty) <- elabVal (recinfo (fileFC "toplevel")) ERHS t
        ctxt <- getContext
        ist <- getIState
        let ppo = ppOptionIst ist
            ty' = normaliseC ctxt [] ty
        iPrintResult =<< renderExternal fmt width (pprintDelab ist tm)

showTotal :: Totality -> IState -> Doc OutputAnnotation
showTotal t@(Partial (Other ns)) i
   = text "possibly not total due to:" <$>
     vsep (map (showTotalN i) ns)
showTotal t@(Partial (Mutual ns)) i
   = text "possibly not total due to recursive path:" <$>
     align (group (vsep (punctuate comma
       (map (\n -> annotate (AnnName n Nothing Nothing Nothing) $
                   text (show n))
            ns))))
showTotal t i = text (show t)

showTotalN :: IState -> Name -> Doc OutputAnnotation
showTotalN ist n = case lookupTotal n (tt_ctxt ist) of
                        [t] -> showN n <> text ", which is" <+> showTotal t ist
                        _ -> empty
    where
       ppo = ppOptionIst ist
       showN n = annotate (AnnName n Nothing Nothing Nothing) . text $
                 showName (Just ist) [] ppo False n

displayHelp = let vstr = showVersion getIdrisVersionNoGit in
              "\nIdris version " ++ vstr ++ "\n" ++
              "--------------" ++ map (\x -> '-') vstr ++ "\n\n" ++
              concatMap cmdInfo helphead ++
              concatMap cmdInfo help
  where cmdInfo (cmds, args, text) = "   " ++ col 16 12 (showSep " " cmds) (show args) text
        col c1 c2 l m r =
            l ++ take (c1 - length l) (repeat ' ') ++
            m ++ take (c2 - length m) (repeat ' ') ++ r ++ "\n"

pprintDef :: Bool -> Name -> Idris [Doc OutputAnnotation]
pprintDef asCore n =
  do ist <- getIState
     ctxt <- getContext
     let ambiguous = length (lookupNames n ctxt) > 1
         patdefs = idris_patdefs ist
         tyinfo = idris_datatypes ist
     if asCore
       then return $ map (ppCoreDef ist) (lookupCtxtName n patdefs)
       else return $ map (ppDef ambiguous ist) (lookupCtxtName n patdefs) ++
                     map (ppTy ambiguous ist) (lookupCtxtName n tyinfo) ++
                     map (ppCon ambiguous ist) (filter (flip isDConName ctxt) (lookupNames n ctxt))
  where ppCoreDef :: IState -> (Name, ([([(Name, Term)], Term, Term)], [PTerm])) -> Doc OutputAnnotation
        ppCoreDef ist (n, (clauses, missing)) =
          case lookupTy n (tt_ctxt ist) of
            [] -> error "Attempted pprintDef of TT of thing that doesn't exist"
            (ty:_) -> prettyName True True [] n <+> colon <+>
                      align (annotate (AnnTerm [] ty) (pprintTT [] ty)) <$>
                      vsep (map (\(vars, lhs, rhs) ->  pprintTTClause vars lhs rhs) clauses)
        ppDef :: Bool -> IState -> (Name, ([([(Name, Term)], Term, Term)], [PTerm])) -> Doc OutputAnnotation
        ppDef amb ist (n, (clauses, missing)) =
          prettyName True amb [] n <+> colon <+>
          align (pprintDelabTy ist n) <$>
          ppClauses ist clauses <> ppMissing missing
        ppClauses ist [] = text "No clauses."
        ppClauses ist cs = vsep (map pp cs)
          where pp (varTys, lhs, rhs) =
                  let vars = map fst varTys
                      ppTm t = annotate (AnnTerm (zip vars (repeat False)) t) .
                               pprintPTerm (ppOptionIst ist)
                                     (zip vars (repeat False))
                                     [] (idris_infixes ist) .
                               delabWithEnv ist varTys $
                               t
                  in group $ ppTm lhs <+> text "=" <$> (group . align . hang 2 $ ppTm rhs)
        ppMissing _ = empty

        ppTy :: Bool -> IState -> (Name, TypeInfo) -> Doc OutputAnnotation
        ppTy amb ist (n, TI constructors isCodata _ _ _ _)
          = kwd key <+> prettyName True amb [] n <+> colon <+>
            align (pprintDelabTy ist n) <+> kwd "where" <$>
            indent 2 (vsep (map (ppCon False ist) constructors))
          where
            key | isCodata = "codata"
                | otherwise = "data"
            kwd = annotate AnnKeyword . text
        ppCon amb ist n = prettyName True amb [] n <+> colon <+> align (pprintDelabTy ist n)


helphead =
  [ (["Command"], SpecialHeaderArg, "Purpose"),
    ([""], NoArg, "")
  ]


replSettings :: Maybe FilePath -> Settings Idris
replSettings hFile = setComplete replCompletion $ defaultSettings {
                       historyFile = hFile
                     }

module Idris.Output where

import Idris.Core.TT
import Idris.Core.Evaluate (isDConName, isTConName, isFnName)

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Docstrings
import Idris.IdeSlave

import Util.Pretty
import Util.ScreenSize (getScreenWidth)

import System.IO (stdout, Handle, hPutStrLn)

pshow :: IState -> Err -> String
pshow ist err = displayDecorated (consoleDecorate ist) .
                renderPretty 1.0 80 .
                fmap (fancifyAnnots ist) $ pprintErr ist err

ihWarn :: Handle -> FC -> Doc OutputAnnotation -> Idris ()
ihWarn h fc err = do i <- getIState
                     case idris_outputmode i of
                       RawOutput ->
                         do err' <- iRender . fmap (fancifyAnnots i) $
                                    text (show fc) <> colon <//> err
                            runIO . hPutStrLn h $ displayDecorated (consoleDecorate i) err'
                       IdeSlave n ->
                         do err' <- iRender . fmap (fancifyAnnots i) $ err
                            let (str, spans) = displaySpans err'
                            runIO . hPutStrLn h $
                              convSExp "warning" (fc_fname fc, fc_start fc, fc_end fc, str, spans) n

iRender :: Doc a -> Idris (SimpleDoc a)
iRender d = do w <- getWidth
               ist <- getIState
               let ideSlave = case idris_outputmode ist of
                                IdeSlave _ -> True
                                _          -> False
               case w of
                 InfinitelyWide -> return $ renderPretty 1.0 1000000000 d
                 ColsWide n -> return $
                               if n < 1
                                 then renderPretty 1.0 1000000000 d
                                 else renderPretty 0.8 n d
                 AutomaticWidth | ideSlave  -> return $ renderPretty 1.0 1000000000 d
                                | otherwise -> do width <- runIO getScreenWidth
                                                  return $ renderPretty 0.8 width d

ihPrintResult :: Handle -> String -> Idris ()
ihPrintResult h s = do i <- getIState
                       case idris_outputmode i of
                         RawOutput -> case s of
                                        "" -> return ()
                                        s  -> runIO $ hPutStrLn h s
                         IdeSlave n ->
                             let good = SexpList [SymbolAtom "ok", toSExp s] in
                             runIO $ hPutStrLn h $ convSExp "return" good n

-- | Write a pretty-printed term to the console with semantic coloring
consoleDisplayAnnotated :: Handle -> Doc OutputAnnotation -> Idris ()
consoleDisplayAnnotated h output = do ist <- getIState
                                      rendered <- iRender $ output
                                      runIO . hPutStrLn h .
                                        displayDecorated (consoleDecorate ist) $
                                        rendered


-- | Write pretty-printed output to IDESlave with semantic annotations
ideSlaveReturnAnnotated :: Integer -> Handle -> Doc OutputAnnotation -> Idris ()
ideSlaveReturnAnnotated n h out = do ist <- getIState
                                     (str, spans) <- fmap displaySpans .
                                                     iRender .
                                                     fmap (fancifyAnnots ist) $
                                                     out
                                     let good = [SymbolAtom "ok", toSExp str, toSExp spans]
                                     runIO . hPutStrLn h $ convSExp "return" good n

ihPrintTermWithType :: Handle -> Doc OutputAnnotation -> Doc OutputAnnotation -> Idris ()
ihPrintTermWithType h tm ty = do ist <- getIState
                                 let output = tm <+> colon <+> align ty
                                 case idris_outputmode ist of
                                   RawOutput -> consoleDisplayAnnotated h output
                                   IdeSlave n -> ideSlaveReturnAnnotated n h output

-- | Pretty-print a collection of overloadings to REPL or IDESlave - corresponds to :t name
ihPrintFunTypes :: Handle -> [(Name, Bool)] -> Name -> [(Name, PTerm)] -> Idris ()
ihPrintFunTypes h bnd n []        = ihPrintError h $ "No such variable " ++ show n
ihPrintFunTypes h bnd n overloads = do imp <- impShow
                                       ist <- getIState
                                       let infixes = idris_infixes ist
                                       let output = vsep (map (uncurry (ppOverload imp infixes)) overloads)
                                       case idris_outputmode ist of
                                         RawOutput -> consoleDisplayAnnotated h output
                                         IdeSlave n -> ideSlaveReturnAnnotated n h output
  where fullName n = prettyName True bnd n
        ppOverload imp infixes n tm =
          fullName n <+> colon <+> align (pprintPTerm imp bnd [] infixes tm)

ihRenderResult :: Handle -> Doc OutputAnnotation -> Idris ()
ihRenderResult h d = do ist <- getIState
                        case idris_outputmode ist of
                          RawOutput -> consoleDisplayAnnotated h d
                          IdeSlave n -> ideSlaveReturnAnnotated n h d

fancifyAnnots :: IState -> OutputAnnotation -> OutputAnnotation
fancifyAnnots ist annot@(AnnName n _ _ _) =
  do let ctxt = tt_ctxt ist
         docs = docOverview ist n
         ty   = Just (getTy ist n)
     case () of
       _ | isDConName    n ctxt -> AnnName n (Just DataOutput) docs ty
       _ | isFnName      n ctxt -> AnnName n (Just FunOutput) docs ty
       _ | isTConName    n ctxt -> AnnName n (Just TypeOutput) docs ty
       _ | isMetavarName n ist  -> AnnName n (Just MetavarOutput) docs ty
       _ | otherwise            -> annot
  where docOverview :: IState -> Name -> Maybe String -- pretty-print first paragraph of docs
        docOverview ist n = do docs <- lookupCtxtExact n (idris_docstrings ist)
                               let o   = overview (fst docs)
                                   -- TODO make width configurable
                                   out = displayS . renderPretty 1.0 50 $ renderDocstring o
                               return (out "")
        getTy :: IState -> Name -> String -- fails if name not already extant!
        getTy ist n = let theTy = pprintPTerm (opt_showimp (idris_options ist)) [] [] (idris_infixes ist) $
                                  delabTy ist n
                      in (displayS . renderPretty 1.0 50 $ theTy) ""
fancifyAnnots _ annot = annot

-- | Show an error with semantic highlighting
ihRenderError :: Handle -> Doc OutputAnnotation -> Idris ()
ihRenderError h e = do ist <- getIState
                       case idris_outputmode ist of
                         RawOutput -> consoleDisplayAnnotated h e
                         IdeSlave n -> do
                           (str, spans) <- fmap displaySpans .
                                           iRender .
                                           fmap (fancifyAnnots ist) $
                                           e
                           let good = [SymbolAtom "error", toSExp str, toSExp spans]
                           runIO . hPutStrLn h $ convSExp "return" good n

ihPrintError :: Handle -> String -> Idris ()
ihPrintError h s = do i <- getIState
                      case idris_outputmode i of
                        RawOutput -> case s of
                                          "" -> return ()
                                          s  -> runIO $ hPutStrLn h s
                        IdeSlave n ->
                          let good = SexpList [SymbolAtom "error", toSExp s] in
                          runIO . hPutStrLn h $ convSExp "return" good n

ihputStrLn :: Handle -> String -> Idris ()
ihputStrLn h s = do i <- getIState
                    case idris_outputmode i of
                      RawOutput -> runIO $ hPutStrLn h s
                      IdeSlave n -> runIO . hPutStrLn h $ convSExp "write-string" s n

iputStrLn = ihputStrLn stdout
iPrintError = ihPrintError stdout
iPrintResult = ihPrintResult stdout
iWarn = ihWarn stdout

ideslavePutSExp :: SExpable a => String -> a -> Idris ()
ideslavePutSExp cmd info = do i <- getIState
                              case idris_outputmode i of
                                   IdeSlave n -> runIO . putStrLn $ convSExp cmd info n
                                   _ -> return ()

-- this needs some typing magic and more structured output towards emacs
iputGoal :: SimpleDoc OutputAnnotation -> Idris ()
iputGoal g = do i <- getIState
                case idris_outputmode i of
                  RawOutput -> runIO $ putStrLn (displayDecorated (consoleDecorate i) g)
                  IdeSlave n -> runIO . putStrLn $
                                convSExp "write-goal" (displayS (fmap (fancifyAnnots i) g) "") n

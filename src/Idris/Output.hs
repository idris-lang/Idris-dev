{-|
Module      : Idris.Output
Description : Utilities to display Idris' internals and other informtation to the user.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.Output where

import Idris.AbsSyntax
import Idris.Colours (hEndColourise, hStartColourise)
import Idris.Core.Evaluate (isDConName, isFnName, isTConName, normaliseAll)
import Idris.Core.TT
import Idris.Delaborate
import Idris.Docstrings
import Idris.IdeMode

import Util.Pretty
import Util.ScreenSize (getScreenWidth)
import Util.System (isATTY)

import Prelude hiding ((<$>))

import Control.Monad.Trans.Except (ExceptT(ExceptT), runExceptT)
import Data.Char (isAlpha)
import Data.List (intersperse, nub)
import Data.Maybe (fromMaybe)
import System.Console.Haskeline.MonadException (MonadException(controlIO),
                                                RunIO(RunIO))
import System.FilePath (replaceExtension)
import System.IO (Handle, hPutStr, hPutStrLn, stdout)

instance MonadException m => MonadException (ExceptT Err m) where
    controlIO f = ExceptT $ controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap ExceptT . run . runExceptT)
                    in fmap runExceptT $ f run'

pshow :: IState -> Err -> String
pshow ist err = displayDecorated (consoleDecorate ist) .
                renderPretty 1.0 80 .
                fmap (fancifyAnnots ist True) $ pprintErr ist err

iWarn :: FC -> Doc OutputAnnotation -> Idris ()
iWarn fc err =
  do i <- getIState
     case idris_outputmode i of
       RawOutput h ->
         do err' <- iRender . fmap (fancifyAnnots i True) $
                      case fc of
                        FC fn _ _ | fn /= "" -> text (show fc) <> colon <//> err
                        _ -> err
            hWriteDoc h i err'
       IdeMode n h ->
         do err' <- iRender . fmap (fancifyAnnots i True) $ err
            let (str, spans) = displaySpans err'
            runIO . hPutStrLn h $
              convSExp "warning" (fc_fname fc, fc_start fc, fc_end fc, str, spans) n

iRender :: Doc a -> Idris (SimpleDoc a)
iRender d = do w <- getWidth
               ist <- getIState
               let ideMode = case idris_outputmode ist of
                                IdeMode _ _ -> True
                                _            -> False
               tty <- runIO isATTY
               case w of
                 InfinitelyWide -> return $ renderPretty 1.0 1000000000 d
                 ColsWide n -> return $
                               if n < 1
                                 then renderPretty 1.0 1000000000 d
                                 else renderPretty 0.8 n d
                 AutomaticWidth | ideMode || not tty -> return $ renderPretty 1.0 80 d
                                | otherwise -> do width <- runIO getScreenWidth
                                                  return $ renderPretty 0.8 width d

hWriteDoc :: Handle -> IState -> SimpleDoc OutputAnnotation -> Idris ()
hWriteDoc h ist rendered =
    do runIO $ displayDecoratedA
                 (hPutStr h)
                 (maybe (return ()) (hStartColourise h))
                 (maybe (return ()) (hEndColourise h))
                 (fmap (annotationColour ist) rendered)
       runIO $ hPutStr h "\n" -- newline translation on the output
                              -- stream should take care of this for
                              -- Windows

-- | Write a pretty-printed term to the console with semantic coloring
consoleDisplayAnnotated :: Handle -> Doc OutputAnnotation -> Idris ()
consoleDisplayAnnotated h output =
    do ist <- getIState
       rendered <- iRender output
       hWriteDoc h ist rendered

iPrintTermWithType :: Doc OutputAnnotation -> Doc OutputAnnotation -> Idris ()
iPrintTermWithType tm ty = iRenderResult (tm <+> colon <+> align ty)

-- | Pretty-print a collection of overloadings to REPL or IDEMode - corresponds to :t name
iPrintFunTypes :: [(Name, Bool)] -> Name -> [(Name, Doc OutputAnnotation)] -> Idris ()
iPrintFunTypes bnd n []        = iPrintError $ "No such variable " ++ show n
iPrintFunTypes bnd n overloads = do ist <- getIState
                                    let ppo = ppOptionIst ist
                                    let infixes = idris_infixes ist
                                    let output = vsep (map (uncurry (ppOverload ppo infixes)) overloads)
                                    iRenderResult output
  where fullName ppo n | length overloads > 1 = prettyName True True bnd n
                       | otherwise = prettyName True (ppopt_impl ppo) bnd n
        ppOverload ppo infixes n tm =
          fullName ppo n <+> colon <+> align tm

iRenderOutput :: Doc OutputAnnotation -> Idris ()
iRenderOutput doc =
  do i <- getIState
     case idris_outputmode i of
       RawOutput h -> do out <- iRender doc
                         hWriteDoc h i out

       IdeMode n h ->
        do (str, spans) <- fmap displaySpans . iRender . fmap (fancifyAnnots i True) $ doc
           let out = [toSExp str, toSExp spans]
           runIO . hPutStrLn h $ convSExp "write-decorated" out n

iRenderResult :: Doc OutputAnnotation -> Idris ()
iRenderResult d = do ist <- getIState
                     case idris_outputmode ist of
                       RawOutput h  -> consoleDisplayAnnotated h d
                       IdeMode n h -> ideModeReturnAnnotated n h d

ideModeReturnWithStatus :: String -> Integer -> Handle -> Doc OutputAnnotation -> Idris ()
ideModeReturnWithStatus status n h out = do
  ist <- getIState
  (str, spans) <- fmap displaySpans .
                  iRender .
                  fmap (fancifyAnnots ist True) $
                  out
  let good = [SymbolAtom status, toSExp str, toSExp spans]
  runIO . hPutStrLn h $ convSExp "return" good n


-- | Write pretty-printed output to IDEMode with semantic annotations
ideModeReturnAnnotated :: Integer -> Handle -> Doc OutputAnnotation -> Idris ()
ideModeReturnAnnotated = ideModeReturnWithStatus "ok"

-- | Show an error with semantic highlighting
iRenderError :: Doc OutputAnnotation -> Idris ()
iRenderError e = do ist <- getIState
                    case idris_outputmode ist of
                      RawOutput h  -> consoleDisplayAnnotated h e
                      IdeMode n h -> ideModeReturnWithStatus "error" n h e

iPrintWithStatus :: String -> String -> Idris ()
iPrintWithStatus status s = do
  i <- getIState
  case idris_outputmode i of
    RawOutput h -> case s of
      "" -> return ()
      s  -> runIO $ hPutStrLn h s
    IdeMode n h ->
      let good = SexpList [SymbolAtom status, toSExp s] in
      runIO $ hPutStrLn h $ convSExp "return" good n


iPrintResult :: String -> Idris ()
iPrintResult = iPrintWithStatus "ok"

iPrintError :: String -> Idris ()
iPrintError = iPrintWithStatus "error"

iputStrLn :: String -> Idris ()
iputStrLn s = do i <- getIState
                 case idris_outputmode i of
                   RawOutput h  -> runIO $ hPutStrLn h s
                   IdeMode n h -> runIO . hPutStrLn h $ convSExp "write-string" s n

iputStr :: String -> Idris ()
iputStr s = do i <- getIState
               case idris_outputmode i of
                   RawOutput h  -> runIO $ hPutStr h s
                   IdeMode n h -> runIO . hPutStr h $ convSExp "write-string" s n

idemodePutSExp :: SExpable a => String -> a -> Idris ()
idemodePutSExp cmd info = do i <- getIState
                             case idris_outputmode i of
                               IdeMode n h ->
                                 runIO . hPutStrLn h $
                                   convSExp cmd info n
                               _ -> return ()

-- TODO: send structured output similar to the metavariable list
iputGoal :: SimpleDoc OutputAnnotation -> Idris ()
iputGoal g = do i <- getIState
                case idris_outputmode i of
                  RawOutput h -> hWriteDoc h i g
                  IdeMode n h ->
                    let (str, spans) = displaySpans . fmap (fancifyAnnots i True) $ g
                        goal = [toSExp str, toSExp spans]
                    in runIO . hPutStrLn h $ convSExp "write-goal" goal n

-- | Warn about totality problems without failing to compile
warnTotality :: Idris ()
warnTotality = do ist <- getIState
                  mapM_ (warn ist) (nub (idris_totcheckfail ist))
  where warn ist (fc, e) = iWarn fc (pprintErr ist (Msg e))


printUndefinedNames :: [Name] -> Doc OutputAnnotation
printUndefinedNames ns = text "Undefined " <> names <> text "."
  where names = encloseSep empty empty (char ',') $ map ppName ns
        ppName = prettyName True True []


prettyDocumentedIst :: IState
                    -> (Name, PTerm, Maybe (Docstring DocTerm))
                    -> Doc OutputAnnotation
prettyDocumentedIst ist (name, ty, docs) =
          prettyName True True [] name <+> colon <+> align (prettyIst ist ty) <$>
          fromMaybe empty (fmap (\d -> renderDocstring (renderDocTerm ppTm norm) d <> line) docs)
  where ppTm = pprintDelab ist
        norm = normaliseAll (tt_ctxt ist) []

sendParserHighlighting :: Idris ()
sendParserHighlighting =
  do ist <- getIState
     let hs = map unwrap . nub . map wrap $ idris_parserHighlights ist
     sendHighlighting hs
     ist <- getIState
     putIState ist {idris_parserHighlights = []}
  where wrap (fc, a) = (FC' fc, a)
        unwrap (fc', a) = (unwrapFC fc', a)

sendHighlighting :: [(FC, OutputAnnotation)] -> Idris ()
sendHighlighting highlights =
  do ist <- getIState
     case idris_outputmode ist of
       RawOutput _ -> updateIState $
                      \ist -> ist { idris_highlightedRegions =
                                      highlights ++ idris_highlightedRegions ist }
       IdeMode n h ->
         let fancier = [ toSExp (fc, fancifyAnnots ist False annot)
                       | (fc, annot) <- highlights, fullFC fc
                       ]
         in case fancier of
              [] -> return ()
              _  -> runIO . hPutStrLn h $
                      convSExp "output"
                               (SymbolAtom "ok",
                                (SymbolAtom "highlight-source", fancier)) n

  where fullFC (FC _ _ _) = True
        fullFC _          = False

-- | Write the highlighting information to a file, for use in external tools
-- or in editors that don't support the IDE protocol
writeHighlights :: FilePath -> Idris ()
writeHighlights f =
  do ist <- getIState
     let hs = reverse $ idris_highlightedRegions ist
     let hfile = replaceExtension f "idh"
     let annots = toSExp [ (fc, fancifyAnnots ist False annot)
                         | (fc@(FC _ _ _), annot) <- hs
                         ]
     runIO $ writeFile hfile $ sExpToString annots

clearHighlights :: Idris ()
clearHighlights = updateIState $ \ist -> ist { idris_highlightedRegions = [] }

renderExternal :: OutputFmt -> Int -> Doc OutputAnnotation -> Idris String
renderExternal fmt width doc
  | width < 1 = throwError . Msg $ "There must be at least one column for the pretty-printer."
  | otherwise =
    do ist <- getIState
       return . wrap fmt .
         displayDecorated (decorate fmt) .
         renderPretty 1.0 width .
         fmap (fancifyAnnots ist True) $
           doc
  where
    decorate _ (AnnFC _) = id

    decorate HTMLOutput (AnnName _ (Just TypeOutput) d _) =
      tag "idris-type" d
    decorate HTMLOutput (AnnName _ (Just FunOutput) d _) =
      tag "idris-function" d
    decorate HTMLOutput (AnnName _ (Just DataOutput) d _) =
      tag "idris-data" d
    decorate HTMLOutput (AnnName _ (Just MetavarOutput) d _) =
      tag "idris-metavar" d
    decorate HTMLOutput (AnnName _ (Just PostulateOutput) d _) =
      tag "idris-postulate" d
    decorate HTMLOutput (AnnName _ _ _ _) = id
    decorate HTMLOutput (AnnBoundName _ True) = tag "idris-bound idris-implicit" Nothing
    decorate HTMLOutput (AnnBoundName _ False) = tag "idris-bound" Nothing
    decorate HTMLOutput (AnnConst c) =
      tag (if constIsType c then "idris-type" else "idris-data")
          (Just $ constDocs c)
    decorate HTMLOutput (AnnData _ _) = tag "idris-data" Nothing
    decorate HTMLOutput (AnnType _ _) = tag "idris-type" Nothing
    decorate HTMLOutput AnnKeyword = tag "idris-keyword" Nothing
    decorate HTMLOutput (AnnTextFmt fmt) =
      case fmt of
        BoldText -> mkTag "strong"
        ItalicText -> mkTag "em"
        UnderlineText -> tag "idris-underlined" Nothing
      where mkTag t x = "<"++t++">"++x++"</"++t++">"
    decorate HTMLOutput (AnnTerm _ _) = id
    decorate HTMLOutput (AnnSearchResult _) = id
    decorate HTMLOutput (AnnErr _) = id
    decorate HTMLOutput (AnnNamespace _ _) = id
    decorate HTMLOutput (AnnLink url) =
      \txt -> "<a href=\"" ++ url ++ "\">" ++ txt ++ "</a>"
    decorate HTMLOutput AnnQuasiquote = id
    decorate HTMLOutput AnnAntiquote = id

    decorate LaTeXOutput (AnnName _ (Just TypeOutput) _ _) =
      latex "IdrisType"
    decorate LaTeXOutput (AnnName _ (Just FunOutput) _ _) =
      latex "IdrisFunction"
    decorate LaTeXOutput (AnnName _ (Just DataOutput) _ _) =
      latex "IdrisData"
    decorate LaTeXOutput (AnnName _ (Just MetavarOutput) _ _) =
      latex "IdrisMetavar"
    decorate LaTeXOutput (AnnName _ (Just PostulateOutput) _ _) =
      latex "IdrisPostulate"
    decorate LaTeXOutput (AnnName _ _ _ _) = id
    decorate LaTeXOutput (AnnBoundName _ True) = latex "IdrisImplicit"
    decorate LaTeXOutput (AnnBoundName _ False) = latex "IdrisBound"
    decorate LaTeXOutput (AnnConst c) =
      latex $ if constIsType c then "IdrisType" else "IdrisData"
    decorate LaTeXOutput (AnnData _ _) = latex "IdrisData"
    decorate LaTeXOutput (AnnType _ _) = latex "IdrisType"
    decorate LaTeXOutput AnnKeyword = latex "IdrisKeyword"
    decorate LaTeXOutput (AnnTextFmt fmt) =
      case fmt of
        BoldText -> latex "textbf"
        ItalicText -> latex "emph"
        UnderlineText -> latex "underline"
    decorate LaTeXOutput (AnnTerm _ _) = id
    decorate LaTeXOutput (AnnSearchResult _) = id
    decorate LaTeXOutput (AnnErr _) = id
    decorate LaTeXOutput (AnnNamespace _ _) = id
    decorate LaTeXOutput (AnnLink url) = (++ "(\\url{" ++ url ++ "})")
    decorate LaTeXOutput AnnQuasiquote = id
    decorate LaTeXOutput AnnAntiquote = id

    tag cls docs str = "<span class=\""++cls++"\""++title++">" ++ str ++ "</span>"
      where title = maybe "" (\d->" title=\"" ++ d ++ "\"") docs

    latex cmd str = "\\"++cmd++"{"++str++"}"

    wrap HTMLOutput str =
      "<!doctype html><html><head><style>" ++ css ++ "</style></head>" ++
      "<body><!-- START CODE --><pre>" ++ str ++ "</pre><!-- END CODE --></body></html>"
      where css = concat . intersperse "\n" $
                    [".idris-data { color: red; } ",
                     ".idris-type { color: blue; }",
                     ".idris-function {color: green; }",
                     ".idris-keyword { font-weight: bold; }",
                     ".idris-bound { color: purple; }",
                     ".idris-implicit { font-style: italic; }",
                     ".idris-underlined { text-decoration: underline; }"]
    wrap LaTeXOutput str =
      concat . intersperse "\n" $
        ["\\documentclass{article}",
         "\\usepackage{fancyvrb}",
         "\\usepackage[usenames]{xcolor}"] ++
        map (\(cmd, color) ->
               "\\newcommand{\\"++ cmd ++
               "}[1]{\\textcolor{"++ color ++"}{#1}}")
             [("IdrisData", "red"), ("IdrisType", "blue"),
              ("IdrisBound", "magenta"), ("IdrisFunction", "green")] ++
        ["\\newcommand{\\IdrisKeyword}[1]{{\\underline{#1}}}",
         "\\newcommand{\\IdrisImplicit}[1]{{\\itshape \\IdrisBound{#1}}}",
         "\n",
         "\\begin{document}",
         "% START CODE",
         "\\begin{Verbatim}[commandchars=\\\\\\{\\}]",
         str,
         "\\end{Verbatim}",
         "% END CODE",
         "\\end{document}"]

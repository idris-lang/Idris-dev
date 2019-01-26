{-|
Module      : Idris.Output
Description : Utilities to display Idris' internals and other informtation to the user.

License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE CPP, FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.Output (clearHighlights, emitWarning, formatMessage, idemodePutSExp,
                     iPrintError, iPrintFunTypes, iPrintResult, iPrintTermWithType,
                     iputGoal, iputStr, iputStrLn, iRender, iRenderError,
                     iRenderOutput, iRenderResult, iWarn, prettyDocumentedIst,
                     printUndefinedNames, pshow, renderExternal, sendHighlighting,
                     sendParserHighlighting, warnTotality, writeHighlights,
                     OutputDoc(..), Message(..)) where

import Idris.AbsSyntax
import Idris.Colours (hEndColourise, hStartColourise)
import Idris.Core.Evaluate (normaliseAll)
import Idris.Core.TT
import Idris.Delaborate
import Idris.Docstrings
import Idris.IdeMode
import Idris.Options

import Util.Pretty
import Util.ScreenSize (getScreenWidth)
import Util.System (isATTY)

#if (MIN_VERSION_base(4,11,0))
import Prelude hiding ((<$>), (<>))
#else
import Prelude hiding ((<$>))
#endif

import Control.Arrow (first)
import Control.Monad.Trans.Except (ExceptT(ExceptT), runExceptT)
import Data.List (intersperse, nub)
import Data.Maybe (fromJust, fromMaybe, isJust, listToMaybe)
import qualified Data.Set as S
import System.Console.Haskeline.MonadException (MonadException(controlIO),
                                                RunIO(RunIO))
import System.FilePath (replaceExtension)
import System.IO (Handle, hPutStr, hPutStrLn)
import System.IO.Error (tryIOError)

instance MonadException m => MonadException (ExceptT Err m) where
    controlIO f = ExceptT $ controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap ExceptT . run . runExceptT)
                    in fmap runExceptT $ f run'

pshow :: IState -> Err -> String
pshow ist err = displayDecorated (consoleDecorate ist) .
                renderPretty 1.0 80 .
                fmap (fancifyAnnots ist True) $ pprintErr ist err

type OutputDoc = Doc OutputAnnotation

class Message a where
  messageExtent :: a -> FC
  messageText :: a -> OutputDoc
  messageSource :: a -> Maybe String

data Ann = AText String | ATagged OutputAnnotation Ann | ASplit Ann Ann

data SimpleWarning = SimpleWarning FC OutputDoc
instance Message SimpleWarning where
  messageExtent (SimpleWarning extent _) = extent
  messageText (SimpleWarning _ msg) = msg
  messageSource _ = Nothing

formatMessage :: Message w => w -> Idris OutputDoc
formatMessage w = do
    i <- getIState
    rs <- readSource fc
    let maybeSource = case rs of
          Just src -> Just src
          Nothing -> messageSource w
    let maybeFormattedSource = maybeSource >>= layoutSource fc (regions (idris_highlightedRegions i))
    return $ layoutMessage (layoutFC fc) maybeFormattedSource (messageText w)
  where
    regions :: S.Set (FC', OutputAnnotation) -> [(FC, OutputAnnotation)]
    regions rs = map (\(FC' a,b) -> (a, b)) $ S.toList rs

    fc :: FC
    fc = messageExtent w

    layoutFC :: FC -> OutputDoc
    layoutFC fc@(FC fn _ _) | fn /= "" = text (show $ fc) <> colon
    layoutFC _                         = empty

    readSource :: FC -> Idris (Maybe String)
    readSource (FC fn _ _) = do
      result <- runIO $ tryIOError (readFile fn)
      case result of
        Left _  -> pure Nothing
        Right v -> pure (Just v)
    readSource _           = pure Nothing

    layoutSource :: FC -> [(FC, OutputAnnotation)] -> String -> Maybe OutputDoc
    layoutSource (FC fn (si, sj) (ei, ej)) highlights src =
        if haveSource
        then Just source
        else Nothing
      where
        sourceLine :: Maybe String
        sourceLine = listToMaybe . drop (si - 1) . (++ ["<end of file>"]) . lines $ src

        haveSource :: Bool
        haveSource = isJust sourceLine

        line1 :: OutputDoc
        line1 = text $ replicate (length (show si)) ' ' ++ " |"

        lineFC :: FC
        lineFC = FC fn (si, 1) (si, length (fromJust sourceLine))

        intersects :: FC -> FC -> Bool
        intersects (FC fn1 s1 e1) (FC fn2 s2 e2)
          | fn1 /= fn2 = False
          | e1 < s2    = False
          | e2 < s1    = False
          | otherwise  = True
        intersects _ _ = False

        intersection :: FC -> FC -> FC
        intersection fc1@(FC fn1 s1 e1) fc2@(FC _ s2 e2)
          | intersects fc1 fc2 = FC fn1 (max s1 s2) (min e1 e2)
          | otherwise          = NoFC
        intersection _ _       = NoFC

        width :: Ann -> Int
        width (AText s)     = length s
        width (ATagged _ n) = width n
        width (ASplit l r)  = width l + width r

        sourceDoc :: Ann -> OutputDoc
        sourceDoc (AText s)     = text s
        sourceDoc (ATagged a n) = annotate a (sourceDoc n)
        sourceDoc (ASplit l r)  = sourceDoc l <> sourceDoc r

        insertAnnotation :: ((Int, Int), OutputAnnotation) -> Ann -> Ann
        insertAnnotation ((sj, ej), oa) (ATagged tag n) = ATagged tag (insertAnnotation ((sj, ej), oa) n)
        insertAnnotation ((sj, ej), oa) (ASplit l r)
          | w <- width l                   = ASplit (insertAnnotation ((sj, ej), oa) l) (insertAnnotation ((sj - w, ej - w), oa) r)
        insertAnnotation ((sj, ej), oa) a@(AText t)
          | sj <= 1, ej >= width a         = ATagged oa a
          | sj > 1,  sj <= width a         = ASplit (AText $ take (sj - 1) t) (insertAnnotation ((1, ej - sj + 1), oa) (AText $ drop (sj - 1) t))
          | sj == 1, ej >= 1, ej < width a = ASplit (insertAnnotation ((1, ej), oa) (AText $ take ej t)) (AText $ drop ej t)
          | otherwise                      = a

        highlightedSource :: OutputDoc
        highlightedSource = sourceDoc .
                            foldr insertAnnotation (AText $ fromJust sourceLine) .
                            map (\(FC _ (_, sj) (_, ej), ann) -> ((sj, ej), ann)) .
                            map (first (intersection lineFC)) .
                            filter (intersects lineFC . fst) $
                            highlights

        line2 :: OutputDoc
        line2 = text (show si ++ " | ") <> highlightedSource

        indicator :: OutputDoc
        indicator = text (replicate (end - sj + 1) ch) <> ellipsis
          where
            (end, ch, ellipsis) = case (si == ei, sj == ej) of
              (True , True ) -> (ej, '^', empty)
              (True , False) -> (ej, '~', empty)
              (False, _    ) -> (length (fromJust sourceLine), '~', text " ...")

        line3 :: OutputDoc
        line3 = line1 <> text (replicate sj ' ') <> indicator

        source :: OutputDoc
        source = line1 <$$> line2 <$$> line3
    layoutSource _ _ _                                    = Nothing

    layoutMessage :: OutputDoc -> Maybe OutputDoc -> OutputDoc -> OutputDoc
    layoutMessage loc (Just src) err = loc <$$> src <$$> err <$$> empty
    layoutMessage loc Nothing    err = loc </> err

iWarn :: FC -> OutputDoc -> Idris ()
iWarn fc err = emitWarning $ SimpleWarning fc err

emitWarning :: Message w => w -> Idris ()
emitWarning w =
  do i <- getIState
     case idris_outputmode i of
       RawOutput h ->
         do formattedErr <- formatMessage w
            err' <- iRender . fmap (fancifyAnnots i True) $ formattedErr
            hWriteDoc h i err'
       IdeMode n h ->
         do err' <- iRender . fmap (fancifyAnnots i True) $ messageText w
            let fc = messageExtent w
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
     let hs = idris_parserHighlights ist
     sendHighlighting hs
     ist <- getIState
     putIState ist {idris_parserHighlights = S.empty}

sendHighlighting :: S.Set (FC', OutputAnnotation) -> Idris ()
sendHighlighting highlights =
  do ist <- getIState
     case idris_outputmode ist of
       RawOutput _ -> updateIState $
                      \ist -> ist { idris_highlightedRegions =
                                      S.union highlights (idris_highlightedRegions ist) }
       IdeMode n h ->
         let fancier = [ toSExp (fc, fancifyAnnots ist False annot)
                       | (FC' fc, annot) <- S.toList highlights, fullFC fc
                       ] in
            case fancier of
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
     let hs = reverse $ map (\(FC' a, b) -> (a,b)) $ S.toList (idris_highlightedRegions ist)
     let hfile = replaceExtension f "idh"
     let annots = toSExp [ (fc, fancifyAnnots ist False annot)
                         | (fc@(FC _ _ _), annot) <- hs
                         ]
     runIO $ writeFile hfile $ sExpToString annots

clearHighlights :: Idris ()
clearHighlights = updateIState $ \ist -> ist { idris_highlightedRegions = S.empty }

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
    decorate HTMLOutput (AnnSyntax c) = \txt -> c

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
    decorate LaTeXOutput (AnnSyntax c) = \txt ->
      case c of
        "\\" -> "\\textbackslash"
        "{" -> "\\{"
        "}" -> "\\}"
        "%" -> "\\%"
        _ -> c

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
                     ".idris-metavar {color: turquoise; }",
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
              ("IdrisBound", "magenta"), ("IdrisFunction", "green"),
              ("IdrisMetavar", "cyan")] ++
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

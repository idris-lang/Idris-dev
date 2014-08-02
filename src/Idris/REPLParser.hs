
module Idris.REPLParser(parseCmd) where

import System.FilePath ((</>))
import System.Console.ANSI (Color(..))

import Idris.Colours
import Idris.AbsSyntax
import Idris.Core.TT
import qualified Idris.Parser as P

import Control.Applicative
import Control.Monad.State.Strict

import Text.Parser.Combinators
import Text.Parser.Char(anyChar)
import Text.Trifecta(Result, parseString)
import Text.Trifecta.Delta

import Debug.Trace
import Data.List
import Data.List.Split(splitOn)
import Data.Char(toLower)
import qualified Data.ByteString.UTF8 as UTF8

parseCmd :: IState -> String -> String -> Result Command
parseCmd i inputname = P.runparser pCmd i inputname

cmd :: [String] -> P.IdrisParser ()
cmd xs = try (do P.lchar ':'; docmd (sortBy (\x y -> compare (length y) (length x)) xs))
    where docmd [] = fail "No such command"
          docmd (x:xs) = try (discard (P.reserved x)) <|> docmd xs

pCmd :: P.IdrisParser Command
pCmd = do P.whiteSpace; do cmd ["q", "quit"]; eof; return Quit
              <|> do cmd ["h", "?", "help"]; eof; return Help
              <|> do cmd ["w", "warranty"]; eof; return Warranty
              <|> do cmd ["r", "reload"]; eof; return Reload
              <|> do cmd ["module"]; f <- P.identifier; eof;
                          return (ModImport (toPath f))
              <|> do cmd ["e", "edit"]; eof; return Edit
              <|> do cmd ["exec", "execute"]; eof; return Execute
              <|> do cmd ["c", "compile"]
                     i <- get
                     c <- option (opt_codegen $ idris_options i) codegenOption
                     f <- P.identifier
                     eof
                     return (Compile c f)
              <|> do cmd ["proofs"]; eof; return Proofs
              <|> do cmd ["rmproof"]; n <- P.name; eof; return (RmProof n)
              <|> do cmd ["showproof"]; n <- P.name; eof; return (ShowProof n)
              <|> do cmd ["log"]; i <- P.natural; eof; return (LogLvl (fromIntegral i))
              <|> do cmd ["let"]
                     defn <- concat <$> many (P.decl defaultSyntax)
                     return (NewDefn defn)
              <|> do cmd ["lto", "loadto"];
                     toline <- P.natural
                     f <- many anyChar;
                     return (Load f (Just (fromInteger toline)))
              <|> do cmd ["l", "load"]; f <- many anyChar;
                     return (Load f Nothing)
              <|> do cmd ["cd"]; f <- many anyChar; return (ChangeDirectory f)
              <|> do cmd ["spec"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Spec t)
              <|> do cmd ["hnf"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (HNF t)
              <|> do cmd ["inline"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (TestInline t)
              <|> do c <- try (cmd ["doc"] *> P.constant); eof; return (DocStr (Right c))
              <|> do cmd ["doc"]; n <- (P.fnName <|> (P.string "_|_" >> return falseTy)); eof; return (DocStr (Left n))
              <|> do cmd ["d", "def"]; P.whiteSpace; n <- P.fnName; eof; return (Defn n)
              <|> do cmd ["total"]; do n <- P.fnName; eof; return (TotCheck n)
              <|> do cmd ["t", "type"]; do P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Check t)
              <|> do cmd ["u", "universes"]; eof; return Universes
              <|> do cmd ["di", "dbginfo"]; n <- P.fnName; eof; return (DebugInfo n)
              <|> do cmd ["miss", "missing"]; n <- P.fnName; eof; return (Missing n)
              <|> try (do cmd ["dynamic"]; eof; return ListDynamic)
              <|> do cmd ["dynamic"]; l <- many anyChar; return (DynamicLink l)
              <|> do cmd ["color", "colour"]; pSetColourCmd
              <|> do cmd ["set"]; o <- pOption; return (SetOpt o)
              <|> do cmd ["unset"]; o <- pOption; return (UnsetOpt o)
              <|> do cmd ["s", "search"]; P.whiteSpace;
                     t <- P.typeExpr (defaultSyntax { implicitAllowed = True }); return (Search t)
              <|> do cmd ["cs", "casesplit"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (CaseSplitAt upd (fromInteger l) n)
              <|> do cmd ["apc", "addproofclause"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (AddProofClauseFrom upd (fromInteger l) n)
              <|> do cmd ["ac", "addclause"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (AddClauseFrom upd (fromInteger l) n)
              <|> do cmd ["am", "addmissing"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (AddMissing upd (fromInteger l) n)
              <|> do cmd ["mw", "makewith"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (MakeWith upd (fromInteger l) n)
              <|> do cmd ["ml", "makelemma"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (MakeLemma upd (fromInteger l) n)
              <|> do cmd ["ps", "proofsearch"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     hints <- many P.fnName
                     return (DoProofSearch upd True (fromInteger l) n hints)
              <|> do cmd ["ref", "refine"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     hint <- P.fnName
                     return (DoProofSearch upd False (fromInteger l) n [hint])
              <|> do cmd ["p", "prove"]; n <- P.name; eof; return (Prove n)
              <|> do cmd ["m", "metavars"]; eof; return Metavars
              <|> do cmd ["a", "addproof"]; do n <- option Nothing (do x <- P.name;
                                                                       return (Just x))
                                               eof; return (AddProof n)
              <|> do cmd ["x"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (ExecVal t)
              <|> do cmd ["patt"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Pattelab t)
              <|> do cmd ["errorhandlers"]; eof ; return ListErrorHandlers
              <|> do cmd ["consolewidth"]; w <- pConsoleWidth ; return (SetConsoleWidth w)
              <|> do cmd ["apropos"]; str <- many anyChar ; return (Apropos str)
              <|> do cmd ["wc", "whocalls"]; P.whiteSpace; n <- P.fnName ; return (WhoCalls n)
              <|> do cmd ["cw", "callswho"]; P.whiteSpace; n <- P.fnName ; return (CallsWho n)
              <|> do cmd ["mkdoc"]; str <- many anyChar; return (MakeDoc str)
              <|> do P.whiteSpace; do eof; return NOP
                             <|> do t <- P.fullExpr defaultSyntax; return (Eval t)

 where toPath n = foldl1' (</>) $ splitOn "." n

pOption :: P.IdrisParser Opt
pOption = do discard (P.symbol "errorcontext"); return ErrContext
      <|> do discard (P.symbol "showimplicits"); return ShowImpl
      <|> do discard (P.symbol "originalerrors"); return ShowOrigErr
      <|> do discard (P.symbol "autosolve"); return AutoSolve
      <|> do discard (P.symbol "nobanner") ; return NoBanner
      <|> do discard (P.symbol "warnreach"); return WarnReach

codegenOption :: P.IdrisParser Codegen
codegenOption = do discard (P.symbol "javascript"); return ViaJavaScript
            <|> do discard (P.symbol "node"); return ViaNode
            <|> do discard (P.symbol "Java"); return ViaJava
            <|> do discard (P.symbol "llvm"); return ViaLLVM
            <|> do discard (P.symbol "bytecode"); return Bytecode
            <|> do discard (P.symbol "C"); return ViaC
            <|> do discard (P.symbol "Ruby"); return ViaRuby

pConsoleWidth :: P.IdrisParser ConsoleWidth
pConsoleWidth = do discard (P.symbol "auto"); return AutomaticWidth
            <|> do discard (P.symbol "infinite"); return InfinitelyWide
            <|> do n <- fmap fromInteger P.natural; return (ColsWide n)

colours :: [(String, Maybe Color)]
colours = [ ("black", Just Black)
          , ("red", Just Red)
          , ("green", Just Green)
          , ("yellow", Just Yellow)
          , ("blue", Just Blue)
          , ("magenta", Just Magenta)
          , ("cyan", Just Cyan)
          , ("white", Just White)
          , ("default", Nothing)
          ]

pColour :: P.IdrisParser (Maybe Color)
pColour = doColour colours
    where doColour [] = fail "Unknown colour"
          doColour ((s, c):cs) = (try (P.symbol s) >> return c) <|> doColour cs

pColourMod :: P.IdrisParser (IdrisColour -> IdrisColour)
pColourMod = try (P.symbol "vivid" >> return doVivid)
         <|> try (P.symbol "dull" >> return doDull)
         <|> try (P.symbol "underline" >> return doUnderline)
         <|> try (P.symbol "nounderline" >> return doNoUnderline)
         <|> try (P.symbol "bold" >> return doBold)
         <|> try (P.symbol "nobold" >> return doNoBold)
         <|> try (P.symbol "italic" >> return doItalic)
         <|> try (P.symbol "noitalic" >> return doNoItalic)
         <|> try (pColour >>= return . doSetColour)
    where doVivid i       = i { vivid = True }
          doDull i        = i { vivid = False }
          doUnderline i   = i { underline = True }
          doNoUnderline i = i { underline = False }
          doBold i        = i { bold = True }
          doNoBold i      = i { bold = False }
          doItalic i      = i { italic = True }
          doNoItalic i    = i { italic = False }
          doSetColour c i = i { colour = c }

-- | Generate the colour type names using the default Show instance.
colourTypes :: [(String, ColourType)]
colourTypes = map (\x -> ((map toLower . reverse . drop 6 . reverse . show) x, x)) $
              enumFromTo minBound maxBound

pColourType :: P.IdrisParser ColourType
pColourType = doColourType colourTypes
    where doColourType [] = fail $ "Unknown colour category. Options: " ++
                                   (concat . intersperse ", " . map fst) colourTypes
          doColourType ((s,ct):cts) = (try (P.symbol s) >> return ct) <|> doColourType cts

pSetColourCmd :: P.IdrisParser Command
pSetColourCmd = (do c <- pColourType
                    let defaultColour = IdrisColour Nothing True False False False
                    opts <- sepBy pColourMod (P.whiteSpace)
                    let colour = foldr ($) defaultColour $ reverse opts
                    return $ SetColour c colour)
            <|> try (P.symbol "on" >> return ColourOn)
            <|> try (P.symbol "off" >> return ColourOff)

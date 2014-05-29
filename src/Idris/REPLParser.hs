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
cmd xs = do P.lchar ':'; docmd (sortBy (\x y -> compare (length y) (length x)) xs)
    where docmd [] = fail "No such command"
          docmd (x:xs) = try (discard (P.symbol x)) <|> docmd xs

pCmd :: P.IdrisParser Command
pCmd = do P.whiteSpace; try (do cmd ["q", "quit"]; eof; return Quit)
              <|> try (do cmd ["h", "?", "help"]; eof; return Help)
              <|> try (do cmd ["r", "reload"]; eof; return Reload)
              <|> try (do cmd ["module"]; f <- P.identifier; eof;
                          return (ModImport (toPath f)))
              <|> try (do cmd ["e", "edit"]; eof; return Edit)
              <|> try (do cmd ["exec", "execute"]; eof; return Execute)
              <|> try (do cmd ["c", "compile"]
                          i <- get
                          c <- option (opt_codegen $ idris_options i) codegenOption
                          f <- P.identifier
                          eof
                          return (Compile c f))
              <|> try (do cmd ["proofs"]; eof; return Proofs)
              <|> try (do cmd ["rmproof"]; n <- P.name; eof; return (RmProof n))
              <|> try (do cmd ["showproof"]; n <- P.name; eof; return (ShowProof n))
              <|> try (do cmd ["log"]; i <- P.natural; eof; return (LogLvl (fromIntegral i)))
              <|> try (do cmd ["lto", "loadto"]; 
                          toline <- P.natural
                          f <- many anyChar; 
                          return (Load f (Just (fromInteger toline))))
              <|> try (do cmd ["l", "load"]; f <- many anyChar; 
                          return (Load f Nothing))
              <|> try (do cmd ["cd"]; f <- many anyChar; return (ChangeDirectory f))
              <|> try (do cmd ["spec"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Spec t))
              <|> try (do cmd ["hnf"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (HNF t))
              <|> try (do cmd ["inline"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (TestInline t))
              <|> try (do cmd ["doc"]; c <- P.constant; eof; return (DocStr (Right c)))
              <|> try (do cmd ["doc"]; n <- (P.fnName <|> (P.string "_|_" >> return falseTy)); eof; return (DocStr (Left n)))
              <|> try (do cmd ["d", "def"]; some (P.char ' ') ; n <- P.fnName; eof; return (Defn n))
              <|> try (do cmd ["total"]; do n <- P.fnName; eof; return (TotCheck n))
              <|> try (do cmd ["t", "type"]; do P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Check t))
              <|> try (do cmd ["u", "universes"]; eof; return Universes)
              <|> try (do cmd ["di", "dbginfo"]; n <- P.fnName; eof; return (DebugInfo n))
              <|> try (do cmd ["miss", "missing"]; n <- P.fnName; eof; return (Missing n))
              <|> try (do cmd ["dynamic"]; eof; return ListDynamic)
              <|> try (do cmd ["dynamic"]; l <- many anyChar; return (DynamicLink l))
              <|> try (do cmd ["color", "colour"]; pSetColourCmd)
              <|> try (do cmd ["set"]; o <- pOption; return (SetOpt o))
              <|> try (do cmd ["unset"]; o <- pOption; return (UnsetOpt o))
              <|> try (do cmd ["s", "search"]; P.whiteSpace; 
                          t <- P.typeExpr (defaultSyntax { implicitAllowed = True }); return (Search t))
              <|> try (do cmd ["cs", "casesplit"]; P.whiteSpace;
                          upd <- option False (do P.lchar '!'; return True)
                          l <- P.natural; n <- P.name;
                          return (CaseSplitAt upd (fromInteger l) n))
              <|> try (do cmd ["apc", "addproofclause"]; P.whiteSpace;
                          upd <- option False (do P.lchar '!'; return True)
                          l <- P.natural; n <- P.name;
                          return (AddProofClauseFrom upd (fromInteger l) n))
              <|> try (do cmd ["ac", "addclause"]; P.whiteSpace;
                          upd <- option False (do P.lchar '!'; return True)
                          l <- P.natural; n <- P.name;
                          return (AddClauseFrom upd (fromInteger l) n))
              <|> try (do cmd ["am", "addmissing"]; P.whiteSpace;
                          upd <- option False (do P.lchar '!'; return True)
                          l <- P.natural; n <- P.name;
                          return (AddMissing upd (fromInteger l) n))
              <|> try (do cmd ["mw", "makewith"]; P.whiteSpace;
                          upd <- option False (do P.lchar '!'; return True)
                          l <- P.natural; n <- P.name;
                          return (MakeWith upd (fromInteger l) n))
              <|> try (do cmd ["ml", "makelemma"]; P.whiteSpace;
                          upd <- option False (do P.lchar '!'; return True)
                          l <- P.natural; n <- P.name;
                          return (MakeLemma upd (fromInteger l) n))
              <|> try (do cmd ["ps", "proofsearch"]; P.whiteSpace;
                          upd <- option False (do P.lchar '!'; return True)
                          l <- P.natural; n <- P.name;
                          hints <- many P.fnName
                          return (DoProofSearch upd True (fromInteger l) n hints))
              <|> try (do cmd ["ref", "refine"]; P.whiteSpace;
                          upd <- option False (do P.lchar '!'; return True)
                          l <- P.natural; n <- P.name;
                          hint <- P.fnName
                          return (DoProofSearch upd False (fromInteger l) n [hint]))
              <|> try (do cmd ["p", "prove"]; n <- P.name; eof; return (Prove n))
              <|> try (do cmd ["m", "metavars"]; eof; return Metavars)
              <|> try (do cmd ["a", "addproof"]; do n <- option Nothing (do x <- P.name;
                                                                            return (Just x))
                                                    eof; return (AddProof n))
              <|> try (do cmd ["x"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (ExecVal t))
              <|> try (do cmd ["patt"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Pattelab t))
              <|> try (do cmd ["errorhandlers"]; eof ; return ListErrorHandlers)
              <|> try (do cmd ["consolewidth"]; w <- pConsoleWidth ; return (SetConsoleWidth w))
              <|> try (do cmd ["apropos"]; str <- many anyChar ; return (Apropos str))
              <|> try (do cmd ["wc", "whocalls"]; P.whiteSpace; n <- P.fnName ; return (WhoCalls n))
              <|> try (do cmd ["cw", "callswho"]; P.whiteSpace; n <- P.fnName ; return (CallsWho n))
              <|> try (do cmd ["mkdoc"]; str <- many anyChar; return (MakeDoc str))
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

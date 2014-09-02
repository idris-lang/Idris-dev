
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

parseCmd :: IState -> String -> String -> Result (Either String Command)
parseCmd i inputname = P.runparser pCmd i inputname

cmd :: [String] -> P.IdrisParser ()
cmd xs = try (do P.lchar ':'; docmd (sortBy (\x y -> compare (length y) (length x)) xs))
    where docmd [] = fail "No such command"
          docmd (x:xs) = try (discard (P.reserved x)) <|> docmd xs

pCmd :: P.IdrisParser (Either String Command)
pCmd = do P.whiteSpace; do cmd ["q", "quit"]; eof; return (Right Quit)
              <|> do cmd ["h", "?", "help"]; eof; return (Right Help)
              <|> do cmd ["w", "warranty"]; eof; return (Right Warranty)
              <|> do cmd ["r", "reload"]; eof; return (Right Reload)
              <|> do cmd ["module"]; f <- P.identifier; eof;
                          return (Right (ModImport (toPath f)))
              <|> do cmd ["e", "edit"]; eof; return (Right Edit)
              <|> do cmd ["exec", "execute"]; ((try $ eof >> return (Right Execute)) <|> return (Left "exec(ute) does not take any parameters"))
              <|> try (do cmd ["c", "compile"]
                          i <- get
                          f <- P.identifier
                          eof
                          return (Right (Compile (Via "c") f)))
              <|> do cmd ["c", "compile"]
                     i <- get
                     c <- codegenOption
                     f <- P.identifier
                     eof
                     return (Right (Compile c f))
              <|> do cmd ["proofs"]; eof; return (Right Proofs)
              <|> do cmd ["rmproof"]; n <- P.name; eof; return (Right (RmProof n))
              <|> do cmd ["showproof"]; n <- P.name; eof; return (Right (ShowProof n))
              <|> do cmd ["log"]; i <- P.natural; eof; return (Right (LogLvl (fromIntegral i)))
              <|> do cmd ["let"]
                     defn <- concat <$> many (P.decl defaultSyntax)
                     return (Right (NewDefn defn))
              <|> do cmd ["unlet","undefine"]
                     (Right . Undefine) `fmap` many P.name
              <|> do cmd ["lto", "loadto"];
                     toline <- P.natural
                     f <- many anyChar;
                     return (Right (Load f (Just (fromInteger toline))))
              <|> do cmd ["l", "load"]; f <- many anyChar;
                     return (Right (Load f Nothing))
              <|> do cmd ["cd"]; f <- many anyChar; return (Right (ChangeDirectory f))
              <|> do cmd ["spec"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Right (Spec t))
              <|> do cmd ["hnf"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Right (HNF t))
              <|> do cmd ["inline"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Right (TestInline t))
              <|> do c <- try (cmd ["doc"] *> P.constant); eof; return (Right (DocStr (Right c)))
              <|> do cmd ["doc"]; n <- (P.fnName <|> (P.string "_|_" >> return falseTy)); eof; return (Right (DocStr (Left n)))
              <|> do cmd ["d", "def"]; P.whiteSpace; n <- P.fnName; eof; return (Right (Defn n))
              <|> do cmd ["total"]; do n <- P.fnName; eof; return (Right (TotCheck n))
              <|> do cmd ["t", "type"]; do P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Right (Check t))
              <|> do cmd ["u", "universes"]; eof; return (Right Universes)
              <|> do cmd ["di", "dbginfo"]; n <- P.fnName; eof; return (Right (DebugInfo n))
              <|> do cmd ["miss", "missing"]; n <- P.fnName; eof; return (Right (Missing n))
              <|> try (do cmd ["dynamic"]; eof; return (Right ListDynamic))
              <|> do cmd ["dynamic"]; l <- many anyChar; return (Right (DynamicLink l))
              <|> do cmd ["color", "colour"]; pSetColourCmd >>= return . Right
              <|> do cmd ["set"]; o <- pOption; return (Right (SetOpt o))
              <|> do cmd ["unset"]; o <- pOption; return (Right (UnsetOpt o))
              <|> do cmd ["s", "search"]; P.whiteSpace;
                     t <- P.typeExpr (defaultSyntax { implicitAllowed = True }); return (Right (Search t))
              <|> do cmd ["cs", "casesplit"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (Right (CaseSplitAt upd (fromInteger l) n))
              <|> do cmd ["apc", "addproofclause"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (Right (AddProofClauseFrom upd (fromInteger l) n))
              <|> do cmd ["ac", "addclause"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (Right (AddClauseFrom upd (fromInteger l) n))
              <|> do cmd ["am", "addmissing"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (Right (AddMissing upd (fromInteger l) n))
              <|> do cmd ["mw", "makewith"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (Right (MakeWith upd (fromInteger l) n))
              <|> do cmd ["ml", "makelemma"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     return (Right (MakeLemma upd (fromInteger l) n))
              <|> do cmd ["ps", "proofsearch"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     hints <- many P.fnName
                     return (Right (DoProofSearch upd True (fromInteger l) n hints))
              <|> do cmd ["ref", "refine"]; P.whiteSpace;
                     upd <- option False (do P.lchar '!'; return True)
                     l <- P.natural; n <- P.name;
                     hint <- P.fnName
                     return (Right (DoProofSearch upd False (fromInteger l) n [hint]))
              <|> do cmd ["p", "prove"]; n <- P.name; eof; return (Right (Prove n))
              <|> do cmd ["m", "metavars"]; eof; return (Right Metavars)
              <|> do cmd ["a", "addproof"]; do n <- option Nothing (do x <- P.name;
                                                                       return (Just x))
                                               eof; return (Right (AddProof n))
              <|> do cmd ["x"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Right (ExecVal t))
              <|> do cmd ["patt"]; P.whiteSpace; t <- P.fullExpr defaultSyntax; return (Right (Pattelab t))
              <|> do cmd ["errorhandlers"]; eof ; return (Right ListErrorHandlers)
              <|> do cmd ["consolewidth"]; w <- pConsoleWidth ; return (Right (SetConsoleWidth w))
              <|> do cmd ["apropos"]; str <- many anyChar ; return (Right (Apropos str))
              <|> do cmd ["wc", "whocalls"]; P.whiteSpace; n <- P.fnName ; return (Right (WhoCalls n))
              <|> do cmd ["cw", "callswho"]; P.whiteSpace; n <- P.fnName ; return (Right (CallsWho n))
              <|> do cmd ["mkdoc"]; str <- many anyChar; return (Right (MakeDoc str))
              <|> do cmd ["printdef"]; P.whiteSpace; n <- P.fnName; return (Right (PrintDef n))
              <|> do cmd ["pp", "pprint"]
                     P.whiteSpace
                     fmt <- ppFormat
                     P.whiteSpace
                     n <- fmap fromInteger P.natural
                     P.whiteSpace
                     t <- P.fullExpr defaultSyntax
                     return (Right (PPrint fmt n t))
              <|> do P.whiteSpace; do eof; return (Right NOP)
                             <|> do t <- P.fullExpr defaultSyntax; return (Right (Eval t))

 where toPath n = foldl1' (</>) $ splitOn "." n

pOption :: P.IdrisParser Opt
pOption = do discard (P.symbol "errorcontext"); return ErrContext
      <|> do discard (P.symbol "showimplicits"); return ShowImpl
      <|> do discard (P.symbol "originalerrors"); return ShowOrigErr
      <|> do discard (P.symbol "autosolve"); return AutoSolve
      <|> do discard (P.symbol "nobanner") ; return NoBanner
      <|> do discard (P.symbol "warnreach"); return WarnReach

codegenOption :: P.IdrisParser Codegen
codegenOption = do discard (P.symbol "bytecode"); return Bytecode
            <|> do x <- P.identifier
                   return (Via (map toLower x))

pConsoleWidth :: P.IdrisParser ConsoleWidth
pConsoleWidth = do discard (P.symbol "auto"); return AutomaticWidth
            <|> do discard (P.symbol "infinite"); return InfinitelyWide
            <|> do n <- fmap fromInteger P.natural; return (ColsWide n)

ppFormat :: P.IdrisParser OutputFmt
ppFormat = (discard (P.symbol "html") >> return HTMLOutput)
       <|> (discard (P.symbol "latex") >> return LaTeXOutput)

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

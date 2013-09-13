module Idris.REPLParser(parseCmd) where

import System.FilePath ((</>))
import System.Console.ANSI (Color(..))

import Idris.Colours
import Idris.Parser
import Idris.AbsSyntax
import Core.TT

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Debug.Trace
import Data.List
import Data.List.Split(splitOn)
import Data.Char(toLower)

parseCmd i = runParser pCmd i "(input)"

cmd :: [String] -> IParser ()
cmd xs = do lchar ':'; docmd (sortBy (\x y -> compare (length y) (length x)) xs)
    where docmd [] = fail "No such command"
          docmd (x:xs) = try (discard (symbol x)) <|> docmd xs

pCmd :: IParser Command
pCmd = do spaces; try (do cmd ["q", "quit"]; eof; return Quit)
              <|> try (do cmd ["h", "?", "help"]; eof; return Help)
              <|> try (do cmd ["r", "reload"]; eof; return Reload)
              <|> try (do cmd ["m", "module"]; f <- identifier; eof;
                          return (ModImport (toPath f)))
              <|> try (do cmd ["e", "edit"]; eof; return Edit)
              <|> try (do cmd ["exec", "execute"]; eof; return Execute)
              <|> try (do cmd ["ttshell"]; eof; return TTShell)
              <|> try (do cmd ["c", "compile"]; f <- identifier; eof; return (Compile ViaC f))
              <|> try (do cmd ["jc", "newcompile"]; f <- identifier; eof; return (Compile ViaJava f))
              <|> try (do cmd ["js", "javascript"]; f <- identifier; eof; return (Compile ViaJavaScript f))
              <|> try (do cmd ["m", "metavars"]; eof; return Metavars)
              <|> try (do cmd ["proofs"]; eof; return Proofs)
              <|> try (do cmd ["p", "prove"]; n <- pName; eof; return (Prove n))
              <|> try (do cmd ["a", "addproof"]; do n <- option Nothing (do x <- pName;
                                                                            return (Just x))
                                                    eof; return (AddProof n))
              <|> try (do cmd ["rmproof"]; n <- pName; eof; return (RmProof n))
              <|> try (do cmd ["showproof"]; n <- pName; eof; return (ShowProof n))
              <|> try (do cmd ["log"]; i <- natural; eof; return (LogLvl (fromIntegral i)))
              <|> try (do cmd ["l", "load"]; f <- getInput; return (Load f))
              <|> try (do cmd ["cd"]; f <- getInput; return (ChangeDirectory f))
              <|> try (do cmd ["spec"]; whiteSpace; t <- pFullExpr defaultSyntax; return (Spec t))
              <|> try (do cmd ["hnf"]; whiteSpace; t <- pFullExpr defaultSyntax; return (HNF t))
              <|> try (do cmd ["doc"]; n <- pfName; eof; return (DocStr n))
              <|> try (do cmd ["d", "def"]; many1 (char ' ') ; n <- pfName; eof; return (Defn n))
              <|> try (do cmd ["total"]; do n <- pfName; eof; return (TotCheck n))
              <|> try (do cmd ["t", "type"]; do whiteSpace; t <- pFullExpr defaultSyntax; return (Check t))
              <|> try (do cmd ["u", "universes"]; eof; return Universes)
              <|> try (do cmd ["di", "dbginfo"]; n <- pfName; eof; return (DebugInfo n))
              <|> try (do cmd ["i", "info"]; n <- pfName; eof; return (Info n))
              <|> try (do cmd ["miss", "missing"]; n <- pfName; eof; return (Missing n))
              <|> try (do cmd ["dynamic"]; eof; return ListDynamic)
              <|> try (do cmd ["dynamic"]; l <- getInput; return (DynamicLink l))
              <|> try (do cmd ["color", "colour"]; pSetColourCmd)
              <|> try (do cmd ["set"]; o <-pOption; return (SetOpt o))
              <|> try (do cmd ["unset"]; o <-pOption; return (UnsetOpt o))
              <|> try (do cmd ["s", "search"]; whiteSpace; t <- pFullExpr defaultSyntax; return (Search t))
              <|> try (do cmd ["x"]; whiteSpace; t <- pFullExpr defaultSyntax; return (ExecVal t))
              <|> try (do cmd ["patt"]; whiteSpace; t <- pFullExpr defaultSyntax; return (Pattelab t))
              <|> do whiteSpace; do eof; return NOP
                             <|> do t <- pFullExpr defaultSyntax; return (Eval t)

 where toPath n = foldl1' (</>) $ splitOn "." n

pOption :: IParser Opt
pOption = do discard (symbol "errorcontext"); return ErrContext
      <|> do discard (symbol "showimplicits"); return ShowImpl


colours :: [(String, Color)]
colours = [ ("black", Black)
          , ("red", Red)
          , ("green", Green)
          , ("yellow", Yellow)
          , ("blue", Blue)
          , ("magenta", Magenta)
          , ("cyan", Cyan)
          , ("white", White)
          ]

pColour :: IParser Color
pColour = doColour colours
    where doColour [] = fail "Unknown colour"
          doColour ((s, c):cs) = (try (symbol s) >> return c) <|> doColour cs

pColourMod :: IParser (IdrisColour -> IdrisColour)
pColourMod = try (symbol "vivid" >> return doVivid)
         <|> try (symbol "dull" >> return doDull)
         <|> try (symbol "underline" >> return doUnderline)
         <|> try (symbol "nounderline" >> return doNoUnderline)
         <|> try (symbol "bold" >> return doBold)
         <|> try (symbol "nobold" >> return doNoBold)
         <|> try (pColour >>= return . doSetColour)
    where doVivid i       = i { vivid = True }
          doDull i        = i { vivid = False }
          doUnderline i   = i { underline = True }
          doNoUnderline i = i { underline = False }
          doBold i        = i { bold = True }
          doNoBold i      = i { bold = False }
          doSetColour c i = i { colour = c }


colourTypes :: [(String, ColourType)]
colourTypes = map (\x -> ((map toLower . reverse . drop 6 . reverse . show) x, x)) $
              enumFromTo minBound maxBound

pColourType :: IParser ColourType
pColourType = doColourType colourTypes
    where doColourType [] = fail $ "Unknown colour category. Options: " ++
                                   (concat . intersperse ", " . map fst) colourTypes
          doColourType ((s,ct):cts) = (try (symbol s) >> return ct) <|> doColourType cts

pSetColourCmd :: IParser Command
pSetColourCmd = (do c <- pColourType
                    let defaultColour = IdrisColour Black True False False
                    opts <- sepBy pColourMod spaces
                    let colour = foldr ($) defaultColour $ reverse opts
                    return $ SetColour c colour)
            <|> try (symbol "on" >> return ColourOn)
            <|> try (symbol "off" >> return ColourOff)

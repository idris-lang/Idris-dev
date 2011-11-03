module Idris.REPLParser(parseCmd) where

import Idris.Parser
import Idris.AbsSyntax
import Core.TT

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Debug.Trace
import Data.List

parseCmd i = runParser pCmd i "(input)"

cmd :: [String] -> IParser ()
cmd xs = do lchar ':'; docmd (sortBy (\x y -> compare (length y) (length x)) xs)
    where docmd [] = fail "No such command"
          docmd (x:xs) = try (discard (symbol x)) <|> docmd xs

pCmd :: IParser Command
pCmd = try (do cmd ["q", "quit"]; eof; return Quit)
   <|> try (do cmd ["h", "?", "help"]; eof; return Help)
   <|> try (do cmd ["r", "reload"]; eof; return Reload)
   <|> try (do cmd ["e", "edit"]; eof; return Edit)
   <|> try (do cmd ["ttshell"]; eof; return TTShell)
   <|> try (do cmd ["c", "compile"]; f <- identifier; eof; return (Compile f))
   <|> try (do cmd ["m", "metavars"]; eof; return Metavars)
   <|> try (do cmd ["p", "prove"]; n <- pName; eof; return (Prove n)) 
   <|> try (do cmd ["log"]; i <- natural; eof; return (LogLvl (fromIntegral i)))
   <|> try (do cmd ["spec"]; t <- pFullExpr defaultSyntax; return (Spec t))
   <|> try (do cmd ["hnf"]; t <- pFullExpr defaultSyntax; return (HNF t))
   <|> do t <- pFullExpr defaultSyntax; return (Eval t)
   <|> do eof; return NOP


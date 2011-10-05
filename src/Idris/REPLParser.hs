module Idris.REPLParser(parseCmd) where

import Idris.Parser
import Idris.AbsSyntax
import Core.TT

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Debug.Trace

parseCmd i = runParser pCmd i "(input)"

cmd :: [String] -> IParser ()
cmd xs = do lchar ':'; docmd xs
    where docmd [] = fail "No such command"
          docmd (x:xs) = try (discard (symbol x)) <|> docmd xs

pCmd :: IParser Command
pCmd = try (do cmd ["q", "quit"]; return Quit)
   <|> try (do cmd ["h", "?", "help"]; return Help)
   <|> do t <- pFullExpr; return (Eval t)
   <|> do eof; return NOP

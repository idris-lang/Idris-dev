module Idris.REPLParser(parseCmd) where

import Idris.Parser
import Idris.AbsSyntax
import Control.Monad

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Debug.Trace

parseCmd = parse pCmd "(input)"

cmd :: [String] -> Parser ()
cmd xs = do lchar ':'; docmd xs
    where docmd [] = fail "No such command"
          docmd (x:xs) = try (void (symbol x)) <|> docmd xs

pCmd :: Parser Command
pCmd = try (do cmd ["q", "quit"]; return Quit)
   <|> try (do cmd ["h", "?", "help"]; return Help)
   

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
   <|> try (do cmd ["exec", "execute"]; eof; return Execute)
   <|> try (do cmd ["ttshell"]; eof; return TTShell)
   <|> try (do cmd ["c", "compile"]; f <- identifier; eof; return (Compile f))
   <|> try (do cmd ["m", "metavars"]; eof; return Metavars)
   <|> try (do cmd ["p", "prove"]; n <- pName; eof; return (Prove n)) 
   <|> try (do cmd ["a", "addproof"]; eof; return AddProof)
   <|> try (do cmd ["log"]; i <- natural; eof; return (LogLvl (fromIntegral i)))
   <|> try (do cmd ["spec"]; t <- pFullExpr defaultSyntax; return (Spec t))
   <|> try (do cmd ["hnf"]; t <- pFullExpr defaultSyntax; return (HNF t))
   <|> try (do cmd ["d", "def"]; n <- pName; eof; return (Defn n))
   <|> try (do cmd ["total"]; do n <- pName; eof; return (TotCheck n))
   <|> try (do cmd ["t", "type"]; do t <- pFullExpr defaultSyntax; return (Check t))
   <|> try (do cmd ["u", "universes"]; eof; return Universes)
   <|> try (do cmd ["di", "dbginfo"]; n <- pfName; eof; return (DebugInfo n))
   <|> try (do cmd ["i", "info"]; n <- pfName; eof; return (Info n))
   <|> try (do cmd ["s", "search"]; t <- pFullExpr defaultSyntax; return (Search t))
   <|> try (do cmd ["x"]; t <- pFullExpr defaultSyntax; return (ExecVal t))
   <|> do t <- pFullExpr defaultSyntax; return (Eval t)
   <|> do eof; return NOP


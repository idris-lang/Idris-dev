{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module ShellParser(parseCommand, parseTactic) where

import Core
import Elaborate
import CoreParser

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Debug.Trace

type TokenParser a = PTok.TokenParser a

lexer :: TokenParser ()
lexer  = PTok.makeTokenParser haskellDef

whiteSpace= PTok.whiteSpace lexer
lexeme    = PTok.lexeme lexer
symbol    = PTok.symbol lexer
natural   = PTok.natural lexer
parens    = PTok.parens lexer
semi      = PTok.semi lexer
comma     = PTok.comma lexer
identifier= PTok.identifier lexer
reserved  = PTok.reserved lexer
operator  = PTok.operator lexer
reservedOp= PTok.reservedOp lexer
lchar = lexeme.char

parseCommand = parse pCommand "(input)"
parseTactic  = parse (pTactic >>= return . Tac) "(input)"

pCommand :: Parser Command
pCommand = do reserved "theorem"; n <- iName; lchar ':'; ty <- pTerm
              return (Theorem n ty)
       <|> do reserved "eval"; tm <- pTerm
              return (Eval tm)
       <|> do reserved "print"; n <- iName; return (Print n)
       <|> do reserved "quit";
              return Quit

pTactic :: Parser Elab
pTactic = do reserved "attack";  return attack
      <|> do reserved "claim";   n <- iName; lchar ':'; ty <- pTerm
             return (claim n ty)
      <|> do reserved "regret";  return regret
      <|> do reserved "fill";    tm <- pTerm; return (fill tm)
      <|> do reserved "unify";   tm <- pTerm; return (unify_fill tm)
      <|> do reserved "solve";   return solve
      <|> do reserved "compute"; return compute
      <|> do reserved "intro";   n <- iName; return (intro n)
      <|> do reserved "forall";  n <- iName; lchar ':'; ty <- pTerm
             return (forall n ty)
      <|> do reserved "eval";    t <- pTerm; return (eval_in t)
      <|> do reserved "check";   t <- pTerm; return (check_in t)
      <|> do reserved "focus";   n <- iName; return (focus n)
      <|> do reserved "state";   return proofstate
      <|> do reserved "qed";     return qed



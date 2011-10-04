module Idris.Parser where

import Idris.AbsSyntax

import Core.CoreParser
import Core.TT

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Debug.Trace

type TokenParser a = PTok.TokenParser a

idrisDef = haskellDef { 
              reservedOpNames = [":", "..", "=", "\\", "|", "<-", "->", "=>"],
              reservedNames = ["let", "in", "data", "Set", "if", "then", "else",
                               "do", "dsl", "import", "infix", "infixl", "infixr",
                               "where", "forall", "syntax",
                               "using", "params", "namespace"]
           } 

lexer :: TokenParser ()
lexer  = PTok.makeTokenParser idrisDef

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

parseExpr = parse pFullExpr "(input)"

pFullExpr = do x <- pExpr; eof; return x

pExpr' :: Parser PTerm
pExpr' = try pApp 
         <|> pSimpleExpr
         <|> try pLambda
         <|> try pPi 

pExpr = buildExpressionParser table pExpr'

pSimpleExpr = 
        try (do symbol "!["; t <- pTerm; lchar ']' 
                return $ PQuote t)
        <|> try (do x <- iName; return (PRef x))
        <|> try (do lchar '_'; return Placeholder)
        <|> try (do lchar '('; o <- operator; lchar ')'; return (PRef (UN [o]))) 
        <|> try (do lchar '('; e <- pExpr; lchar ')'; return e)

pApp = do f <- pSimpleExpr
          args <- many1 pSimpleExpr
          return (PApp f [] args)

pTSig = do lchar ':'
           pExpr

pLambda = do lchar '\\'; x <- iName; t <- option Placeholder pTSig
             symbol "=>"
             sc <- pExpr
             return (PLam x t sc)

pPi = do lchar '('; x <- iName; t <- pTSig; lchar ')'
         symbol "->"
         sc <- pExpr
         return (PPi Exp x t sc)
  <|> do lchar '{'; x <- iName; t <- pTSig; lchar '}'
         symbol "->"
         sc <- pExpr
         return (PPi Imp x t sc)

table = [[binary "="  (\x y -> PApp (PRef (UN ["="])) [] [x,y]) AssocLeft],
         [binary "->" (PPi Exp (MN 0 "X")) AssocRight]]

binary name f assoc = Infix (do { reservedOp name; return f }) assoc


module Idris.Parser where

import Idris.AbsSyntax

import Core.CoreParser
import Core.TT

import Text.ParserCombinators.Parsec
import Text.Parsec.Prim(Parsec)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Data.List
import Control.Monad.State
import Debug.Trace

type TokenParser a = PTok.TokenParser a

idrisDef = haskellDef { 
              reservedOpNames = [":", "..", "=", "\\", "|", "<-", "->", "=>"],
              reservedNames = ["let", "in", "data", "Set", "if", "then", "else",
                               "do", "dsl", "import", "infix", "infixl", "infixr",
                               "where", "forall", "syntax",
                               "using", "params", "namespace"]
           } 

type IParser = Parsec String IState

lexer :: TokenParser IState
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

parseExpr i = runParser pFullExpr i "(input)"

parseProg :: String -> Idris [PDecl]
parseProg fname = do file <- lift $ readFile fname
                     i <- get
                     case (runParser (do ps <- many1 pDecl
                                         i' <- getState
                                         return (ps, i')) i fname file) of
                        Left err -> fail (show err)
                        Right (x, i) -> do put i
                                           return x


pFullExpr = do x <- pExpr; eof; return x

pDecl :: IParser PDecl
pDecl = do d <- pDecl'; lchar ';'; return d

pDecl' :: IParser PDecl
pDecl' = try (do f <- fixity; i <- natural; ops <- sepBy1 operator (lchar ',')
                 let prec = fromInteger i
                 istate <- getState
                 let fs = map (Fix (f prec)) ops
                 setState (istate { 
                    idris_infixes = sort (fs ++ idris_infixes istate) })
                 return (PFix (f prec) ops))
     <|> try (do n <- iName; ty <- pTSig
                 return (PTy n ty))

fixity :: IParser (Int -> Fixity) 
fixity = try (do reserved "infixl"; return Infixl)
     <|> try (do reserved "infixr"; return Infixr)
     <|> try (do reserved "infix";  return InfixN)

pExpr = do i <- getState
           buildExpressionParser (table (idris_infixes i)) pExpr'

pExpr' :: IParser PTerm
pExpr' = try pApp 
     <|> pSimpleExpr
     <|> try pLambda
     <|> try pPi 

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

table fixes 
   = toTable (reverse fixes) ++
      [[binary "="  (\x y -> PApp (PRef (UN ["="])) [] [x,y]) AssocLeft],
       [binary "->" (PPi Exp (MN 0 "X")) AssocRight]]

toTable fs = map (map toBin) 
                 (groupBy (\ (Fix x _) (Fix y _) -> prec x == prec y) fs)
   where toBin (Fix f op) = binary op 
                               (\x y -> PApp (PRef (UN [op])) [] [x,y]) (assoc f)
         assoc (Infixl _) = AssocLeft
         assoc (Infixr _) = AssocRight
         assoc (InfixN _) = AssocNone

binary name f assoc = Infix (do { reservedOp name; return f }) assoc


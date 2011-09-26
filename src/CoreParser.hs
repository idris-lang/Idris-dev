{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module CoreParser(parseTerm, parseFile, parseDef, pTerm, iName) where

import Core

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

parseFile = parse pTestFile "(input)"
parseDef = parse pDef "(input)"
parseTerm = parse pTerm "(input)"

pTestFile :: Parser RProgram
pTestFile = many1 pDef

iName :: Parser Name
iName = identifier >>= (\n -> return (UN [n]))

pDef :: Parser (Name, RDef)
pDef = try (do x <- iName; lchar ':'; ty <- pTerm
               lchar '='
               tm <- pTerm
               lchar ';'
               return (x, RFunction (RawFun ty tm)))
       <|> do x <- iName; lchar ':'; ty <- pTerm; lchar ';'
              return (x, RConst ty)

app :: Parser (Raw -> Raw -> Raw)
app = do whiteSpace ; return RApp

arrow :: Parser (Raw -> Raw -> Raw)
arrow = do symbol "->" ; return $ \s t -> RBind (MN 0 "X") (Pi s) t

pTerm :: Parser Raw
pTerm = try (do chainl1 pNoApp app)
           <|> pNoApp

pNoApp :: Parser Raw
pNoApp = try (chainr1 pExp arrow)
           <|> pExp

pExp :: Parser Raw
pExp = do lchar '\\'; x <- iName; lchar ':'; ty <- pTerm
          symbol "=>";
          sc <- pTerm
          return (RBind x (Lam ty) sc)
       <|> try (do lchar '?'; x <- iName; lchar ':'; ty <- pTerm
                   lchar '.';
                   sc <- pTerm
                   return (RBind x (Lam ty) sc))
       <|> try (do lchar '('; 
                   x <- iName; lchar ':'; ty <- pTerm
                   lchar ')';
                   symbol "->";
                   sc <- pTerm
                   return (RBind x (Pi ty) sc))
       <|> try (do lchar '('; 
                   t <- pTerm
                   lchar ')'
                   return t)
       <|> try (do lchar '?';
                   x <- iName; lchar ':'; ty <- pTerm
                   lchar '.';
                   sc <- pTerm
                   return (RBind x (Hole ty) sc))
       <|> try (do symbol "??";
                   x <- iName; lchar ':'; ty <- pTerm
                   lchar '=';
                   val <- pTerm
                   sc <- pTerm
                   return (RBind x (Guess ty val) sc))
       <|> try (do reserved "let"; 
                   x <- iName; lchar ':'; ty <- pTerm
                   lchar '=';
                   val <- pTerm
                   reserved "in";
                   sc <- pTerm
                   return (RBind x (Let ty val) sc))
--        <|> try (do reserved "nlet"; 
--                    x <- iName; lchar ':'; ty <- pTerm
--                    lchar '=';
--                    val <- pTerm
--                    reserved "in";
--                    sc <- pTerm
--                    return (RBind x (NLet ty val) sc))
       <|> try (do lchar '_'; 
                   x <- iName; lchar ':'; ty <- pTerm
                   lchar '.';
                   sc <- pTerm
                   return (RBind x (PVar ty) sc))
       <|> try (do reserved "Set"; i <- natural
                   return (RSet (fromInteger i)))
       <|> try (do x <- iName
                   return (Var x))


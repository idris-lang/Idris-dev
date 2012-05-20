module RTS.BCParser where

import Core.CoreParser
import Core.TT

import RTS.Bytecode

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

import Data.List
import Control.Monad.State
import Debug.Trace
import Data.Maybe
import System.FilePath

type TokenParser a = PTok.TokenParser a

type BParser = GenParser Char ()

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
integer   = PTok.integer lexer
float     = PTok.float lexer
strlit    = PTok.stringLiteral lexer
chlit     = PTok.charLiteral lexer
lchar = lexeme.char

parseFile :: FilePath -> IO BCProg
parseFile fname = do fp <- readFile fname
                     case runParser pProgram () fname fp of
                        Left err-> fail (show err)
                        Right x -> return x

pProgram :: BParser BCProg
pProgram = do fs <- many1 pFun
              return $ BCProg fs

pFun :: BParser (Name, Bytecode)
pFun = do n <- iName []
          lchar ':'
          bc <- many1 pInstruction
          return (n, bc)

pInstruction :: BParser BCOp
pInstruction =
        try (do reserved "PUSH"; v <- pValue; return (PUSH v))
    <|> try (do reserved "SLIDE"; v <- integer; return (SLIDE (fromInteger v)))
    <|> try (do reserved "DISCARD"; v <- integer; return (DISCARD (fromInteger v)))
    <|> try (do reserved "DISCARDINT"; v <- integer
                return (DISCARDINT (fromInteger v)))
    <|> try (do reserved "DISCARDFLOAT"; v <- integer
                return (DISCARDFLOAT (fromInteger v)))
    <|> try (do reserved "EVAL"; return (EVAL True))
    <|> try (do reserved "EVAL_NOUPDATE"; return (EVAL False))
    <|> try (do reserved "MKCON"; t <- integer; a <- integer;
                return (MKCON (fromInteger t) (fromInteger a)))
    <|> try (do reserved "MKTHUNK"; n <- iName []; arg <- integer; arity <- integer
                return (MKTHUNK n (fromInteger arg) (fromInteger arity)))
    <|> try (do reserved "MKUNIT"; return MKUNIT)
    <|> try (do reserved "CALL"; n <- iName []; i <- integer;
                return (CALL n (fromInteger i)))
    <|> try (do reserved "ERROR"; s <- strlit; return (ERROR s))
    <|> try (do reserved "SPLIT"; return SPLIT)
    <|> try (do reserved "DUMP"; return DUMP)
    <|> do reserved "CASE"; s <- sepBy1 pAlt (lchar '|')
           def <- option Nothing (do reserved "default"; symbol "->";
                                     bc <- many1 pInstruction
                                     return (Just bc))
           return (CASE s def)
  where pAlt = try (do t <- integer; symbol "->"
                       bc <- many1 pInstruction
                       return (fromInteger t, bc))

pValue :: BParser Value
pValue = try (do x <- integer; lchar 'L'; return (VBigInt x))
     <|> try (do x <- integer; return (VInt (fromInteger x)))
     <|> try (do x <- float; return (VFloat x))
     <|> try (do x <- strlit; return (VString x))
     <|> try (do x <- chlit; return (VChar x))
     <|> try (do lchar 'S'; x <- integer; return (VRef (fromInteger x)))

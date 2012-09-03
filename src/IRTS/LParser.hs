module IRTS.LParser where

import Core.CoreParser
import Core.TT
import IRTS.Lang
import IRTS.Simplified
import IRTS.Bytecode
import IRTS.CodegenC
import Paths_idris

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

type LParser = GenParser Char ()

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

fovm :: FilePath -> IO ()
fovm f = do defs <- parseFOVM f
            codegenC defs "a.out" True [] "" DEBUG

parseFOVM :: FilePath -> IO [(Name, LDecl)]
parseFOVM fname = do -- putStrLn $ "Reading " ++ fname
                     fp <- readFile fname
                     case runParser pProgram () fname fp of
                        Left err-> fail (show err)
                        Right x -> return x

pProgram :: LParser [(Name, LDecl)]
pProgram = do fs <- many1 pLDecl
              eof
              return fs 

pLDecl :: LParser (Name, LDecl)
pLDecl = do reserved "data"
            n <- iName []
            ar <- natural
            return (n, LConstructor n (-1) (fromInteger ar))
     <|> do reserved "fun"
            n <- iName []
            lchar '('
            args <- sepBy (iName []) (lchar ',')
            lchar ')'
            lchar '='
            def <- pLExp
            return (n, LFun n args def)

pLExp = buildExpressionParser optable pLExp' 

optable = [[binary "*" (\x y -> LOp LTimes [x,y]) AssocLeft,
            binary "/" (\x y -> LOp LDiv [x,y]) AssocLeft,
            binary "*." (\x y -> LOp LFTimes [x,y]) AssocLeft,
            binary "/." (\x y -> LOp LFTimes [x,y]) AssocLeft
            ],
           [
            binary "+" (\x y -> LOp LPlus [x,y]) AssocLeft,
            binary "-" (\x y -> LOp LMinus [x,y]) AssocLeft,
            binary "++" (\x y -> LOp LStrConcat [x,y]) AssocLeft,
            binary "+." (\x y -> LOp LFPlus [x,y]) AssocLeft,
            binary "-." (\x y -> LOp LFMinus [x,y]) AssocLeft
            ],
           [
            binary "==" (\x y -> LOp LEq [x, y]) AssocNone,
            binary "==." (\x y -> LOp LFEq [x, y]) AssocNone,
            binary "<" (\x y -> LOp LLt [x, y]) AssocNone,
            binary "<." (\x y -> LOp LFLt [x, y]) AssocNone,
            binary ">" (\x y -> LOp LGt [x, y]) AssocNone,
            binary ">." (\x y -> LOp LFGt [x, y]) AssocNone,
            binary "<=" (\x y -> LOp LLe [x, y]) AssocNone,
            binary "<=." (\x y -> LOp LFLe [x, y]) AssocNone,
            binary ">=" (\x y -> LOp LGe [x, y]) AssocNone,
            binary ">=." (\x y -> LOp LFGe [x, y]) AssocNone
          ]]

binary name f assoc = Infix (do reservedOp name; return f) assoc

pLExp' :: LParser LExp
pLExp' = try (do lchar '%'; pCast)
     <|> try (do lchar '%'; pPrim)
     <|> try (do tc <- option False (do lchar '%'; reserved "tc"; return True)
                 x <- iName [];
                 lchar '('
                 args <- sepBy pLExp (lchar ',')
                 lchar ')'
                 if null args then return (LV (Glob x)) else return (LApp tc x args))
     <|> do lchar '('; e <- pLExp; lchar ')'; return e
     <|> pLConst
     <|> do reserved "let"; x <- iName []; lchar '='; v <- pLExp
            reserved "in"; e <- pLExp
            return (LLet x v e)
     <|> do reserved "foreign"; l <- pLang; t <- pType
            fname <- strlit
            lchar '('
            fargs <- sepBy (do t' <- pType; e <- pLExp; return (t', e)) (lchar ',')
            lchar ')'
            return (LForeign l t fname fargs)
     <|> pCase
     <|> do x <- iName []
            return (LV (Glob x))
     
pLang = do reserved "C"; return LANG_C

pType = do reserved "Int"; return FInt
    <|> do reserved "Float"; return FDouble
    <|> do reserved "String"; return FString
    <|> do reserved "Unit"; return FUnit
    <|> do reserved "Ptr"; return FPtr
    <|> do reserved "Any"; return FAny

pCase :: LParser LExp
pCase = do reserved "case"; e <- pLExp; reserved "of"
           lchar '{'
           alts <- sepBy1 pAlt (lchar '|')
           lchar '}'
           return (LCase e alts)

pCast :: LParser LExp
pCast = do reserved "FloatString"; e <- pLExp; return (LOp LFloatStr [e])
    <|> do reserved "StringFloat"; e <- pLExp; return (LOp LStrFloat [e])
    <|> do reserved "FloatInt"; e <- pLExp; return (LOp LFloatInt [e])
    <|> do reserved "IntFloat"; e <- pLExp; return (LOp LIntFloat [e])
    <|> do reserved "StringInt"; e <- pLExp; return (LOp LStrInt [e])
    <|> do reserved "IntString"; e <- pLExp; return (LOp LIntStr [e])

pPrim :: LParser LExp
pPrim = do reserved "StrEq"; e <- pLExp; e' <- pLExp; return (LOp LStrEq [e, e'])
    <|> do reserved "StrLt"; e <- pLExp; e' <- pLExp; return (LOp LStrLt [e, e'])
    <|> do reserved "StrLen"; e <- pLExp; return (LOp LStrLen [e])
    <|> do reserved "ReadString"; return (LOp LReadStr [])
    <|> do reserved "WriteString"; e <- pLExp; return (LOp LPrintStr [e])
    <|> do reserved "WriteInt"; e <- pLExp; return (LOp LPrintNum [e])

pAlt :: LParser LAlt
pAlt = try (do x <- iName []
               lchar '('; args <- sepBy1 (iName []) (lchar ','); lchar ')'
               symbol "=>"
               rhs <- pLExp
               return (LConCase (-1) x args rhs))
    <|> do x <- iName [];
           symbol "=>"
           rhs <- pLExp
           return (LConCase (-1) x [] rhs)
    <|> do c <- natural
           symbol "=>"
           rhs <- pLExp
           return (LConstCase (I (fromInteger c)) rhs)
    <|> do symbol "_"
           symbol "=>"
           rhs <- pLExp
           return (LDefaultCase rhs)


pLConst :: LParser LExp
pLConst = try (do f <- float; return $ LConst (Fl f))
      <|> try (do i <- natural; return $ LConst (I (fromInteger i)))     
      <|> try (do s <- strlit; return $ LConst (Str s))
      <|> try (do c <- chlit; return $ LConst (Ch c))


module IRTS.LParser where

import Core.CoreParser
import Core.TT
import IRTS.Lang
import IRTS.Simplified
import IRTS.Bytecode
import IRTS.CodegenC
import IRTS.Defunctionalise
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
            let (nexttag, tagged) = addTags 0 (liftAll defs)
            let ctxtIn = addAlist tagged emptyContext
            let defuns = defunctionalise nexttag ctxtIn
--             print defuns
            let checked = checkDefs defuns (toAlist defuns)
--            print checked
            case checked of
                 OK c -> codegenC c "a.out" True ["math.h"] "" TRACE
                 Error e -> fail $ show e 

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
            binary "/." (\x y -> LOp LFDiv [x,y]) AssocLeft,
            binary "*:" (\x y -> LOp LBTimes [x,y]) AssocLeft,
            binary "/:" (\x y -> LOp LBDiv [x,y]) AssocLeft
            ],
           [
            binary "+" (\x y -> LOp LPlus [x,y]) AssocLeft,
            binary "-" (\x y -> LOp LMinus [x,y]) AssocLeft,
            binary "++" (\x y -> LOp LStrConcat [x,y]) AssocLeft,
            binary "+." (\x y -> LOp LFPlus [x,y]) AssocLeft,
            binary "-." (\x y -> LOp LFMinus [x,y]) AssocLeft,
            binary "+:" (\x y -> LOp LBPlus [x,y]) AssocLeft,
            binary "-:" (\x y -> LOp LBMinus [x,y]) AssocLeft
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
            binary ">=." (\x y -> LOp LFGe [x, y]) AssocNone,

            binary "==:" (\x y -> LOp LBEq [x, y]) AssocNone,
            binary "<:" (\x y -> LOp LBLt [x, y]) AssocNone,
            binary ">:" (\x y -> LOp LBGt [x, y]) AssocNone,
            binary "<=:" (\x y -> LOp LBLe [x, y]) AssocNone,
            binary ">=:" (\x y -> LOp LBGe [x, y]) AssocNone
          ]]

binary name f assoc = Infix (do reservedOp name; return f) assoc

pLExp' :: LParser LExp
pLExp' = try (do lchar '%'; pCast)
     <|> try (do lchar '%'; pPrim)
     <|> try (do tc <- option False (do lchar '%'; reserved "tc"; return True)
                 x <- iName [];
                 lazy <- option False (do lchar '@'; return True)
                 lchar '('
                 args <- sepBy pLExp (lchar ',')
                 lchar ')'
                 if null args 
                    then if lazy then return (LLazyApp x [])
                                 else return (LV (Glob x)) 
                    else if lazy then return (LLazyApp x args)
                                 else return (LApp tc x args))
     <|> do lchar '('; e <- pLExp; lchar ')'; return e
     <|> pLConst
     <|> do reserved "let"; x <- iName []; lchar '='; v <- pLExp
            reserved "in"; e <- pLExp
            return (LLet x v e)
     <|> do lchar '\\'; xs <- sepBy (iName []) (lchar ',')
            symbol "=>"
            e <- pLExp
            return (LLam xs e)
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
pCast = do reserved "FloatString"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LFloatStr [e])
    <|> do reserved "StringFloat"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LStrFloat [e])
    <|> do reserved "FloatInt"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LFloatInt [e])
    <|> do reserved "IntFloat"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LIntFloat [e])
    <|> do reserved "StringInt"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LStrInt [e])
    <|> do reserved "IntString"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LIntStr [e])
    <|> do reserved "BigInt"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LBigInt [e])
    <|> do reserved "IntBig"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LIntBig [e])
    <|> do reserved "BigString"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LBigStr [e])
    <|> do reserved "StringBig"; lchar '('; e <- pLExp; lchar ')'
           return (LOp LStrBig [e])

pPrim :: LParser LExp
pPrim = do reserved "StrEq"; lchar '(';
           e <- pLExp; lchar ',';
           e' <- pLExp; lchar ')'; 
           return (LOp LStrEq [e, e'])
    <|> do reserved "StrLt"; lchar '('
           e <- pLExp; lchar ','; e' <- pLExp; 
           lchar ')'
           return (LOp LStrLt [e, e'])
    <|> do reserved "StrLen"; lchar '('; e <- pLExp; lchar ')';
           return (LOp LStrLen [e])
    <|> do reserved "ReadString"; lchar '('; e <- pLExp; lchar ')';
           return (LOp LReadStr [e])
    <|> do reserved "WriteString"; lchar '(';
           e <- pLExp; lchar ')'
           return (LOp LPrintStr [e])
    <|> do reserved "WriteInt"; lchar '('; 
           e <- pLExp; lchar ')';
           return (LOp LPrintNum [e])
    <|> do reserved "lazy"; lchar '(';
           e <- pLExp; lchar ')';
           return (LLazyExp e)
    <|> do reserved "StrHead"; lchar '('; e <- pLExp; lchar ')';
           return (LOp LStrHead [e])
    <|> do reserved "StrTail"; lchar '('; e <- pLExp; lchar ')';
           return (LOp LStrTail [e])
    <|> do reserved "StrRev"; lchar '('; e <- pLExp; lchar ')';
           return (LOp LStrRev [e])
    <|> do reserved "StrCons"; lchar '('; x <- pLExp; lchar ','; 
           xs <- pLExp; lchar ')';
           return (LOp LStrCons [x, xs])
    <|> do reserved "StrIndex"; lchar '('; x <- pLExp; lchar ','; 
           i <- pLExp; lchar ')';
           return (LOp LStrIndex [x, i])

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
      <|> try (do i <- natural; lchar ':'; return $ LConst (BI i))     
      <|> try (do i <- natural; return $ LConst (I (fromInteger i)))     
      <|> try (do s <- strlit; return $ LConst (Str s))
      <|> try (do c <- chlit; return $ LConst (Ch c))


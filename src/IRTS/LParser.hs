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
            let tagged = addTags defs
            let ctxtIn = addAlist tagged emptyContext
            let checked = checkDefs ctxtIn tagged 
            -- print checked
            case checked of
                   OK c -> do let bc = map toBC c
                              -- print bc
                              let h = concatMap toDecl (map fst bc)
                              let cc = concatMap (uncurry toC) bc
                              putStrLn h
                              putStrLn cc
                              d <- getDataDir
                              mprog <- readFile (d ++ "/rts/idris_main.c")
                              putStrLn mprog

parseFOVM :: FilePath -> IO [(Name, LDecl)]
parseFOVM fname = do putStrLn $ "Reading " ++ fname
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
            binary "/" (\x y -> LOp LDiv [x,y]) AssocLeft],
           [binary "+" (\x y -> LOp LPlus [x,y]) AssocLeft,
            binary "-" (\x y -> LOp LMinus [x,y]) AssocLeft],
           [binary "==" (\x y -> LOp LEq [x, y]) AssocNone]]

binary name f assoc = Infix (do reservedOp name; return f) assoc

pLExp' :: LParser LExp
pLExp' = try (do reserved "printNum"; e <- pLExp
                 return (LOp LPrintNum [e]))
     <|> try (do reserved "print"; e <- pLExp
                 return (LOp LPrintStr [e]))
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
     <|> pCase
     <|> do x <- iName []
            return (LV (Glob x))
     
pCase :: LParser LExp
pCase = do reserved "case"; e <- pLExp; reserved "of"
           lchar '{'
           alts <- sepBy1 pAlt (lchar '|')
           lchar '}'
           return (LCase e alts)

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


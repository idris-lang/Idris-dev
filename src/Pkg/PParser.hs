module Pkg.PParser where

import Core.CoreParser
import Core.TT
import Idris.REPL
import Idris.AbsSyntaxTree

import Paths_idris

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as PTok

type TokenParser a = PTok.TokenParser a

type PParser = GenParser Char PkgDesc

lexer :: TokenParser PkgDesc
lexer  = idrisLexer

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

data PkgDesc = PkgDesc { pkgname :: String,
                         libdeps :: [String],
                         objs :: [String],
                         makefile :: Maybe String,
                         idris_opts :: [Opt],
                         sourcedir :: String,
                         modules :: [Name],
                         idris_main :: Name,
                         execout :: Maybe String
                       }
    deriving Show

defaultPkg = PkgDesc "" [] [] Nothing [] "" [] (UN "") Nothing

parseDesc :: FilePath -> IO PkgDesc
parseDesc fp = do p <- readFile fp
                  case runParser pPkg defaultPkg fp p of
                       Left err -> fail (show err)
                       Right x -> return x

pPkg :: PParser PkgDesc
pPkg = do reserved "package"; p <- identifier 
          st <- getState
          setState (st { pkgname = p })
          many1 pClause 
          st <- getState
          return st

pClause :: PParser ()
pClause = do reserved "executable"; lchar '=';
             exec <- iModuleName []
             st <- getState
             setState (st { execout = Just (show exec) })
      <|> do reserved "main"; lchar '=';
             main <- iModuleName []
             st <- getState
             setState (st { idris_main = main })
      <|> do reserved "sourcedir"; lchar '=';
             src <- identifier
             st <- getState
             setState (st { sourcedir = src })
      <|> do reserved "opts"; lchar '=';
             opts <- strlit
             st <- getState
             let args = parseArgs (words opts)
             setState (st { idris_opts = args })
      <|> do reserved "modules"; lchar '=';
             ms <- sepBy1 (iModuleName []) (lchar ',')
             st <- getState
             setState (st { modules = modules st ++ ms })
      <|> do reserved "libs"; lchar '=';
             ls <- sepBy1 identifier (lchar ',')
             st <- getState
             setState (st { libdeps = libdeps st ++ ls })
      <|> do reserved "objs"; lchar '=';
             ls <- sepBy1 identifier (lchar ',')
             st <- getState
             setState (st { objs = libdeps st ++ ls })
      <|> do reserved "makefile"; lchar '=';
             mk <- iName []
             st <- getState
             setState (st { makefile = Just (show mk) })
  

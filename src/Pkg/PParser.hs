{-# LANGUAGE OverlappingInstances #-}

module Pkg.PParser where

import Text.Trifecta hiding (span, stringLiteral, charLiteral, natural, symbol, char, string, whiteSpace)

import Idris.Core.TT
import Idris.REPL
import Idris.AbsSyntaxTree
import Idris.ParseHelpers
import Idris.CmdOptions

import Control.Monad.State.Strict
import Control.Applicative
import qualified System.IO.UTF8 as UTF8

type PParser = StateT PkgDesc IdrisInnerParser

data PkgDesc = PkgDesc { pkgname :: String,
                         libdeps :: [String],
                         objs :: [String],
                         makefile :: Maybe String,
                         idris_opts :: [Opt],
                         sourcedir :: String,
                         modules :: [Name],
                         idris_main :: Name,
                         execout :: Maybe String,
                         idris_tests :: [Name]
                       }
    deriving Show

instance TokenParsing PParser where
  someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()


defaultPkg = PkgDesc "" [] [] Nothing [] "" [] (sUN "") Nothing []

parseDesc :: FilePath -> IO PkgDesc
parseDesc fp = do p <- UTF8.readFile fp
                  case runparser pPkg defaultPkg fp p of
                       Failure err -> fail (show err)
                       Success x -> return x

pPkg :: PParser PkgDesc
pPkg = do reserved "package"; p <- identifier
          st <- get
          put (st { pkgname = p })
          some pClause
          st <- get
          eof
          return st

pClause :: PParser ()
pClause = do reserved "executable"; lchar '=';
             exec <- iName []
             st <- get
             put (st { execout = Just (show exec) })
      <|> do reserved "main"; lchar '=';
             main <- iName []
             st <- get
             put (st { idris_main = main })
      <|> do reserved "sourcedir"; lchar '=';
             src <- identifier
             st <- get
             put (st { sourcedir = src })
      <|> do reserved "opts"; lchar '=';
             opts <- stringLiteral
             st <- get
             let args = pureArgParser (words opts)
             put (st { idris_opts = args })
      <|> do reserved "modules"; lchar '=';
             ms <- sepBy1 (iName []) (lchar ',')
             st <- get
             put (st { modules = modules st ++ ms })
      <|> do reserved "libs"; lchar '=';
             ls <- sepBy1 identifier (lchar ',')
             st <- get
             put (st { libdeps = libdeps st ++ ls })
      <|> do reserved "objs"; lchar '=';
             ls <- sepBy1 identifier (lchar ',')
             st <- get
             put (st { objs = libdeps st ++ ls })
      <|> do reserved "makefile"; lchar '=';
             mk <- iName []
             st <- get
             put (st { makefile = Just (show mk) })
      <|> do reserved "tests"; lchar '=';
             ts <- sepBy1 (iName []) (lchar ',')
             st <- get
             put st { idris_tests = idris_tests st ++ ts }


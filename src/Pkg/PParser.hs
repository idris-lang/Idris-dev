module Pkg.PParser where

import Text.Trifecta hiding (span, stringLiteral, charLiteral, natural, symbol, char, string, whiteSpace)

import Idris.Core.TT
import Idris.REPL
import Idris.AbsSyntaxTree
import Idris.ParseHelpers

import Paths_idris

import Control.Monad.State.Strict
import Control.Applicative


type PParser = StateT PkgDesc IdrisInnerParser

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

defaultPkg = PkgDesc "" [] [] Nothing [] "" [] (sUN "") Nothing

parseDesc :: FilePath -> IO PkgDesc
parseDesc fp = do p <- readFile fp
                  case runparser pPkg defaultPkg fp p of
                       Failure err -> fail (show err)
                       Success x -> return x

pPkg :: PParser PkgDesc
pPkg = do reserved "package"; p <- identifier
          st <- get
          put (st { pkgname = p })
          some pClause
          st <- get
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
             let args = parseArgs (words opts)
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


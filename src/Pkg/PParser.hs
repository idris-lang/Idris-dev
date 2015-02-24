{-# LANGUAGE CPP #-}
#if !(MIN_VERSION_base(4,8,0))
{-# LANGUAGE OverlappingInstances #-}
#endif

module Pkg.PParser where

import Text.Trifecta hiding (span, stringLiteral, charLiteral, natural, symbol, char, string, whiteSpace)

import Idris.Core.TT
import Idris.REPL
import Idris.AbsSyntaxTree
import Idris.ParseHelpers
import Idris.CmdOptions

import Control.Monad.State.Strict
import Control.Applicative

import System.Info (os)


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

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPING #-} TokenParsing PParser where
#else
instance TokenParsing PParser where
#endif
  someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()


defaultPkg = PkgDesc "" [] [] Nothing [] "" [] (sUN "") Nothing []

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
          eof
          return st

pClause :: PParser ()
pClause = do reserved "executable"; lchar '=';
             exec <- iName []
             st <- get
             put (st { execout = Just (if os `elem` ["win32", "mingw32", "cygwin32"] 
                                          then ((show exec) ++ ".exe")
                                          else ( show exec )
                                      ) })
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


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

import Util.System

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

someSpace :: IdrisParser ()
someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()

defaultPkg :: PkgDesc
defaultPkg = PkgDesc "" [] [] Nothing [] "" [] (sUN "") Nothing []

parseDesc :: FilePath -> IO PkgDesc
parseDesc fp = do p <- readFile fp
                  case runparser pPkg idrisInit fp p of
                       Failure err -> fail (show err)
                       Success x -> return x

pPkg :: IdrisParser PkgDesc
pPkg = do reserved "package"; p <- identifier
          changes <- foldr (.) id <$> some pClause
          eof
          return $ changes defaultPkg{ pkgname = p }

pClause :: IdrisParser (PkgDesc -> PkgDesc)
pClause = do reserved "executable"; lchar '=';
             exec <- iName []
             return $ \st -> st { execout = Just (if isWindows
                                          then ((show exec) ++ ".exe")
                                          else ( show exec )
                                      ) }
      <|> do reserved "main"; lchar '=';
             main <- iName []
             return $ \st -> st { idris_main = main }
      <|> do reserved "sourcedir"; lchar '=';
             src <- identifier
             return $ \st-> st { sourcedir = src }
      <|> do reserved "opts"; lchar '=';
             opts <- stringLiteral
             let args = pureArgParser (words opts)
             return $ \st -> st { idris_opts = args }
      <|> do reserved "modules"; lchar '=';
             ms <- sepBy1 (iName []) (lchar ',')
             return $ \st -> st { modules = modules st ++ ms }
      <|> do reserved "libs"; lchar '=';
             ls <- sepBy1 identifier (lchar ',')
             return $ \st -> st { libdeps = libdeps st ++ ls }
      <|> do reserved "objs"; lchar '=';
             ls <- sepBy1 identifier (lchar ',')
             return $ \st -> st { objs = libdeps st ++ ls }
      <|> do reserved "makefile"; lchar '=';
             mk <- iName []
             return $ \st -> st { makefile = Just (show mk) }
      <|> do reserved "tests"; lchar '=';
             ts <- sepBy1 (iName []) (lchar ',')
             return $ \st -> st { idris_tests = idris_tests st ++ ts }


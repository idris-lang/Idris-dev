{-|
Module      : Idris.Package.Parser
Description : `iPKG` file parser and package description information.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP, ConstraintKinds #-}
#if !(MIN_VERSION_base(4,8,0))
{-# LANGUAGE OverlappingInstances #-}
#endif
module Idris.Package.Parser where

import Idris.AbsSyntaxTree
import Idris.CmdOptions
import Idris.Core.TT
import Idris.Package.Common
import Idris.Parser.Helpers hiding (stringLiteral)
import Idris.REPL

import Util.System

import Control.Applicative
import Control.Monad.State.Strict
import Data.List (union)
import Data.Maybe (fromJust, isNothing)
import System.FilePath (isValid, takeFileName)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Text.Trifecta hiding (char, charLiteral, natural, span, string, symbol,
                      whiteSpace)

type PParser = StateT PkgDesc IdrisInnerParser

instance HasLastTokenSpan PParser where
  getLastTokenSpan = return Nothing

#if MIN_VERSION_base(4,9,0)
instance {-# OVERLAPPING #-} DeltaParsing PParser where
  line = lift line
  {-# INLINE line #-}
  position = lift position
  {-# INLINE position #-}
  slicedWith f (StateT m) = StateT $ \s -> slicedWith (\(a,s') b -> (f a b, s')) $ m s
  {-# INLINE slicedWith #-}
  rend = lift rend
  {-# INLINE rend #-}
  restOfLine = lift restOfLine
  {-# INLINE restOfLine #-}
#endif

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPING #-} TokenParsing PParser where
#else
instance TokenParsing PParser where
#endif
  someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()


parseDesc :: FilePath -> IO PkgDesc
parseDesc fp = do
    p <- readFile fp
    case runparser pPkg defaultPkg fp p of
      Failure (ErrInfo err _) -> fail (show $ PP.plain err)
      Success x -> return x

pPkg :: PParser PkgDesc
pPkg = do
    reserved "package"
    p <- filename
    st <- get
    put (st { pkgname = p })
    some pClause
    st <- get
    eof
    return st


-- | Parses a filename.
-- |
-- | Treated for now as an identifier or a double-quoted string.
filename :: (MonadicParsing m, HasLastTokenSpan m) => m String
filename = (do
    filename <- token $
        -- Treat a double-quoted string as a filename to support spaces.
        -- This also moves away from tying filenames to identifiers, so
        -- it will also accept hyphens
        -- (https://github.com/idris-lang/Idris-dev/issues/2721)
        stringLiteral
        <|>
        -- Through at least version 0.9.19.1, IPKG executable values were
        -- possibly namespaced identifiers, like foo.bar.baz.
        show <$> fst <$> iName []
    case filenameErrorMessage filename of
      Just errorMessage -> fail errorMessage
      Nothing -> return filename)
    <?> "filename"
    where
        -- TODO: Report failing span better! We could lookAhead,
        -- or do something with DeltaParsing?
        filenameErrorMessage :: FilePath -> Maybe String
        filenameErrorMessage path = either Just (const Nothing) $ do
            checkEmpty path
            checkValid path
            checkNoDirectoryComponent path
            where
                checkThat ok message =
                    if ok then Right () else Left message

                checkEmpty path =
                    checkThat (path /= "") "filename must not be empty"

                checkValid path =
                    checkThat (System.FilePath.isValid path)
                        "filename must contain only valid characters"

                checkNoDirectoryComponent path =
                    checkThat (path == takeFileName path)
                        "filename must contain no directory component"


pClause :: PParser ()
pClause = do reserved "executable"; lchar '=';
             exec <- filename
             st <- get
             put (st { execout = Just exec })

      <|> do reserved "main"; lchar '=';
             main <- fst <$> iName []
             st <- get
             put (st { idris_main = Just main })

      <|> do reserved "sourcedir"; lchar '=';
             src <- fst <$> identifier
             st <- get
             put (st { sourcedir = src })

      <|> do reserved "opts"; lchar '=';
             opts <- stringLiteral
             st <- get
             let args = pureArgParser (words opts)
             put (st { idris_opts = args ++ idris_opts st })

      <|> do reserved "pkgs"; lchar '=';
             ps <- sepBy1 (fst <$> identifier) (lchar ',')
             st <- get
             let pkgs = pureArgParser $ concatMap (\x -> ["-p", x]) ps

             put (st { pkgdeps    = ps `union` (pkgdeps st)
                     , idris_opts = pkgs ++ idris_opts st})

      <|> do reserved "modules"; lchar '=';
             ms <- sepBy1 (fst <$> iName []) (lchar ',')
             st <- get
             put (st { modules = modules st ++ ms })

      <|> do reserved "libs"; lchar '=';
             ls <- sepBy1 (fst <$> identifier) (lchar ',')
             st <- get
             put (st { libdeps = libdeps st ++ ls })

      <|> do reserved "objs"; lchar '=';
             ls <- sepBy1 (fst <$> identifier) (lchar ',')
             st <- get
             put (st { objs = objs st ++ ls })

      <|> do reserved "makefile"; lchar '=';
             mk <- fst <$> iName []
             st <- get
             put (st { makefile = Just (show mk) })

      <|> do reserved "tests"; lchar '=';
             ts <- sepBy1 (fst <$> iName []) (lchar ',')
             st <- get
             put st { idris_tests = idris_tests st ++ ts }

      <|> do reserved "version"
             lchar '='
             vStr <- many (satisfy (not . isEol))
             eol
             someSpace
             st <- get
             put st {pkgversion = Just vStr}

      <|> do reserved "readme"
             lchar '='
             rme <- many (satisfy (not . isEol))
             eol
             someSpace
             st <- get
             put (st { pkgreadme = Just rme })

      <|> do reserved "license"
             lchar '='
             lStr <- many (satisfy (not . isEol))
             eol
             st <- get
             put st {pkglicense = Just lStr}

      <|> do reserved "homepage"
             lchar '='
             www <- many (satisfy (not . isEol))
             eol
             someSpace
             st <- get
             put st {pkghomepage = Just www}

      <|> do reserved "sourceloc"
             lchar '='
             srcpage <- many (satisfy (not . isEol))
             eol
             someSpace
             st <- get
             put st {pkgsourceloc = Just srcpage}

      <|> do reserved "bugtracker"
             lchar '='
             src <- many (satisfy (not . isEol))
             eol
             someSpace
             st <- get
             put st {pkgbugtracker = Just src}

      <|> do reserved "brief"
             lchar '='
             brief <- stringLiteral
             st <- get
             someSpace
             put st {pkgbrief = Just brief}

      <|> do reserved "author"; lchar '=';
             author <- many (satisfy (not . isEol))
             eol
             someSpace
             st <- get
             put st {pkgauthor = Just author}

      <|> do reserved "maintainer"; lchar '=';
             maintainer <- many (satisfy (not . isEol))
             eol
             someSpace
             st <- get
             put st {pkgmaintainer = Just maintainer}

{-|
Module      : Idris.Package.Parser
Description : `iPKG` file parser and package description information.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE CPP, ConstraintKinds, FlexibleInstances, TypeSynonymInstances #-}
module Idris.Package.Parser where

import Idris.CmdOptions
import Idris.Imports
import Idris.Package.Common
import Idris.Parser.Helpers hiding (stringLiteral)

import Control.Applicative
import Control.Monad.State.Strict
import Data.List (union)
import System.Directory (doesFileExist)
import System.Exit
import System.FilePath (isValid, takeExtension, takeFileName)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Text.Trifecta ((<?>))
import qualified Text.Trifecta as P

type PParser = StateT PkgDesc IdrisInnerParser

instance HasLastTokenSpan PParser where
  getLastTokenSpan = return Nothing

#if MIN_VERSION_base(4,9,0)
instance {-# OVERLAPPING #-} P.DeltaParsing PParser where
  line = lift P.line
  {-# INLINE line #-}
  position = lift P.position
  {-# INLINE position #-}
  slicedWith f (StateT m) = StateT $ \s -> P.slicedWith (\(a,s') b -> (f a b, s')) $ m s
  {-# INLINE slicedWith #-}
  rend = lift P.rend
  {-# INLINE rend #-}
  restOfLine = lift P.restOfLine
  {-# INLINE restOfLine #-}
#endif

instance {-# OVERLAPPING #-} P.TokenParsing PParser where
  someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()


parseDesc :: FilePath -> IO PkgDesc
parseDesc fp = do
    when (not $ takeExtension fp == ".ipkg") $ do
        putStrLn $ unwords ["The presented iPKG file does not have a '.ipkg' extension:", show fp]
        exitWith (ExitFailure 1)
    res <- doesFileExist fp
    if res
      then do
        p <- readFile fp
        case runparser pPkg defaultPkg fp p of
          P.Failure (P.ErrInfo err _) -> fail (show $ PP.plain err)
          P.Success x -> return x
      else do
        putStrLn $ unwords [ "The presented iPKG file does not exist:", show fp]
        exitWith (ExitFailure 1)

pPkg :: PParser PkgDesc
pPkg = do
    reserved "package"
    p <- pPkgName
    P.someSpace
    st <- get
    put (st { pkgname = p })
    some pClause
    st <- get
    P.eof
    return st

pPkgName :: PParser PkgName
pPkgName = (either fail pure . pkgName =<< packageName) <?> "PkgName"

-- | Parses a filename.
-- |
-- | Treated for now as an identifier or a double-quoted string.
filename :: (MonadicParsing m, HasLastTokenSpan m) => m String
filename = (do
    filename <- P.token $
        -- Treat a double-quoted string as a filename to support spaces.
        -- This also moves away from tying filenames to identifiers, so
        -- it will also accept hyphens
        -- (https://github.com/idris-lang/Idris-dev/issues/2721)
        P.stringLiteral
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
             opts <- P.stringLiteral
             st <- get
             let args = pureArgParser (words opts)
             put (st { idris_opts = args ++ idris_opts st })

      <|> do reserved "pkgs"; lchar '=';
             ps <- P.sepBy1 (pPkgName <* P.someSpace) (lchar ',')
             st <- get
             let pkgs = pureArgParser $ concatMap (\x -> ["-p", show x]) ps

             put (st { pkgdeps    = ps `union` (pkgdeps st)
                     , idris_opts = pkgs ++ idris_opts st})

      <|> do reserved "modules"; lchar '=';
             ms <- P.sepBy1 (fst <$> iName []) (lchar ',')
             st <- get
             put (st { modules = modules st ++ ms })

      <|> do reserved "libs"; lchar '=';
             ls <- P.sepBy1 (fst <$> identifier) (lchar ',')
             st <- get
             put (st { libdeps = libdeps st ++ ls })

      <|> do reserved "objs"; lchar '=';
             ls <- P.sepBy1 (fst <$> identifier) (lchar ',')
             st <- get
             put (st { objs = objs st ++ ls })

      <|> do reserved "makefile"; lchar '=';
             mk <- fst <$> iName []
             st <- get
             put (st { makefile = Just (show mk) })

      <|> do reserved "tests"; lchar '=';
             ts <- P.sepBy1 (fst <$> iName []) (lchar ',')
             st <- get
             put st { idris_tests = idris_tests st ++ ts }

      <|> do reserved "version"
             lchar '='
             vStr <- many (P.satisfy (not . isEol))
             eol
             P.someSpace
             st <- get
             put st {pkgversion = Just vStr}

      <|> do reserved "readme"
             lchar '='
             rme <- many (P.satisfy (not . isEol))
             eol
             P.someSpace
             st <- get
             put (st { pkgreadme = Just rme })

      <|> do reserved "license"
             lchar '='
             lStr <- many (P.satisfy (not . isEol))
             eol
             st <- get
             put st {pkglicense = Just lStr}

      <|> do reserved "homepage"
             lchar '='
             www <- many (P.satisfy (not . isEol))
             eol
             P.someSpace
             st <- get
             put st {pkghomepage = Just www}

      <|> do reserved "sourceloc"
             lchar '='
             srcpage <- many (P.satisfy (not . isEol))
             eol
             P.someSpace
             st <- get
             put st {pkgsourceloc = Just srcpage}

      <|> do reserved "bugtracker"
             lchar '='
             src <- many (P.satisfy (not . isEol))
             eol
             P.someSpace
             st <- get
             put st {pkgbugtracker = Just src}

      <|> do reserved "brief"
             lchar '='
             brief <- P.stringLiteral
             st <- get
             P.someSpace
             put st {pkgbrief = Just brief}

      <|> do reserved "author"; lchar '=';
             author <- many (P.satisfy (not . isEol))
             eol
             P.someSpace
             st <- get
             put st {pkgauthor = Just author}

      <|> do reserved "maintainer"; lchar '=';
             maintainer <- many (P.satisfy (not . isEol))
             eol
             P.someSpace
             st <- get
             put st {pkgmaintainer = Just maintainer}

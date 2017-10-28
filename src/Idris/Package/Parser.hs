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
import Idris.Parser.Helpers (HasLastTokenSpan, IdrisInnerParser, MonadicParsing,
                             eol, getLastTokenSpan, iName, identifier, isEol,
                             lchar, multiLineComment, packageName,
                             parseErrorDoc, reserved, runparser,
                             simpleWhiteSpace, singleLineComment)

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
          Left err -> fail (show $ PP.plain $ parseErrorDoc err)
          Right x -> return x
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

textUntilEol :: MonadicParsing m => m String
textUntilEol = many (P.satisfy (not . isEol)) <* eol <* P.someSpace

clause          :: String -> PParser a -> (PkgDesc -> a -> PkgDesc) -> PParser ()
clause name p f = do value <- reserved name *> lchar '=' *> p
                     modify $ \st -> f st value

commaSep   :: MonadicParsing m => m a -> m [a]
commaSep p = P.sepBy1 p (lchar ',')

pClause :: PParser ()
pClause = clause "executable" filename (\st v -> st { execout = Just v })
      <|> clause "main" (fst <$> iName []) (\st v -> st { idris_main = Just v })
      <|> clause "sourcedir" (fst <$> identifier) (\st v -> st { sourcedir = v })
      <|> clause "opts" (pureArgParser . words <$> P.stringLiteral) (\st v -> st { idris_opts = v ++ idris_opts st })
      <|> clause "pkgs" (commaSep (pPkgName <* P.someSpace)) (\st ps ->
             let pkgs = pureArgParser $ concatMap (\x -> ["-p", show x]) ps
             in st { pkgdeps    = ps `union` pkgdeps st
                   , idris_opts = pkgs ++ idris_opts st })
      <|> clause "modules" (commaSep (fst <$> iName [])) (\st v -> st { modules = modules st ++ v })
      <|> clause "libs" (commaSep (fst <$> identifier)) (\st v -> st { libdeps = libdeps st ++ v })
      <|> clause "objs" (commaSep (fst <$> identifier)) (\st v -> st { objs = objs st ++ v })
      <|> clause "makefile" (fst <$> iName []) (\st v -> st { makefile = Just (show v) })
      <|> clause "tests" (commaSep (fst <$> iName [])) (\st v -> st { idris_tests = idris_tests st ++ v })
      <|> clause "version" textUntilEol (\st v -> st { pkgversion = Just v })
      <|> clause "readme" textUntilEol (\st v -> st { pkgreadme = Just v })
      <|> clause "license" textUntilEol (\st v -> st { pkglicense = Just v })
      <|> clause "homepage" textUntilEol (\st v -> st { pkghomepage = Just v })
      <|> clause "sourceloc" textUntilEol (\st v -> st { pkgsourceloc = Just v })
      <|> clause "bugtracker" textUntilEol (\st v -> st { pkgbugtracker = Just v })
      <|> clause "brief" (P.stringLiteral <* P.someSpace) (\st v -> st { pkgbrief = Just v })
      <|> clause "author" textUntilEol (\st v -> st { pkgauthor = Just v })
      <|> clause "maintainer" textUntilEol (\st v -> st { pkgmaintainer = Just v })

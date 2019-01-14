{-|
Module      : Idris.Package.Parser
Description : `iPKG` file parser and package description information.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE FlexibleContexts #-}
module Idris.Package.Parser where

import Idris.CmdOptions
import Idris.Imports
import Idris.Options (Opt)
import Idris.Package.Common
import Idris.Parser (moduleName)
import Idris.Parser.Helpers (Parser, Parsing, eol, iName, identifier,
                             identifierWithExtraChars, isEol, lchar,
                             packageName, parseErrorDoc, reserved, runparser,
                             someSpace, stringLiteral)

import Control.Applicative
import Control.Monad.State.Strict
import Data.List (union)
import qualified Options.Applicative as Opts
import System.Directory (doesFileExist)
import System.Exit
import System.FilePath (isValid, takeExtension, takeFileName)
import Text.Megaparsec ((<?>))
import qualified Text.Megaparsec as P
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type PParser = Parser PkgDesc

parseDesc :: FilePath -> IO PkgDesc
parseDesc fp = do
    unless (takeExtension fp == ".ipkg") $ do
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
    someSpace
    modify $ \st -> st { pkgname = p }
    some pClause
    st <- get
    P.eof
    return st

pPkgName :: PParser PkgName
pPkgName = (either fail pure . pkgName =<< packageName) <?> "PkgName"

-- | Parses a filename.
-- |
-- | Treated for now as an identifier or a double-quoted string.
filename :: Parsing m => m String
filename = (do
                -- Treat a double-quoted string as a filename to support spaces.
                -- This also moves away from tying filenames to identifiers, so
                -- it will also accept hyphens
                -- (https://github.com/idris-lang/Idris-dev/issues/2721)
    filename <- stringLiteral
                -- Through at least version 0.9.19.1, IPKG executable values were
                -- possibly namespaced identifiers, like foo.bar.baz.
            <|> show <$> iName []
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

textUntilEol :: Parsing m => m String
textUntilEol = many (P.satisfy (not . isEol)) <* eol <* someSpace

clause          :: String -> PParser a -> (PkgDesc -> a -> PkgDesc) -> PParser ()
clause name p f = do value <- reserved name *> lchar '=' *> p <* someSpace
                     modify $ \st -> f st value

commaSep   :: Parsing m => m a -> m [a]
commaSep p = P.sepBy1 p (lchar ',')

pOptions :: PParser [Opt]
pOptions = do
  str <- stringLiteral
  case execArgParserPure (words str) of
    Opts.Success a -> return a
    Opts.Failure e -> fail $ fst $ Opts.renderFailure e ""
    _              -> fail "Unexpected error"

libIdentifier :: Parsing m => m String
libIdentifier = identifierWithExtraChars "_'-."

pClause :: PParser ()
pClause = clause "executable" filename (\st v -> st { execout = Just v })
      <|> clause "main" (iName []) (\st v -> st { idris_main = Just v })
      <|> clause "sourcedir" (identifier <|> stringLiteral) (\st v -> st { sourcedir = v })
      <|> clause "opts" pOptions (\st v -> st { idris_opts = v ++ idris_opts st })
      <|> clause "pkgs" (commaSep (pPkgName <* someSpace)) (\st ps ->
             let pkgs = pureArgParser $ concatMap (\x -> ["-p", show x]) ps
             in st { pkgdeps    = ps `union` pkgdeps st
                   , idris_opts = pkgs ++ idris_opts st })
      <|> clause "modules" (commaSep moduleName) (\st v -> st { modules = modules st ++ v })
      <|> clause "libs" (commaSep libIdentifier) (\st v -> st { libdeps = libdeps st ++ v })
      <|> clause "objs" (commaSep identifier) (\st v -> st { objs = objs st ++ v })
      <|> clause "makefile" (iName []) (\st v -> st { makefile = Just (show v) })
      <|> clause "tests" (commaSep (iName [])) (\st v -> st { idris_tests = idris_tests st ++ v })
      <|> clause "version" textUntilEol (\st v -> st { pkgversion = Just v })
      <|> clause "readme" textUntilEol (\st v -> st { pkgreadme = Just v })
      <|> clause "license" textUntilEol (\st v -> st { pkglicense = Just v })
      <|> clause "homepage" textUntilEol (\st v -> st { pkghomepage = Just v })
      <|> clause "sourceloc" textUntilEol (\st v -> st { pkgsourceloc = Just v })
      <|> clause "bugtracker" textUntilEol (\st v -> st { pkgbugtracker = Just v })
      <|> clause "brief" stringLiteral (\st v -> st { pkgbrief = Just v })
      <|> clause "author" textUntilEol (\st v -> st { pkgauthor = Just v })
      <|> clause "maintainer" textUntilEol (\st v -> st { pkgmaintainer = Just v })


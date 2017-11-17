{-|
Module      : Idris.Parser.Parser
Description : Low-level parser wrappers and tools.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}
module Idris.Parser.Parser
  ( -- * Parsing
    Parser(..)
  , Parsing(..)
  , runparser
    -- * Parse state
  , ParseState
    -- * Parse errors
  , ParseError
  , errorSpan
  , parseErrorMessage
  , parseErrorPretty
    -- * Parse position
  , getFC
  )
where

import Idris.Core.TT (FC(..))

import Control.Monad.State.Strict (StateT(..), evalStateT)
import Control.Monad.Writer.Strict (MonadWriter(..), WriterT(..), runWriterT)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Void (Void(..))
import System.FilePath (addTrailingPathSeparator, splitFileName)
import qualified Text.Megaparsec as P

{- * Parsing -}

-- | Our parser stack with state of type @s@
type Parser s = StateT s (WriterT FC (P.Parsec Void String))

-- | A constraint for parsing without state
type Parsing m = (P.MonadParsec Void String m, MonadWriter FC m)

-- | Run the Idris parser stack
runparser :: Parser st res -> st -> String -> String -> Either ParseError res
runparser p i inputname s =
  case P.parse (runWriterT (evalStateT p i)) inputname s of
    Left err -> Left $ ParseError s err
    Right v  -> Right $ fst v

{- * Parse state -}

type ParseState = P.State String

{- * Parse errors -}

data ParseError = ParseError String (P.ParseError (P.Token String) Void)

-- | Retrieve a parse error's FC
errorSpan :: ParseError -> FC
errorSpan (ParseError _ err) = sourcePositionFC pos
  where
    (pos NonEmpty.:| _) = P.errorPos err

parseErrorMessage :: ParseError -> String
parseErrorMessage (ParseError _ err) = P.parseErrorTextPretty err

parseErrorPretty                    :: ParseError -> String
parseErrorPretty (ParseError s err) = P.parseErrorPretty' s err

{- * Parse position -}

sourcePositionFC :: P.SourcePos -> FC
sourcePositionFC (P.SourcePos name line column) =
  FC f (lineNumber, columnNumber) (lineNumber, columnNumber)
  where
    lineNumber = P.unPos line
    columnNumber = P.unPos column
    (dir, file) = splitFileName name
    f = if dir == addTrailingPathSeparator "."
        then file
        else name

-- | Get the current parse position.
getFC :: Parsing m => m FC
getFC = sourcePositionFC <$> P.getPosition

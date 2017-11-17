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
  , errorMessage
  , prettyError
    -- * Parse position
  , getFC
  , extent
  , addExtent
  , trackExtent
  , hideExtent
  )
where

import Idris.Core.TT (FC(..))

import Control.Monad.State.Strict (StateT(..), evalStateT)
import Control.Monad.Writer.Strict (MonadWriter(..), WriterT(..), censor, runWriterT, tell)
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

-- | A single-line parse error message, including location.
errorMessage :: ParseError -> String
errorMessage (ParseError _ err) = P.parseErrorTextPretty err

-- | A fully formatted parse error, with caret and bar, etc.
prettyError                    :: ParseError -> String
prettyError (ParseError s err) = P.parseErrorPretty' s err

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

-- | Run a parser and return only its extent.
extent :: MonadWriter FC m => m a -> m FC
extent = fmap snd . listen

-- | Add an extent (widen) our current parsing context.
addExtent :: MonadWriter FC m => FC -> m ()
addExtent = tell

-- | Run a parser and track its extent.
trackExtent :: Parsing m => m a -> m a
trackExtent p = do (FC f (sr, sc) _) <- getFC
                   result <- p
                   (FC f _ (er, ec)) <- getFC
                   addExtent (FC f (sr, sc) (er, max 1 (ec - 1)))
                   return result

-- | Run a parser, hiding its extent.
hideExtent :: Parsing m => m a -> m a
hideExtent = censor (const NoFC)

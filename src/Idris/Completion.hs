module Idris.Completion (idrisCompletion) where

import Core.Evaluate (ctxtAlist)
import Core.TT

import Idris.AbsSyntaxTree

import Control.Monad.State.Strict

import Data.List
import Data.Maybe

import System.Console.Haskeline


-- | Convert a name into a string usable for completion. Filters out names
-- that users probably don't want to see.
nameString :: Name -> Maybe String
nameString (UN ('@':_)) = Nothing
nameString (UN ('#':_)) = Nothing
nameString (UN n)       = Just n
nameString (NS n _)     = nameString n
nameString _            = Nothing

-- FIXME: Respect module imports
-- | Get the user-visible names from the current interpreter state.
names :: StateT IState IO [String]
names = do i <- get
           let ctxt = tt_ctxt i
           return $ nub $ mapMaybe (nameString . fst) $ ctxtAlist ctxt

completeWith :: [String] -> String -> [Completion]
completeWith ns n = if uniqueExists
                    then [simpleCompletion n]
                    else map simpleCompletion prefixMatches
    where prefixMatches = filter (isPrefixOf n) ns
          uniqueExists = n `elem` prefixMatches

completeName :: String -> StateT IState IO [Completion]
completeName n = do ns <- names
                    return $ completeWith ns n

completeExpr :: CompletionFunc (StateT IState IO)
completeExpr = completeWord Nothing [' ', '\t'] completeName

idrisCompletion :: [String] -> CompletionFunc (StateT IState IO)
idrisCompletion commands (before, after) = complete (reverse $ dropWhile (\x -> x == ' ') before)
    where complete :: String -> StateT IState IO (String, [Completion])
          complete []        = noCompletions
          complete (':':cmd) = return $ ("", completeWith commands (':':cmd))
          complete _         = completeExpr (before, after)

          noCompletions = return (before, [])



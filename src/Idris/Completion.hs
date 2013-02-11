module Idris.Completion (idrisCompletion) where

import Core.Evaluate (ctxtAlist)
import Core.TT

import Idris.AbsSyntaxTree

import Control.Monad.State.Strict

import Data.List
import Data.Maybe

import System.Console.Haskeline

-- TODO: add specific classes of identifiers to complete, fx metavariables
-- | A specification of the arguments that REPL commands can take
data CmdArg = ExprArg -- ^ The command takes an expression
            | NameArg -- ^ The command takes a name
            | FileArg -- ^ The command takes a file
            | ModuleArg -- ^ The command takes a module name
            | OptionArg -- ^ The command takes an option

-- | Information about how to complete the various commands
cmdArgs :: [(String, CmdArg)]
cmdArgs = [ (":t", ExprArg)
          , (":miss", NameArg)
          , (":missing", NameArg)
          , (":i", NameArg)
          , (":info", NameArg)
          , (":total", NameArg)
          , (":l", FileArg)
          , (":load", FileArg)
          , (":m", ModuleArg) -- NOTE: Argumentless form is a different command
          , (":p", NameArg)
          , (":prove", NameArg)
          , (":a", NameArg)
          , (":addproof", NameArg)
          , (":rmproof", NameArg)
          , (":showproof", NameArg)
          , (":c", FileArg)
          , (":compile", FileArg)
          , (":js", FileArg)
          , (":javascript", FileArg)
          , (":set", OptionArg)
          , (":unset", OptionArg)
          ]
commands = map fst cmdArgs

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


modules :: StateT IState IO [String]
modules = do i <- get
             return $ map show $ imported i

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
completeExpr = completeWord Nothing " \t" completeName

completeOption :: CompletionFunc (StateT IState IO)
completeOption = completeWord Nothing " \t" completeOpt
    where completeOpt = return . (completeWith ["errorcontext", "showimplicits"])

isWhitespace :: Char -> Bool
isWhitespace = (flip elem) " \t\n"

-- | Get the completion function for a particular command
completeCmd :: String -> CompletionFunc (StateT IState IO)
completeCmd cmd (prev, next) = fromMaybe completeCmdName (fmap completeArg $ lookup cmd cmdArgs)
    where completeArg FileArg = completeFilename (prev, next)
          completeArg NameArg = completeExpr (prev, next) -- FIXME only complete one name
          completeArg OptionArg = completeOption (prev, next)
          completeArg ModuleArg = noCompletion (prev, next) -- FIXME do later
          completeArg ExprArg = completeExpr (prev, next)
          completeCmdName = return $ ("", completeWith commands cmd)

idrisCompletion :: CompletionFunc (StateT IState IO)
idrisCompletion (prev, next) = case firstWord of
                                 ':':cmdName -> completeCmd (':':cmdName) (prev, next)
                                 _ -> completeExpr (prev, next)
    where (firstWord, remainder) = break isWhitespace $ dropWhile isWhitespace $ reverse prev
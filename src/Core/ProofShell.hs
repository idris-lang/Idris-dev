{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, PatternGuards #-}

module Core.ProofShell where

import Core.Typecheck
import Core.Evaluate
import Core.TT
import Core.ShellParser
import Core.Elaborate

import Control.Monad.State
import System.Console.Haskeline

import Util.Pretty

data ShellState = ShellState 
                        { ctxt     :: Context,
                          prf      :: Maybe ProofState,
                          deferred :: [(Name, ProofState)],
                          exitNow  :: Bool
                        }

initState c = ShellState c Nothing [] False

processCommand :: Command -> ShellState -> (ShellState, String)
processCommand (Theorem n ty) state 
    = case check (ctxt state) [] ty of
              OK (gl, t) -> 
                 case isTType (ctxt state) [] t of
                    OK _ -> (state { prf = Just (newProof n (ctxt state) gl) }, "")
                    _ ->    (state, "Goal is not a type")
              err ->            (state, show err)
processCommand Quit     state = (state { exitNow = True }, "Bye bye")
processCommand (Eval t) state = 
    case check (ctxt state) [] t of
         OK (val, ty) ->
            let nf = normalise (ctxt state) [] val 
                tnf = normalise (ctxt state) [] ty in
                (state, show nf ++ " : " ++ show ty)
         err -> (state, show err)
processCommand (Print n) state =
    case lookupDef Nothing n (ctxt state) of
         [tm] -> (state, show tm)
         _ -> (state, "No such name")
processCommand (Tac e)  state 
    | Just ps <- prf state = case execElab () e ps of
                                OK (ES (ps', _) resp _) -> 
                                   if (not (done ps')) 
                                      then (state { prf = Just ps' }, resp)
                                      else (state { prf = Nothing,
                                                    ctxt = addToCtxt (thname ps')
                                                                     (pterm ps')
                                                                     (ptype ps')
                                                                     (context ps') }, resp)
                                err -> (state, show err)
    | otherwise = (state, "No proof in progress")

runShell :: ShellState -> InputT IO ShellState
runShell st = do (prompt, parser) <- 
                           maybe (return ("TT# ", parseCommand)) 
                                 (\st -> do outputStrLn . render . pretty $ st
                                            return (show (thname st) ++ "# ", parseTactic)) 
                                 (prf st)
                 x <- getInputLine prompt
                 cmd <- case x of
                    Nothing -> return $ Right Quit
                    Just input -> return (parser input)
                 case cmd of
                    Left err -> do outputStrLn (show err)
                                   runShell st
                    Right cmd -> do let (st', r) = processCommand cmd st
                                    outputStrLn r
                                    if (not (exitNow st')) then runShell st'
                                                           else return st'


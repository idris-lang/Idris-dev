{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module ProofShell where

import Typecheck
import Evaluate
import Core
import ShellParser
import Elaborate

import Control.Monad.State
import System.Console.Readline

data ShellState = State { ctxt     :: Context,
                          prf      :: Maybe ProofState,
                          deferred :: [(Name, ProofState)],
                          exitNow  :: Bool
                        }

initState c = State c Nothing [] False

processCommand :: Command -> ShellState -> (ShellState, String)
processCommand (Theorem n ty) state 
    = case check (ctxt state) [] ty of
              OK (gl, t) -> 
                 case isSet (ctxt state) [] t of
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
    case lookupDef n (ctxt state) of
         Just tm -> (state, show tm)
         Nothing -> (state, "No such name")
processCommand (Tac e)  state 
    | Just ps <- prf state = case runElab e ps of
                                OK (ps', resp) -> 
                                   if (not (done ps')) 
                                      then (state { prf = Just ps' }, resp)
                                      else (state { prf = Nothing,
                                                    ctxt = addToCtxt (thname ps')
                                                                     (pterm ps')
                                                                     (ptype ps')
                                                                     (context ps') }, resp)
                                err -> (state, show err)
    | otherwise = (state, "No proof in progress")

runShell :: ShellState -> IO ShellState
runShell st = do (prompt, parser) <- 
                           maybe (return ("> ", parseCommand)) 
                                 (\st -> do print st
                                            return (show (thname st) ++ "> ", parseTactic)) 
                                 (prf st)
                 x <- readline prompt
                 cmd <- case x of
                    Nothing -> return $ Right Quit
                    Just input -> do addHistory input
                                     return (parser input)
                 case cmd of
                    Left err -> do putStrLn (show err)
                                   runShell st
                    Right cmd -> do let (st', r) = processCommand cmd st
                                    putStrLn r
                                    if (not (exitNow st')) then runShell st'
                                                           else return st'


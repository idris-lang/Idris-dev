module Idris.Prover where

import Core.Elaborate hiding (Tactic(..))
import Core.TT
import Core.Evaluate
import Core.CaseTree
import Core.Typecheck

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Parser
import Idris.Error
import Idris.DataOpts
import Idris.Completion
import Idris.IdeSlave

import System.Console.Haskeline
import System.Console.Haskeline.History
import Control.Monad.State

import Util.Pretty
import Debug.Trace

prover :: Bool -> Name -> Idris ()
prover lit x =
           do ctxt <- getContext
              i <- getIState
              case lookupTy x ctxt of
                  [t] -> if elem x (idris_metavars i)
                               then prove ctxt lit x t
                               else fail $ show x ++ " is not a metavariable"
                  _ -> fail "No such metavariable"

showProof :: Bool -> Name -> [String] -> String
showProof lit n ps 
    = bird ++ show n ++ " = proof {" ++ break ++
             showSep break (map (\x -> "  " ++ x ++ ";") ps) ++
                     break ++ "}\n"
  where bird = if lit then "> " else ""
        break = "\n" ++ bird

proverSettings :: ElabState [PDecl] -> Settings Idris
proverSettings e = setComplete (proverCompletion (assumptionNames e)) defaultSettings

assumptionNames :: ElabState [PDecl] -> [String]
assumptionNames e
  = case envAtFocus (proof e) of
         OK env -> names env
  where names [] = []
        names ((MN _ _, _) : bs) = names bs
        names ((n, _) : bs) = show n : names bs

prove :: Context -> Bool -> Name -> Type -> Idris ()
prove ctxt lit n ty
    = do let ps = initElaborator n ctxt ty
         ideslavePutSExp "start-proof-mode" n
         (tm, prf) <- ploop True ("-" ++ show n) [] (ES (ps, []) "" Nothing) Nothing
         iLOG $ "Adding " ++ show tm
         iputStrLn $ showProof lit n prf
         i <- getIState
         ideslavePutSExp "end-proof-mode" n
         let proofs = proof_list i
         putIState (i { proof_list = (n, prf) : proofs })
         let tree = simpleCase False True False CompileTime (FC "proof" 0) [([], P Ref n ty, tm)]
         logLvl 3 (show tree)
         (ptm, pty) <- recheckC (FC "proof" 0) [] tm
         logLvl 5 ("Proof type: " ++ show pty ++ "\n" ++
                   "Expected type:" ++ show ty)
         case converts ctxt [] ty pty of
              OK _ -> return ()
              Error e -> ierror (CantUnify False ty pty e [] 0)
         ptm' <- applyOpts ptm
         updateContext (addCasedef n (CaseInfo True False) False False True False
                                 [Right (P Ref n ty, ptm)]
                                 [([], P Ref n ty, ptm)]
                                 [([], P Ref n ty, ptm')] ty)
         solveDeferred n
elabStep :: ElabState [PDecl] -> ElabD a -> Idris (a, ElabState [PDecl])
elabStep st e = do case runStateT e st of
                     OK (a, st') -> return (a, st')
                     Error a -> do i <- getIState
                                   fail (pshow i a)

dumpState :: IState -> ProofState -> Idris ()
dumpState ist (PS nm [] _ _ tm _ _ _ _ _ _ _ _ _ _ _ _ _ _) =
  iputGoal . render $ pretty nm <> colon <+> text "No more goals."
dumpState ist ps@(PS nm (h:hs) _ _ tm _ _ _ _ _ _ problems i _ _ ctxy _ _ _) = do
  let OK ty  = goalAtFocus ps
  let OK env = envAtFocus ps
  iputGoal . render $
    prettyOtherGoals hs $$
    prettyAssumptions env $$
    prettyGoal ty
  where
    -- XXX
    tPretty t = pretty $ delab ist t

    prettyPs [] = empty
    prettyPs ((MN _ "rewrite_rule", _) : bs) = prettyPs bs
    prettyPs ((n, Let t v) : bs) =
      nest nestingSize (pretty n <+> text "=" <+> tPretty v <> colon <+>
        tPretty t $$ prettyPs bs)
    prettyPs ((n, b) : bs) = 
      pretty n <+> colon <+> tPretty (binderTy b) $$ prettyPs bs

    prettyG (Guess t v) = tPretty t <+> text "=?=" <+> tPretty v
    prettyG b = tPretty $ binderTy b

    prettyGoal ty =
      text "----------                 Goal:                  ----------" $$
      pretty h <> colon $$ nest nestingSize (prettyG ty)

    prettyAssumptions env =
      if length env == 0 then
        empty
      else
        text "----------              Assumptions:              ----------" $$
        nest nestingSize (prettyPs $ reverse env)

    prettyOtherGoals hs =
      if length hs == 0 then
        empty
      else
        text "----------              Other goals:              ----------" $$
        pretty hs

lifte :: ElabState [PDecl] -> ElabD a -> Idris a
lifte st e = do (v, _) <- elabStep st e
                return v

receiveInput :: ElabState [PDecl] -> Idris (Maybe String)
receiveInput e =
  do i <- getIState
     l <- liftIO $ getLine
     let (sexp, id) = parseMessage l
     putIState $ i { idris_outputmode = (IdeSlave id) }
     case sexpToCommand sexp of
       Just (REPLCompletions prefix) ->
         do (unused, compls) <- proverCompletion (assumptionNames e) (reverse prefix, "")
            let good = SexpList [SymbolAtom "ok", toSExp (map replacement compls, reverse unused)]
            ideslavePutSExp "return" good
            receiveInput e
       Just (Interpret cmd) -> return (Just cmd)
       Nothing -> return Nothing

ploop :: Bool -> String -> [String] -> ElabState [PDecl] -> Maybe History -> Idris (Term, [String])
ploop d prompt prf e h
    = do i <- getIState
         when d $ dumpState i (proof e)
         (x, h') <-
           case idris_outputmode i of
             RawOutput -> runInputT (proverSettings e) $
                          -- Manually track the history so that we can use the proof state
                          do _ <- case h of
                               Just history -> putHistory history
                               Nothing -> return ()
                             l <- getInputLine (prompt ++ "> ")
                             h' <- getHistory
                             return (l, Just h')
             IdeSlave n ->
               do isetPrompt prompt
                  i <- receiveInput e
                  return (i, h)
         (cmd, step) <- case x of
            Nothing -> do iFail ""; fail "Abandoned"
            Just input -> do return (parseTac i input, input)
         case cmd of
            Right Abandon -> do iFail ""; fail "Abandoned"
            _ -> return ()
         (d, st, done, prf') <- idrisCatch
           (case cmd of
              Left err -> do iFail (show err)
                             return (False, e, False, prf)
              Right Undo -> do (_, st) <- elabStep e loadState
                               iResult ""
                               return (True, st, False, init prf)
              Right ProofState -> do iResult ""
                                     return (True, e, False, prf)
              Right ProofTerm -> do tm <- lifte e get_term
                                    iResult $ "TT: " ++ show tm ++ "\n"
                                    return (False, e, False, prf)
              Right Qed -> do hs <- lifte e get_holes
                              when (not (null hs)) $ fail "Incomplete proof"
                              iResult "Proof completed!"
                              return (False, e, True, prf)
              Right tac -> do (_, e) <- elabStep e saveState
                              (_, st) <- elabStep e (runTac True i tac)
--                               trace (show (problems (proof st))) $
                              iResult ""
                              return (True, st, False, prf ++ [step]))
           (\err -> do iFail (show err)
                       return (False, e, False, prf))
         ideslavePutSExp "write-proof-state" (prf', length prf')
         if done then do (tm, _) <- elabStep st get_term
                         return (tm, prf')
                 else ploop d prompt prf' st h'


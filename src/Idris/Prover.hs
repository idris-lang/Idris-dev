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

import System.Console.Haskeline
import Control.Monad.State

import Util.Pretty

prover :: Bool -> Name -> Idris ()
prover lit x =
           do ctxt <- getContext
              i <- get
              case lookupTy Nothing x ctxt of
                  [t] -> if elem x (idris_metavars i)
                               then prove ctxt lit x t
                               else fail $ show x ++ " is not a metavariable"
                  _ -> fail "No such metavariable"

showProof :: Bool -> Name -> [String] -> String
showProof lit n ps 
    = bird ++ show n ++ " = proof {" ++ break ++
             showSep break (map (\x -> "    " ++ x ++ ";") ps) ++
                     break ++ "}\n"
  where bird = if lit then "> " else ""
        break = "\n" ++ bird

prove :: Context -> Bool -> Name -> Type -> Idris ()
prove ctxt lit n ty 
    = do let ps = initElaborator n ctxt ty 
         (tm, prf) <- ploop True ("-" ++ show n) [] (ES (ps, []) "" Nothing)
         iLOG $ "Adding " ++ show tm
         iputStrLn $ showProof lit n prf
         i <- get
         put (i { last_proof = Just (n, prf) })
         let tree = simpleCase False True [(P Ref n ty, tm)]
         logLvl 3 (show tree)
         (ptm, pty) <- recheckC (FC "proof" 0) [] tm
         ptm' <- applyOpts ptm
         updateContext (addCasedef n True False True [(P Ref n ty, ptm)] 
                                                [(P Ref n ty, ptm')] ty)
         solveDeferred n
elabStep :: ElabState [PDecl] -> ElabD a -> Idris (a, ElabState [PDecl])
elabStep st e = do case runStateT e st of
                     OK (a, st') -> return (a, st')
                     Error a -> do i <- get
                                   fail (pshow i a)

dumpState :: IState -> ProofState -> IO ()
dumpState ist (PS nm [] _ tm _ _ _ _ _ _ _ _ _ _ _) =
  putStrLn . render $ pretty nm <> colon <+> text "No more goals."
dumpState ist ps@(PS nm (h:hs) _ tm _ _ _ _ problems i _ _ ctxy _ _) = do
  let OK ty  = goalAtFocus ps
  let OK env = envAtFocus ps
  putStrLn . render $
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

ploop :: Bool -> String -> [String] -> ElabState [PDecl] -> Idris (Term, [String])
ploop d prompt prf e 
    = do i <- get
         when d $ liftIO $ dumpState i (proof e)
         x <- lift $ getInputLine (prompt ++ "> ")
         (cmd, step) <- case x of
            Nothing -> fail "Abandoned"
            Just input -> do return (parseTac i input, input)
         case cmd of
            Right Abandon -> fail "Abandoned"
            _ -> return ()
         (d, st, done, prf') <- idrisCatch 
           (case cmd of
              Left err -> do iputStrLn (show err)
                             return (False, e, False, prf)
              Right Undo -> 
                           do (_, st) <- elabStep e loadState
                              return (True, st, False, init prf)
              Right ProofState ->
                              return (True, e, False, prf)
              Right ProofTerm -> 
                           do tm <- lifte e get_term
                              iputStrLn $ "TT: " ++ show tm ++ "\n"
                              return (False, e, False, prf)
              Right Qed -> do hs <- lifte e get_holes
                              when (not (null hs)) $ fail "Incomplete proof"
                              return (False, e, True, prf)
              Right tac -> do (_, e) <- elabStep e saveState
                              (_, st) <- elabStep e (runTac True i tac)
                              return (True, st, False, prf ++ [step]))
           (\err -> do iputStrLn (show err)
                       return (False, e, False, prf))
         if done then do (tm, _) <- elabStep st get_term 
                         return (tm, prf')
                 else ploop d prompt prf' st


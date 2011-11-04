module Idris.Prover where

import Core.Elaborate hiding (Tactic(..))
import Core.TT
import Core.Evaluate
import Core.CaseTree
import Core.Typecheck

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.ElabDecls
import Idris.Parser
import Idris.Error

import System.Console.Readline
import Control.Monad.State

prover :: Name -> Idris ()
prover x = do ctxt <- getContext
              i <- get
              case lookupTy x ctxt of
                  Just t -> if elem x (idris_metavars i)
                               then prove ctxt x t
                               else fail $ show x ++ " is not a metavariable"
                  _ -> fail "No such metavariable"

dumpProof :: Name -> [String] -> IO ()
dumpProof n ps = do putStrLn $ show n ++ " = proof {"
                    mapM_ (\x -> putStrLn $ "    " ++ x ++ ";") ps
                    putStrLn "};\n"

prove :: Context -> Name -> Type -> Idris ()
prove ctxt n ty 
    = do let ps = initElaborator n ctxt ty 
         (tm, prf) <- ploop True ("-" ++ show n) [] (ES ps "" Nothing)
         iLOG $ "Adding " ++ show tm
         lift $ dumpProof n prf
         let tree = simpleCase False [(P Ref n ty, tm)]
         logLvl 3 (show tree)
         (ptm, pty) <- tclift $ recheck ctxt [] tm
         updateContext (addCasedef n False [(P Ref n ty, ptm)] ty)
         solveDeferred n

elabStep :: ElabState -> Elab a -> Idris (a, ElabState)
elabStep st e = do case runStateT e st of
                     OK (a, st') -> return (a, st')
                     Error a -> do i <- get
                                   fail (pshow i a)
                  
dumpState :: IState -> ProofState -> IO ()
dumpState ist (PS nm [] _ tm _ _ _ _ _ _ _ _) = putStrLn $ (show nm) ++ ": no more goals"
dumpState ist ps@(PS nm (h:hs) _ tm _ _ i _ _ ctxy _ _)
   = do let OK ty = goalAtFocus ps
        let OK env = envAtFocus ps
        putStrLn $ "Other goals: " ++ show hs ++ "\n"
        putStr $ showPs (reverse env)
        putStrLn $ "---------------------------------- (" ++ show nm
                     ++ ") --------"
        putStrLn $ show h ++ " : " ++ showG ty ++ "\n"
  where
    tshow t = show (delab ist t)

    showPs [] = ""
    showPs ((MN _ "rewrite_rule", _) : bs) = showPs bs
    showPs ((n, Let t v) : bs)
        = "  " ++ show n ++ " = " ++ tshow v ++ " : " ++
            tshow t ++ "\n" ++ showPs bs
    showPs ((n, b) : bs)
        = "  " ++ show n ++ " : " ++
            tshow (binderTy b) ++ "\n" ++ showPs bs

    showG (Guess t v) = tshow t ++ " =?= " ++ tshow v
    showG b = tshow (binderTy b)

lifte :: ElabState -> Elab a -> Idris a
lifte st e = do (v, _) <- elabStep st e
                return v

ploop :: Bool -> String -> [String] -> ElabState -> Idris (Term, [String])
ploop d prompt prf e 
    = do i <- get
         when d $ lift $ dumpState i (proof e)
         x <- lift $ readline (prompt ++ "> ")
         (cmd, step) <- case x of
            Nothing -> fail "Abandoned"
            Just input -> do lift $ addHistory input
                             return (parseTac i input, input)
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
           (\err -> do iputStrLn (report err)
                       return (False, e, False, prf))
         if done then do (tm, _) <- elabStep st get_term 
                         return (tm, prf')
                 else ploop d prompt prf' st


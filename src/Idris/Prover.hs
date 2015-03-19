{-# LANGUAGE PatternGuards #-}
module Idris.Prover where

import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.CaseTree
import Idris.Core.Typecheck

import Idris.Elab.Utils
import Idris.Elab.Value

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Delaborate
import Idris.Docs (getDocs, pprintDocs, pprintConstDocs)
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Parser hiding (params)
import Idris.Error
import Idris.DataOpts
import Idris.Completion
import qualified Idris.IdeMode as IdeMode
import Idris.Output
import Idris.TypeSearch (searchByType)

import Text.Trifecta.Result(Result(..))

import System.IO (Handle, stdin, stdout, hPutStrLn)
import System.Console.Haskeline
import System.Console.Haskeline.History
import Control.Monad.State.Strict
import Control.DeepSeq

import Util.Pretty
import Debug.Trace

prover :: Bool -> Name -> Idris ()
prover lit x =
           do ctxt <- getContext
              i <- getIState
              case lookupTy x ctxt of
                  [t] -> if elem x (map fst (idris_metavars i))
                               then prove (idris_optimisation i) ctxt lit x t
                               else ifail $ show x ++ " is not a metavariable"
                  _ -> fail "No such metavariable"

showProof :: Bool -> Name -> [String] -> String
showProof lit n ps
    = bird ++ show n ++ " = proof" ++ break ++
             showSep break (map (\x -> "  " ++ x) ps) ++
                     break ++ "\n"
  where bird = if lit then "> " else ""
        break = "\n" ++ bird

proverSettings :: ElabState EState -> Settings Idris
proverSettings e = setComplete (proverCompletion (assumptionNames e)) defaultSettings

assumptionNames :: ElabState EState -> [String]
assumptionNames e
  = case envAtFocus (proof e) of
         OK env -> names env
  where names [] = []
        names ((MN _ _, _) : bs) = names bs
        names ((n, _) : bs) = show n : names bs

prove :: Ctxt OptInfo -> Context -> Bool -> Name -> Type -> Idris ()
prove opt ctxt lit n ty
    = do let ps = initElaborator n ctxt ty
         idemodePutSExp "start-proof-mode" n
         (tm, prf) <- ploop n True ("-" ++ show n) [] (ES (ps, initEState) "" Nothing) Nothing
         iLOG $ "Adding " ++ show tm
         i <- getIState
         case idris_outputmode i of
           IdeMode _ _ -> idemodePutSExp "end-proof-mode" (n, showProof lit n prf)
           _            -> iputStrLn $ showProof lit n prf
         let proofs = proof_list i
         putIState (i { proof_list = (n, prf) : proofs })
         let tree = simpleCase False (STerm Erased) False CompileTime (fileFC "proof") [] [] [([], P Ref n ty, tm)]
         logLvl 3 (show tree)
         (ptm, pty) <- recheckC (fileFC "proof") id [] tm
         logLvl 5 ("Proof type: " ++ show pty ++ "\n" ++
                   "Expected type:" ++ show ty)
         case converts ctxt [] ty pty of
              OK _ -> return ()
              Error e -> ierror (CantUnify False (ty, Nothing) (pty, Nothing) e [] 0)
         ptm' <- applyOpts ptm
         ei <- getErasureInfo `fmap` getIState
         updateContext (addCasedef n ei (CaseInfo True True False) False (STerm Erased) True False
                                 [] []  -- argtys, inaccArgs
                                 [Right (P Ref n ty, ptm)]
                                 [([], P Ref n ty, ptm)]
                                 [([], P Ref n ty, ptm)]
                                 [([], P Ref n ty, ptm)]
                                 [([], P Ref n ty, ptm')] ty)
         solveDeferred n
         case idris_outputmode i of
           IdeMode n h ->
             runIO . hPutStrLn h $ IdeMode.convSExp "return" (IdeMode.SymbolAtom "ok", "") n
           _ -> return ()

elabStep :: ElabState EState -> ElabD a -> Idris (a, ElabState EState)
elabStep st e = case runStateT eCheck st of
                     OK (a, st') -> return (a, st')
                     Error a -> ierror a
  where eCheck = do res <- e
                    matchProblems True
                    unifyProblems
                    probs' <- get_probs
                    case probs' of
                         [] -> do tm <- get_term
                                  ctxt <- get_context
                                  lift $ check ctxt [] (forget tm)
                                  return res
                         ((_,_,_,_,e,_,_):_) -> lift $ Error e

dumpState :: IState -> ProofState -> Idris ()
dumpState ist ps | [] <- holes ps =
  do let nm = thname ps
     rendered <- iRender $ prettyName True False [] nm <> colon <+> text "No more goals."
     iputGoal rendered
dumpState ist ps | (h : hs) <- holes ps = do
  let OK ty  = goalAtFocus ps
  let OK env = envAtFocus ps
  let state = prettyOtherGoals hs <> line <>
              prettyAssumptions env <> line <>
              prettyGoal (zip (assumptionNames env) (repeat False)) ty
  rendered <- iRender state
  iputGoal rendered

  where
    (h : hs) = holes ps -- apparently the pattern guards don't give us this

    ppo = ppOptionIst ist

    tPretty bnd t = annotate (AnnTerm bnd t) .
                    pprintPTerm ppo bnd [] (idris_infixes ist) $
                    delab ist t

    assumptionNames :: Env -> [Name]
    assumptionNames = map fst

    prettyPs :: [(Name, Bool)] -> Env -> Doc OutputAnnotation
    prettyPs bnd [] = empty
    prettyPs bnd ((n@(MN _ r), _) : bs)
        | r == txt "rewrite_rule" = prettyPs ((n, False):bnd) bs
    prettyPs bnd ((n@(MN _ _), _) : bs)
        | not (n `elem` freeEnvNames bs) = prettyPs bnd bs
    prettyPs bnd ((n, Let t v) : bs) =
      line <> bindingOf n False <+> text "=" <+> tPretty bnd v <+> colon <+>
        align (tPretty bnd t) <> prettyPs ((n, False):bnd) bs
    prettyPs bnd ((n, b) : bs) =
      line <> bindingOf n False <+> colon <+>
      align (tPretty bnd (binderTy b)) <> prettyPs ((n, False):bnd) bs

    prettyG bnd (Guess t v) = tPretty bnd t <+> text "=?=" <+> tPretty bnd v
    prettyG bnd b = tPretty bnd $ binderTy b

    prettyGoal bnd ty =
      text "----------                 Goal:                  ----------" <$$>
      bindingOf h False <+> colon <+> align (prettyG bnd ty)

    prettyAssumptions env =
      if length env == 0 then
        empty
      else
        text "----------              Assumptions:              ----------" <>
        nest nestingSize (prettyPs [] $ reverse env)

    prettyOtherGoals hs =
      if length hs == 0 then
        empty
      else
        text "----------              Other goals:              ----------" <$$>
        nest nestingSize (align . cat . punctuate (text ",") . map (flip bindingOf False) $ hs)

    freeEnvNames :: Env -> [Name]
    freeEnvNames = foldl (++) [] . map (\(n, b) -> freeNames (Bind n b Erased))

lifte :: ElabState EState -> ElabD a -> Idris a
lifte st e = do (v, _) <- elabStep st e
                return v

receiveInput :: Handle -> ElabState EState -> Idris (Maybe String)
receiveInput h e =
  do i <- getIState
     let inh = if h == stdout then stdin else h
     len' <- runIO $ IdeMode.getLen inh
     len <- case len' of
       Left err -> ierror err
       Right n  -> return n
     l <- runIO $ IdeMode.getNChar inh len ""
     (sexp, id) <- case IdeMode.parseMessage l of
                     Left err -> ierror err
                     Right (sexp, id) -> return (sexp, id)
     putIState $ i { idris_outputmode = (IdeMode id h) }
     case IdeMode.sexpToCommand sexp of
       Just (IdeMode.REPLCompletions prefix) ->
         do (unused, compls) <- proverCompletion (assumptionNames e) (reverse prefix, "")
            let good = IdeMode.SexpList [IdeMode.SymbolAtom "ok", IdeMode.toSExp (map replacement compls, reverse unused)]
            idemodePutSExp "return" good
            receiveInput h e
       Just (IdeMode.Interpret cmd) -> return (Just cmd)
       Just (IdeMode.TypeOf str) -> return (Just (":t " ++ str))
       Just (IdeMode.DocsFor str _) -> return (Just (":doc " ++ str))
       _ -> return Nothing

ploop :: Name -> Bool -> String -> [String] -> ElabState EState -> Maybe History -> Idris (Term, [String])
ploop fn d prompt prf e h
    = do i <- getIState
         let autoSolve = opt_autoSolve (idris_options i)
         when d $ dumpState i (proof e)
         (x, h') <-
           case idris_outputmode i of
             RawOutput _ ->
               runInputT (proverSettings e) $
                 -- Manually track the history so that we can use the proof state
                 do case h of
                      Just history -> putHistory history
                      Nothing -> return ()
                    l <- getInputLine (prompt ++ "> ")
                    h' <- getHistory
                    return (l, Just h')
             IdeMode _ handle ->
               do isetPrompt prompt
                  i <- receiveInput handle e
                  return (i, h)
         (cmd, step) <- case x of
            Nothing -> do iPrintError ""; ifail "Abandoned"
            Just input -> do return (parseTactic i input, input)
         case cmd of
            Success Abandon -> do iPrintError ""; ifail "Abandoned"
            _ -> return ()
         (d, st, done, prf', res) <- idrisCatch
           (case cmd of
              Failure err -> return (False, e, False, prf, Left . Msg . show . fixColour (idris_colourRepl i) $ err)
              Success Undo -> do (_, st) <- elabStep e loadState
                                 return (True, st, False, init prf, Right $ iPrintResult "")
              Success ProofState -> return (True, e, False, prf, Right $ iPrintResult "")
              Success ProofTerm -> do tm <- lifte e get_term
                                      iputStrLn $ "TT: " ++ show tm ++ "\n"
                                      return (False, e, False, prf, Right $ iPrintResult "")
              Success Qed -> do hs <- lifte e get_holes
                                when (not (null hs)) $ ifail "Incomplete proof"
                                iputStrLn "Proof completed!"
                                return (False, e, True, prf, Right $ iPrintResult "")
              Success (TCheck (PRef _ n)) -> checkNameType n
              Success (TCheck t) -> checkType t
              Success (TEval t)  -> evalTerm t e
              Success (TDocStr x) -> docStr x
              Success (TSearch t) -> search t
              Success tac ->
                do (_, e) <- elabStep e saveState
                   (_, st) <- elabStep e (runTac autoSolve i (Just proverFC) fn tac)
                   return (True, st, False, prf ++ [step], Right $ iPrintResult ""))
           (\err -> return (False, e, False, prf, Left err))
         idemodePutSExp "write-proof-state" (prf', length prf')
         case res of
           Left err -> do ist <- getIState
                          iRenderError $ pprintErr ist err
                          ploop fn d prompt prf' st h'
           Right ok ->
             if done then do (tm, _) <- elabStep st get_term
                             return (tm, prf')
                     else do ok
                             ploop fn d prompt prf' st h'
  where envCtxt env ctxt = foldl (\c (n, b) -> addTyDecl n Bound (binderTy b) c) ctxt env
        checkNameType n = do
          ctxt <- getContext
          ist <- getIState
          imp <- impShow
          idrisCatch (do
              let OK env = envAtFocus (proof e)
                  ctxt'  = envCtxt env ctxt
                  bnd    = map (\x -> (fst x, False)) env
                  ist'   = ist { tt_ctxt = ctxt' }
              putIState ist'
              -- Unlike the REPL, metavars have no special treatment, to
              -- make it easier to see how to prove with them.
              let action = case lookupNames n ctxt' of
                             [] -> iPrintError $ "No such variable " ++ show n
                             ts -> iPrintFunTypes bnd n (map (\n -> (n, pprintDelabTy ist' n)) ts)
              putIState ist
              return (False, e, False, prf, Right action))
            (\err -> do putIState ist ; ierror err)

        checkType t = do
          ist <- getIState
          ctxt <- getContext
          idrisCatch (do
              let OK env = envAtFocus (proof e)
                  ctxt'  = envCtxt env ctxt
              putIState ist { tt_ctxt = ctxt' }
              (tm, ty) <- elabVal recinfo ERHS t
              let ppo = ppOptionIst ist
                  ty'     = normaliseC ctxt [] ty
                  infixes = idris_infixes ist
                  action = case tm of
                    TType _ ->
                      iPrintTermWithType (prettyImp ppo PType) type1Doc
                    _ -> let bnd = map (\x -> (fst x, False)) env in
                         iPrintTermWithType (pprintPTerm ppo bnd [] infixes (delab ist tm))
                                             (pprintPTerm ppo bnd [] infixes (delab ist ty))
              putIState ist
              return (False, e, False, prf, Right action))
            (\err -> do putIState ist { tt_ctxt = ctxt } ; ierror err)

        proverFC = FC "(prover shell)" (0, 0) (0, 0)

        evalTerm t e = withErrorReflection $
          do ctxt <- getContext
             ist <- getIState
             idrisCatch (do
               let OK env = envAtFocus (proof e)
                   ctxt'  = envCtxt env ctxt
                   ist'   = ist { tt_ctxt = ctxt' }
                   bnd    = map (\x -> (fst x, False)) env
               putIState ist'
               (tm, ty) <- elabVal recinfo ERHS t
               let tm'     = force (normaliseAll ctxt' env tm)
                   ty'     = force (normaliseAll ctxt' env ty)
                   ppo     = ppOption (idris_options ist')
                   infixes = idris_infixes ist
                   tmDoc   = pprintPTerm ppo bnd [] infixes (delab ist' tm')
                   tyDoc   = pprintPTerm ppo bnd [] infixes (delab ist' ty')
                   action  = iPrintTermWithType tmDoc tyDoc
               putIState ist
               return (False, e, False, prf, Right action))
              (\err -> do putIState ist ; ierror err)
        docStr :: Either Name Const -> Idris (Bool, ElabState EState, Bool, [String], Either Err (Idris ()))
        docStr (Left n) = do ist <- getIState
                             idrisCatch (case lookupCtxtName n (idris_docstrings ist) of
                                           [] -> return (False, e, False, prf,
                                                         Left . Msg $ "No documentation for " ++ show n)
                                           ns -> do toShow <- mapM (showDoc ist) ns
                                                    return (False,  e, False, prf,
                                                            Right $ iRenderResult (vsep toShow)))
                                        (\err -> do putIState ist ; ierror err)
               where showDoc ist (n, d) = do doc <- getDocs n FullDocs
                                             return $ pprintDocs ist doc
        docStr (Right c) = do ist <- getIState
                              return (False, e, False, prf, Right . iRenderResult $ pprintConstDocs ist c (constDocs c))
        search t = return (False, e, False, prf, Right $ searchByType [] t)

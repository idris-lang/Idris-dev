{-|
Module      : Idris.Elab.Quasiquote
Description : Code to elaborate quasiquotations.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Elab.Quasiquote (extractUnquotes) where

import Idris.AbsSyntax
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.TT


extract1 :: Int -> (PTerm -> a) -> PTerm -> Elab' aux (a, [(Name, PTerm)])
extract1 n c tm = do (tm', ex) <- extractUnquotes n tm
                     return (c tm', ex)

extract2 :: Int -> (PTerm -> PTerm -> a) -> PTerm -> PTerm -> Elab' aux (a, [(Name, PTerm)])
extract2 n c a b = do (a', ex1) <- extractUnquotes n a
                      (b', ex2) <- extractUnquotes n b
                      return (c a' b', ex1 ++ ex2)

extractTUnquotes :: Int -> PTactic -> Elab' aux (PTactic, [(Name, PTerm)])
extractTUnquotes n (Rewrite t) = extract1 n Rewrite t
extractTUnquotes n (Induction t) = extract1 n Induction t
extractTUnquotes n (LetTac name t) = extract1 n (LetTac name) t
extractTUnquotes n (LetTacTy name t1 t2) = extract2 n (LetTacTy name) t1 t2
extractTUnquotes n (Exact tm) = extract1 n Exact tm
extractTUnquotes n (Try tac1 tac2)
  = do (tac1', ex1) <- extractTUnquotes n tac1
       (tac2', ex2) <- extractTUnquotes n tac2
       return (Try tac1' tac2', ex1 ++ ex2)
extractTUnquotes n (TSeq tac1 tac2)
  = do (tac1', ex1) <- extractTUnquotes n tac1
       (tac2', ex2) <- extractTUnquotes n tac2
       return (TSeq tac1' tac2', ex1 ++ ex2)
extractTUnquotes n (ApplyTactic t) = extract1 n ApplyTactic t
extractTUnquotes n (ByReflection t) = extract1 n ByReflection t
extractTUnquotes n (Reflect t) = extract1 n Reflect t
extractTUnquotes n (GoalType s tac)
  = do (tac', ex) <- extractTUnquotes n tac
       return (GoalType s tac', ex)
extractTUnquotes n (TCheck t) = extract1 n TCheck t
extractTUnquotes n (TEval t) = extract1 n TEval t
extractTUnquotes n (Claim name t) = extract1 n (Claim name) t
extractTUnquotes n tac = return (tac, []) -- the rest don't contain PTerms, or have been desugared away

extractPArgUnquotes :: Int -> PArg -> Elab' aux (PArg, [(Name, PTerm)])
extractPArgUnquotes d (PImp p m opts n t) =
  do (t', ex) <- extractUnquotes d t
     return (PImp p m opts n t', ex)
extractPArgUnquotes d (PExp p opts n t) =
  do (t', ex) <- extractUnquotes d t
     return (PExp p opts n t', ex)
extractPArgUnquotes d (PConstraint p opts n t) =
  do (t', ex) <- extractUnquotes d t
     return (PConstraint p opts n t', ex)
extractPArgUnquotes d (PTacImplicit p opts n scpt t) =
  do (scpt', ex1) <- extractUnquotes d scpt
     (t', ex2) <- extractUnquotes d t
     return (PTacImplicit p opts n scpt' t', ex1 ++ ex2)

extractDoUnquotes :: Int -> PDo -> Elab' aux (PDo, [(Name, PTerm)])
extractDoUnquotes d (DoExp fc tm)
  = do (tm', ex) <- extractUnquotes d tm
       return (DoExp fc tm', ex)
extractDoUnquotes d (DoBind fc n nfc tm)
  = do (tm', ex) <- extractUnquotes d tm
       return (DoBind fc n nfc tm', ex)
extractDoUnquotes d (DoBindP fc t t' alts)
  = fail "Pattern-matching binds cannot be quasiquoted"
extractDoUnquotes d (DoLet  fc n nfc v b)
  = do (v', ex1) <- extractUnquotes d v
       (b', ex2) <- extractUnquotes d b
       return (DoLet fc n nfc v' b', ex1 ++ ex2)
extractDoUnquotes d (DoLetP fc t t') = fail "Pattern-matching lets cannot be quasiquoted"


extractUnquotes :: Int -> PTerm -> Elab' aux (PTerm, [(Name, PTerm)])
extractUnquotes n (PLam fc name nfc ty body)
  = do (ty', ex1) <- extractUnquotes n ty
       (body', ex2) <- extractUnquotes n body
       return (PLam fc name nfc ty' body', ex1 ++ ex2)
extractUnquotes n (PPi plicity name fc ty body)
  = do (ty', ex1) <- extractUnquotes n ty
       (body', ex2) <- extractUnquotes n body
       return (PPi plicity name fc ty' body', ex1 ++ ex2)
extractUnquotes n (PLet fc name nfc ty val body)
  = do (ty', ex1) <- extractUnquotes n ty
       (val', ex2) <- extractUnquotes n val
       (body', ex3) <- extractUnquotes n body
       return (PLet fc name nfc ty' val' body', ex1 ++ ex2 ++ ex3)
extractUnquotes n (PTyped tm ty)
  = do (tm', ex1) <- extractUnquotes n tm
       (ty', ex2) <- extractUnquotes n ty
       return (PTyped tm' ty', ex1 ++ ex2)
extractUnquotes n (PApp fc f args)
  = do (f', ex1) <- extractUnquotes n f
       args' <- mapM (extractPArgUnquotes n) args
       let (args'', exs) = unzip args'
       return (PApp fc f' args'', ex1 ++ concat exs)
extractUnquotes n (PAppBind fc f args)
  = do (f', ex1) <- extractUnquotes n f
       args' <- mapM (extractPArgUnquotes n) args
       let (args'', exs) = unzip args'
       return (PAppBind fc f' args'', ex1 ++ concat exs)
extractUnquotes n (PCase fc expr cases)
  = do (expr', ex1) <- extractUnquotes n expr
       let (pats, rhss) = unzip cases
       (pats', exs1) <- fmap unzip $ mapM (extractUnquotes n) pats
       (rhss', exs2) <- fmap unzip $ mapM (extractUnquotes n) rhss
       return (PCase fc expr' (zip pats' rhss'), ex1 ++ concat exs1 ++ concat exs2)
extractUnquotes n (PIfThenElse fc c t f)
  = do (c', ex1) <- extractUnquotes n c
       (t', ex2) <- extractUnquotes n t
       (f', ex3) <- extractUnquotes n f
       return (PIfThenElse fc c' t' f', ex1 ++ ex2 ++ ex3)
extractUnquotes n (PRewrite fc by x y z)
  = do (x', ex1) <- extractUnquotes n x
       (y', ex2) <- extractUnquotes n y
       case z of
         Just zz -> do (z', ex3) <- extractUnquotes n zz
                       return (PRewrite fc by x' y' (Just z'), ex1 ++ ex2 ++ ex3)
         Nothing -> return (PRewrite fc by x' y' Nothing, ex1 ++ ex2)
extractUnquotes n (PPair fc hls info l r)
  = do (l', ex1) <- extractUnquotes n l
       (r', ex2) <- extractUnquotes n r
       return (PPair fc hls info l' r', ex1 ++ ex2)
extractUnquotes n (PDPair fc hls info a b c)
  = do (a', ex1) <- extractUnquotes n a
       (b', ex2) <- extractUnquotes n b
       (c', ex3) <- extractUnquotes n c
       return (PDPair fc hls info a' b' c', ex1 ++ ex2 ++ ex3)
extractUnquotes n (PAlternative ms b alts)
  = do alts' <- mapM (extractUnquotes n) alts
       let (alts'', exs) = unzip alts'
       return (PAlternative ms b alts'', concat exs)
extractUnquotes n (PHidden tm)
  = do (tm', ex) <- extractUnquotes n tm
       return (PHidden tm', ex)
extractUnquotes n (PGoal fc a name b)
  = do (a', ex1) <- extractUnquotes n a
       (b', ex2) <- extractUnquotes n b
       return (PGoal fc a' name b', ex1 ++ ex2)
extractUnquotes n (PDoBlock steps)
  = do steps' <- mapM (extractDoUnquotes n) steps
       let (steps'', exs) = unzip steps'
       return (PDoBlock steps'', concat exs)
extractUnquotes n (PIdiom fc tm)
  = fmap (\(tm', ex) -> (PIdiom fc tm', ex)) $ extractUnquotes n tm
extractUnquotes n (PProof tacs)
  = do (tacs', exs) <- fmap unzip $ mapM (extractTUnquotes n) tacs
       return (PProof tacs', concat exs)
extractUnquotes n (PTactics tacs)
  = do (tacs', exs) <- fmap unzip $ mapM (extractTUnquotes n) tacs
       return (PTactics tacs', concat exs)
extractUnquotes n (PElabError err) = fail "Can't quasiquote an error"
extractUnquotes n (PCoerced tm)
  = do (tm', ex) <- extractUnquotes n tm
       return (PCoerced tm', ex)
extractUnquotes n (PDisamb ns tm)
  = do (tm', ex) <- extractUnquotes n tm
       return (PDisamb ns tm', ex)
extractUnquotes n (PUnifyLog tm)
  = fmap (\(tm', ex) -> (PUnifyLog tm', ex)) $ extractUnquotes n tm
extractUnquotes n (PNoImplicits tm)
  = fmap (\(tm', ex) -> (PNoImplicits tm', ex)) $ extractUnquotes n tm
extractUnquotes n (PQuasiquote tm goal)
  = fmap (\(tm', ex) -> (PQuasiquote tm' goal, ex)) $ extractUnquotes (n+1) tm
extractUnquotes n (PUnquote tm)
  | n == 0 = do n <- getNameFrom (sMN 0 "unquotation")
                return (PRef (fileFC "(unquote)") [] n, [(n, tm)])
  | otherwise = fmap (\(tm', ex) -> (PUnquote tm', ex)) $
                extractUnquotes (n-1) tm
extractUnquotes n (PRunElab fc tm ns)
  = fmap (\(tm', ex) -> (PRunElab fc tm' ns, ex)) $ extractUnquotes n tm
extractUnquotes n (PConstSugar fc tm)
  = extractUnquotes n tm
extractUnquotes n x = return (x, []) -- no subterms!

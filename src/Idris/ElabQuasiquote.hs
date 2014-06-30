module Idris.ElabQuasiquote (extractUnquotes) where

import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.TT
import Idris.AbsSyntax


extract1 :: (PTerm -> a) -> PTerm -> Elab' aux (a, [(Name, PTerm)])
extract1 c tm = do (tm', ex) <- extractUnquotes tm
                   return (c tm', ex)

extract2 :: (PTerm -> PTerm -> a) -> PTerm -> PTerm -> Elab' aux (a, [(Name, PTerm)])
extract2 c a b = do (a', ex1) <- extractUnquotes a
                    (b', ex2) <- extractUnquotes b
                    return (c a' b', ex1 ++ ex2)

extractTUnquotes :: PTactic -> Elab' aux (PTactic, [(Name, PTerm)])
extractTUnquotes (Rewrite t) = extract1 Rewrite t
extractTUnquotes (Induction t) = extract1 Induction t
extractTUnquotes (LetTac n t) = extract1 (LetTac n) t
extractTUnquotes (LetTacTy n t1 t2) = extract2 (LetTacTy n) t1 t2
extractTUnquotes (Exact tm) = extract1 Exact tm
extractTUnquotes (Try tac1 tac2)
  = do (tac1', ex1) <- extractTUnquotes tac1
       (tac2', ex2) <- extractTUnquotes tac2
       return (Try tac1' tac2', ex1 ++ ex2)
extractTUnquotes (TSeq tac1 tac2)
  = do (tac1', ex1) <- extractTUnquotes tac1
       (tac2', ex2) <- extractTUnquotes tac2
       return (TSeq tac1' tac2', ex1 ++ ex2)
extractTUnquotes (ApplyTactic t) = extract1 ApplyTactic t
extractTUnquotes (ByReflection t) = extract1 ByReflection t
extractTUnquotes (Reflect t) = extract1 Reflect t
extractTUnquotes (GoalType s tac)
  = do (tac', ex) <- extractTUnquotes tac
       return (GoalType s tac', ex)
extractTUnquotes (TCheck t) = extract1 TCheck t
extractTUnquotes (TEval t) = extract1 TEval t
extractTUnquotes tac = return (tac, []) -- the rest don't contain PTerms

extractPArgUnquotes :: PArg -> Elab' aux (PArg, [(Name, PTerm)])
extractPArgUnquotes (PImp p m opts n t) =
  do (t', ex) <- extractUnquotes t
     return (PImp p m opts n t', ex)
extractPArgUnquotes (PExp p opts n t) =
  do (t', ex) <- extractUnquotes t
     return (PExp p opts n t', ex)
extractPArgUnquotes (PConstraint p opts n t) =
  do (t', ex) <- extractUnquotes t
     return (PConstraint p opts n t', ex)
extractPArgUnquotes (PTacImplicit p opts n scpt t) =
  do (scpt', ex1) <- extractUnquotes scpt
     (t', ex2) <- extractUnquotes t
     return (PTacImplicit p opts n scpt' t', ex1 ++ ex2)

extractDoUnquotes :: PDo -> Elab' aux (PDo, [(Name, PTerm)])
extractDoUnquotes (DoExp fc tm)
  = do (tm', ex) <- extractUnquotes tm
       return (DoExp fc tm', ex)
extractDoUnquotes (DoBind fc n tm)
  = do (tm', ex) <- extractUnquotes tm
       return (DoBind fc n tm', ex)
extractDoUnquotes (DoBindP fc t t' alts)
  = fail "Pattern-matching binds cannot be quasiquoted"
extractDoUnquotes (DoLet  fc n v b)
  = do (v', ex1) <- extractUnquotes v
       (b', ex2) <- extractUnquotes b
       return (DoLet fc n v' b', ex1 ++ ex2)
extractDoUnquotes (DoLetP fc t t') = fail "Pattern-matching lets cannot be quasiquoted"


extractUnquotes :: PTerm -> Elab' aux (PTerm, [(Name, PTerm)])
extractUnquotes (PLam n ty body)
  = do (ty', ex1) <- extractUnquotes ty
       (body', ex2) <- extractUnquotes body
       return (PLam n ty' body', ex1 ++ ex2)
extractUnquotes (PPi  plicity n ty body)
  = do (ty', ex1) <- extractUnquotes ty
       (body', ex2) <- extractUnquotes body
       return (PPi plicity n ty' body', ex1 ++ ex2)
extractUnquotes (PLet n ty val body)
  = do (ty', ex1) <- extractUnquotes ty
       (val', ex2) <- extractUnquotes val
       (body', ex3) <- extractUnquotes body
       return (PLet n ty' val' body', ex1 ++ ex2 ++ ex3)
extractUnquotes (PTyped tm ty)
  = do (tm', ex1) <- extractUnquotes tm
       (ty', ex2) <- extractUnquotes ty
       return (PTyped tm' ty', ex1 ++ ex2)
extractUnquotes (PApp fc f args)
  = do (f', ex1) <- extractUnquotes f
       args' <- mapM extractPArgUnquotes args
       let (args'', exs) = unzip args'
       return (PApp fc f' args'', ex1 ++ concat exs)
extractUnquotes (PAppBind fc f args)
  = do (f', ex1) <- extractUnquotes f
       args' <- mapM extractPArgUnquotes args
       let (args'', exs) = unzip args'
       return (PAppBind fc f' args'', ex1 ++ concat exs)
extractUnquotes (PCase fc expr cases)
  = do (expr', ex1) <- extractUnquotes expr
       let (pats, rhss) = unzip cases
       (pats', exs1) <- fmap unzip $ mapM extractUnquotes pats
       (rhss', exs2) <- fmap unzip $ mapM extractUnquotes rhss
       return (PCase fc expr' (zip pats' rhss'), ex1 ++ concat exs1 ++ concat exs2)
extractUnquotes (PRefl fc x)
  = do (x', ex) <- extractUnquotes x
       return (PRefl fc x', ex)
extractUnquotes (PEq fc a b)
  = do (a', ex1) <- extractUnquotes a
       (b', ex2) <- extractUnquotes b
       return (PEq fc a' b', ex1 ++ ex2)
extractUnquotes (PRewrite fc x y z)
  = do (x', ex1) <- extractUnquotes x
       (y', ex2) <- extractUnquotes y
       case z of
         Just zz -> do (z', ex3) <- extractUnquotes zz
                       return (PRewrite fc x' y' (Just z'), ex1 ++ ex2 ++ ex3)
         Nothing -> return (PRewrite fc x' y' Nothing, ex1 ++ ex2)
extractUnquotes (PPair fc info l r)
  = do (l', ex1) <- extractUnquotes l
       (r', ex2) <- extractUnquotes r
       return (PPair fc info l' r', ex1 ++ ex2)
extractUnquotes (PDPair fc info a b c)
  = do (a', ex1) <- extractUnquotes a
       (b', ex2) <- extractUnquotes b
       (c', ex3) <- extractUnquotes c
       return (PDPair fc info a' b' c', ex1 ++ ex2 ++ ex3)
extractUnquotes (PAlternative b alts)
  = do alts' <- mapM extractUnquotes alts
       let (alts'', exs) = unzip alts'
       return (PAlternative b alts'', concat exs)
extractUnquotes (PHidden tm)
  = do (tm', ex) <- extractUnquotes tm
       return (PHidden tm', ex)
extractUnquotes (PGoal fc a n b)
  = do (a', ex1) <- extractUnquotes a
       (b', ex2) <- extractUnquotes b
       return (PGoal fc a' n b', ex1 ++ ex2)
extractUnquotes (PDoBlock steps)
  = do steps' <- mapM extractDoUnquotes steps
       let (steps'', exs) = unzip steps'
       return (PDoBlock steps'', concat exs)
extractUnquotes (PIdiom fc tm)
  = fmap (\(tm', ex) -> (PIdiom fc tm', ex)) $ extractUnquotes tm
extractUnquotes (PProof tacs)
  = do (tacs', exs) <- fmap unzip $ mapM extractTUnquotes tacs
       return (PProof tacs', concat exs)
extractUnquotes (PTactics tacs)
  = do (tacs', exs) <- fmap unzip $ mapM extractTUnquotes tacs
       return (PTactics tacs', concat exs)
extractUnquotes (PElabError err) = fail "Can't quasiquote an error"
extractUnquotes (PCoerced tm)
  = do (tm', ex) <- extractUnquotes tm
       return (PCoerced tm', ex)
extractUnquotes (PDisamb ns tm)
  = do (tm', ex) <- extractUnquotes tm
       return (PDisamb ns tm', ex)
extractUnquotes (PUnifyLog tm)
  = fmap (\(tm', ex) -> (PUnifyLog tm', ex)) $ extractUnquotes tm
extractUnquotes (PNoImplicits tm)
  = fmap (\(tm', ex) -> (PNoImplicits tm', ex)) $ extractUnquotes tm
extractUnquotes (PQuasiquote _ _) = fail "Nested quasiquotes not supported"
extractUnquotes (PUnquote tm) =
  do n <- getNameFrom (sMN 0 "unquotation")
     return (PRef (fileFC "(unquote)") n, [(n, tm)])
extractUnquotes x = return (x, []) -- no subterms!



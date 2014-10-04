{-# LANGUAGE PatternGuards #-}

module Idris.Transforms(transformPats, applyTransRules) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.TT

import Debug.Trace

transformPats :: IState -> [Either Term (Term, Term)] ->
                [Either Term (Term, Term)]
transformPats ist ps = map tClause ps where
  tClause (Left t) = Left t -- not a clause, leave it alone
  tClause (Right (lhs, rhs)) -- apply transforms on RHS
      = let rhs' = applyTransRules ist rhs in
            Right (lhs, rhs')

applyTransRules :: IState -> Term -> Term
applyTransRules ist tm = applyAll (idris_transforms ist) tm

applyAll :: Ctxt [(Term, Term)] -> Term -> Term
applyAll ts ap@(App f a) 
    | (P _ fn ty, args) <- unApply ap
         = case lookupCtxtExact fn ts of
                Just rules -> case applyFnRules rules ap of
                                   Just tm' -> tm'
                                   _ -> App (applyAll ts f) (applyAll ts a)
                Nothing -> App (applyAll ts f) (applyAll ts a)
applyAll ts (Bind n b sc) = Bind n (fmap (applyAll ts) b) (applyAll ts sc)
applyAll ts t = t

applyFnRules :: [(Term, Term)] -> Term -> Maybe Term
applyFnRules [] tm = Nothing
applyFnRules (r : rs) tm | Just tm' <- applyRule r tm = Just tm'
                         | otherwise = applyFnRules rs tm

applyRule :: (Term, Term) -> Term -> Maybe Term
applyRule (lhs, rhs) tm 
    | Just ms <- matchTerm lhs tm 
--          = trace ("SUCCESS " ++ show ms ++ "\n FROM\n" ++ show lhs ++
--                   "\n" ++ show rhs 
--                   ++ "\n" ++ show tm) $ 
         = Just $ depat ms rhs
    | otherwise = Nothing
  where depat ms (Bind n (PVar t) sc) 
          = case lookup n ms of
                 Just tm -> depat ms (instantiate tm sc)
                 _ -> depat ms sc -- no occurrence? Shouldn't happen
        depat ms tm = tm

matchTerm :: Term -> Term -> Maybe [(Name, Term)]
matchTerm lhs tm = matchVars [] lhs tm
   where
      matchVars acc (Bind n (PVar t) sc) tm 
           = matchVars (n : acc) (instantiate (P Bound n t) sc) tm
      matchVars acc sc tm 
          = -- trace (show acc ++ ": " ++ show (sc, tm)) $
            doMatch acc sc tm

      doMatch :: [Name] -> Term -> Term -> Maybe [(Name, Term)]
      doMatch ns (P _ n _) tm
           | n `elem` ns = return [(n, tm)]
      doMatch ns (App f a) (App f' a')
           = do fm <- doMatch ns f f'
                am <- doMatch ns a a'
                return (fm ++ am)
      doMatch ns x y | x == y = return []
                     | otherwise = Nothing



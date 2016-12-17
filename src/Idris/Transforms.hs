{-|
Module      : Idris.Transforms
Description : A collection of transformations.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE PatternGuards #-}

module Idris.Transforms(
    transformPats
  , transformPatsWith
  , applyTransRulesWith
  , applyTransRules
  ) where

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

transformPatsWith :: [(Term, Term)] -> [Either Term (Term, Term)] ->
                     [Either Term (Term, Term)]
transformPatsWith rs ps = map tClause ps where
  tClause (Left t) = Left t -- not a clause, leave it alone
  tClause (Right (lhs, rhs)) -- apply transforms on RHS
      = let rhs' = applyTransRulesWith rs rhs in
            Right (lhs, rhs')

-- | Work on explicitly named terms, so we don't have to manipulate de
-- Bruijn indices
applyTransRules :: IState -> Term -> Term
applyTransRules ist tm = finalise $ applyAll [] (idris_transforms ist) (vToP tm)

-- | Work on explicitly named terms, so we don't have to manipulate de
-- Bruijn indices
applyTransRulesWith :: [(Term, Term)] -> Term -> Term
applyTransRulesWith rules tm
   = finalise $ applyAll rules emptyContext (vToP tm)

applyAll :: [(Term, Term)] -> Ctxt [(Term, Term)] -> Term -> Term
applyAll extra ts ap@(App s f a)
    | (P _ fn ty, args) <- unApply ap
         = let rules = case lookupCtxtExact fn ts of
                            Just r -> extra ++ r
                            Nothing -> extra
               ap' = App s (applyAll extra ts f) (applyAll extra ts a) in
               case rules of
                    [] -> ap'
                    rs -> case applyFnRules rs ap of
                                   Just tm'@(App s f' a') ->
                                     App s (applyAll extra ts f')
                                           (applyAll extra ts a')
                                   Just tm' -> tm'
                                   _ -> App s (applyAll extra ts f)
                                              (applyAll extra ts a)
applyAll extra ts (Bind n b sc) = Bind n (fmap (applyAll extra ts) b)
                                         (applyAll extra ts sc)
applyAll extra ts t = t

applyFnRules :: [(Term, Term)] -> Term -> Maybe Term
applyFnRules [] tm = Nothing
applyFnRules (r : rs) tm | Just tm' <- applyRule r tm = Just tm'
                         | otherwise = applyFnRules rs tm

applyRule :: (Term, Term) -> Term -> Maybe Term
applyRule (lhs, rhs) tm
    | Just ms <- matchTerm lhs tm
--          = trace ("SUCCESS " ++ show ms ++ "\n FROM\n" ++ show lhs ++
--                   "\n" ++ show rhs
--                   ++ "\n" ++ show tm ++ " GIVES\n" ++ show (depat ms rhs)) $
          = Just $ depat ms rhs
    | otherwise = Nothing
-- ASSUMPTION: The names in the transformation rule bindings cannot occur
-- in the term being transformed.
-- (In general, this would not be true, but when we elaborate transformation
-- rules we mangle the names so that it is true. While this feels a bit
-- hacky, it's much easier to think about than mangling de Bruijn indices).
  where depat ms (Bind n (PVar _ t) sc)
          = case lookup n ms of
                 Just tm -> depat ms (subst n tm sc)
                 _ -> depat ms sc -- no occurrence? Shouldn't happen
        depat ms tm = tm

matchTerm :: Term -> Term -> Maybe [(Name, Term)]
matchTerm lhs tm = matchVars [] lhs tm
   where
      matchVars acc (Bind n (PVar _ t) sc) tm
           = matchVars (n : acc) (instantiate (P Bound n t) sc) tm
      matchVars acc sc tm
          = -- trace (show acc ++ ": " ++ show (sc, tm)) $
            doMatch acc sc tm

      doMatch :: [Name] -> Term -> Term -> Maybe [(Name, Term)]
      doMatch ns (P _ n _) tm
           | n `elem` ns = return [(n, tm)]
      doMatch ns (App _ f a) (App _ f' a')
           = do fm <- doMatch ns f f'
                am <- doMatch ns a a'
                return (fm ++ am)
      doMatch ns x y | vToP x == vToP y = return []
                     | otherwise = Nothing

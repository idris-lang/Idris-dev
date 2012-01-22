{-# LANGUAGE PatternGuards #-}

module Idris.Coverage where

import Core.TT
import Core.Evaluate
import Core.CaseTree

import Idris.AbsSyntax
import Idris.Delaborate

import Data.List
import Debug.Trace

-- Given a list of LHSs, generate a extra clauses which cover the remaining
-- cases. The ones which haven't been provided are marked 'absurd' so that the
-- checker will make sure they can't happen.

-- This will only work after the given clauses have been typechecked and the
-- names are fully explicit!

genClauses :: FC -> Name -> [Term] -> [PClause] -> Idris [PClause]
genClauses fc n xs given
   = do i <- getIState
        let lhss = map (getLHS i) xs
        let argss = transpose lhss
        let all_args = map (genAll i) argss
        logLvl 7 $ "COVERAGE of " ++ show n
        logLvl 10 $ show argss ++ "\n" ++ show all_args
        logLvl 10 $ "Original: \n" ++ 
                        showSep "\n" (map (\t -> showImp True (delab' i t True)) xs)
        let parg = case lookupCtxt Nothing n (idris_implicits i) of
                        (p : _) -> p
                        _ -> repeat (pexp Placeholder)
        let new = mnub i $ filter (noMatch i) $ mkClauses parg all_args
        logLvl 7 $ "New clauses: \n" ++ showSep "\n" (map (showImp True) new)
        return (map (\t -> PClause n t [] PImpossible []) new)
  where getLHS i term 
            | (f, args) <- unApply term = map (\t -> delab' i t True) args
            | otherwise = []

        lhsApp (PClause _ l _ _ _) = l
        lhsApp (PWith _ l _ _ _) = l

        mnub i [] = []
        mnub i (x : xs) = 
            if (any (\t -> case matchClause x t of
                                Right _ -> True
                                Left _ -> False) xs) then mnub i xs 
                                                     else x : mnub i xs

        noMatch i tm = all (\x -> case matchClause (delab' i x True) tm of
                                          Right _ -> False
                                          Left miss -> True) xs 


        mkClauses :: [PArg] -> [[PTerm]] -> [PTerm]
        mkClauses parg args
            = do args' <- mkArg args
                 let tm = PApp fc (PRef fc n) (zipWith upd args' parg)
                 return tm
          where
            mkArg :: [[PTerm]] -> [[PTerm]]
            mkArg [] = return []
            mkArg (a : as) = do a' <- a
                                as' <- mkArg as
                                return (a':as')

genAll :: IState -> [PTerm] -> [PTerm]
genAll i args = concatMap otherPats (nub args)
  where 
    otherPats :: PTerm -> [PTerm]
    otherPats o@(PRef fc n) = ops fc n [] o
    otherPats o@(PApp _ (PRef fc n) xs) = ops fc n xs o
    otherPats arg = return arg

    ops fc n xs o
        | (TyDecl c@(DCon _ arity) ty : _) <- lookupDef Nothing n (tt_ctxt i)
            = do xs' <- mapM otherPats (map getTm xs)
                 let p = PApp fc (PRef fc n) (zipWith upd xs' xs)
                 let tyn = getTy n (tt_ctxt i)
                 case lookupCtxt Nothing tyn (idris_datatypes i) of
                         (TI ns : _) -> p : map (mkPat fc) (ns \\ [n])
                         _ -> [p]
    ops fc n arg o = return o

    getTy n ctxt = case lookupTy Nothing n ctxt of
                          (t : _) -> case unApply (getRetTy t) of
                                        (P _ tyn _, _) -> tyn
                                        x -> error $ "Can't happen getTy 1 " ++ show (n, x)
                          _ -> error "Can't happen getTy 2"

    mkPat fc x = case lookupCtxt Nothing x (idris_implicits i) of
                      (pargs : _)
                         -> PApp fc (PRef fc x) (map (upd Placeholder) pargs)  
                      _ -> error "Can't happen - genAll"

upd p' p = p { getTm = p' }

-- recursive calls are well-founded if one of their argument positions is
-- always decreasing.

-- If we encounter a non-total name, we'll fail

wellFounded :: IState -> Name -> SC -> Either [Name] Bool
wellFounded i n sc = case wff [] sc of
                     RightOK smaller_args -> 
                       -- is there a number in every list?
                       -- trace (show (n, smaller_args)) $
                       case smaller_args of
                            [] -> Right True
                            (x : xs) -> let args = foldl intersect x xs in
                                            Right $ not (null args)
                     LeftErr x -> Left x 
  where
    wff :: [Name] -> SC -> EitherErr [Name] [[Int]]
    wff ns (Case n as) = do is <- mapM (wffC ns) as
                            return $ concat is
      where wffC ns (ConCase _ i ns' sc) = wff (ns ++ ns') sc
            wffC ns (ConstCase _ sc) = wff ns sc
            wffC ns (DefaultCase sc) = wff ns sc
    wff ns (STerm t) = argPos ns t
    wff ns _ = return []

    checkOK n' = case lookupTotal n' (tt_ctxt i) of
                    [Partial _] -> LeftErr [n']
                    [Total] -> RightOK ()
                    x -> RightOK ()
--     checkOK n = RightOK ()

    argPos ns ap@(App f' a')
        | (P _ f _, args) <- unApply ap 
                = if f == n then
                    do aa <- argPos ns a' 
                       return $ chkArgs 0 ns args : aa
                    else do checkOK f
                            argPos ns a'
    argPos ns (App f a) = do f' <- argPos ns f
                             a' <- argPos ns a
                             return (f' ++ a')
    argPos ns (Bind n (Let t v) sc) = do v' <- argPos ns v
                                         sc' <- argPos ns sc
                                         return (v' ++ sc')
    argPos ns (Bind n _ sc) = argPos ns sc
    argPos ns _ = return []

    chkArgs i ns [] = []
    chkArgs i ns (P _ n _ : xs) | n `elem` ns = i : chkArgs (i + 1) ns xs
    chkArgs i ns (_ : xs) = chkArgs (i+1) ns xs



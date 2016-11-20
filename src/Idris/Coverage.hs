{-|
Module      : Idris.Coverage
Description : Clause generation for coverage checking
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Coverage where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate
import Idris.Error
import Idris.Output (iWarn, iputStrLn)

import Control.Monad.State.Strict
import Data.Char
import Data.Either
import Data.List
import Data.Maybe
import Debug.Trace

-- | Generate a pattern from an 'impossible' LHS.
--
-- We need this to eliminate the pattern clauses which have been
-- provided explicitly from new clause generation.
mkPatTm :: PTerm -> Idris Term
mkPatTm t = do i <- getIState
               let timp = addImpl' True [] [] [] i t
               evalStateT (toTT (mapPT deNS timp)) 0
  where
    toTT (PRef _ _ n) = do i <- lift getIState
                           case lookupNameDef n (tt_ctxt i) of
                                [(n', TyDecl nt _)] -> return $ P nt n' Erased
                                _ -> return $ P Ref n Erased
    toTT (PApp _ t args) = do t' <- toTT t
                              args' <- mapM (toTT . getTm) args
                              return $ mkApp t' args'
    toTT (PDPair _ _ _ l _ r) = do l' <- toTT l
                                   r' <- toTT r
                                   return $ mkApp (P Ref sigmaCon Erased) [Erased, Erased, l', r']
    toTT (PPair _ _ _ l r) = do l' <- toTT l
                                r' <- toTT r
                                return $ mkApp (P Ref pairCon Erased) [Erased, Erased, l', r']
    -- For alternatives, pick the first and drop the namespaces. It doesn't
    -- really matter which is taken since matching will ignore the namespace.
    toTT (PAlternative _ _ (a : as)) = toTT a
    toTT _ = do v <- get
                put (v + 1)
                return (P Bound (sMN v "imp") Erased)

    deNS (PRef f hl (NS n _)) = PRef f hl n
    deNS t = t

-- | Given a list of LHSs, generate a extra clauses which cover the remaining
-- cases. The ones which haven't been provided are marked 'absurd' so
-- that the checker will make sure they can't happen.
--
-- This will only work after the given clauses have been typechecked and the
-- names are fully explicit!
genClauses :: FC -> Name -> [Term] -> [PTerm] -> Idris [PTerm]
genClauses fc n xs given
   = do i <- getIState
        let lhs_tms = map (\x -> flattenArgs $ delab' i x True True) xs
        -- if a placeholder was given, don't bother generating cases for it
        let lhs_tms' = zipWith mergePlaceholders lhs_tms
                          (map (stripUnmatchable i) (map flattenArgs given))
        let lhss = map pUnApply lhs_tms'
        nty <- case lookupTyExact n (tt_ctxt i) of
                    Just t -> return (normalise (tt_ctxt i) [] t)
                    _ -> fail "Can't happen - genClauses, lookupTyExact"

        let argss = transpose lhss
        let all_args = map (genAll i) (zip (genPH i nty) argss)
        logCoverage 5 $ "COVERAGE of " ++ show n
        logCoverage 5 $ "using type " ++ show nty
        logCoverage 5 $ "non-concrete args " ++ show (genPH i nty)

        logCoverage 5 $ show (lhs_tms, lhss)
        logCoverage 5 $ "Args are: " ++ show argss
        logCoverage 5 $ show (map length argss) ++ "\nAll args:\n" ++ show (map length all_args)
        logCoverage 10 $ "All args are: " ++ show all_args
        logCoverage 3 $ "Original: \n" ++
             showSep "\n" (map (\t -> showTmImpls (delab' i t True True)) xs)
        -- add an infinite supply of explicit arguments to update the possible
        -- cases for (the return type may be variadic, or function type, so
        -- there may be more case splitting that the idris_implicits record
        -- suggests)
        let parg = case lookupCtxt n (idris_implicits i) of
                        (p : _) ->
                          p ++ repeat (PExp 0 [] (sMN 0 "gcarg") Placeholder)
                        _       -> repeat (pexp Placeholder)
        let tryclauses = mkClauses parg all_args
        logCoverage 3 $ show (length tryclauses) ++ " initially to check"
        logCoverage 2 $ showSep "\n" (map (showTm i) tryclauses)

        let xsdelab = map (\x -> stripUnmatchable i (delab' i x True True)) xs
        let new = filter (noMatch i xsdelab) tryclauses
        logCoverage 2 $ show (length new) ++ " clauses to check for impossibility"
        logCoverage 4 $ "New clauses: \n" ++ showSep "\n" (map (showTm i) new)
--           ++ " from:\n" ++ showSep "\n" (map (showImp True) tryclauses)
        return new
--         return (map (\t -> PClause n t [] PImpossible []) new)
  where getLHS i term
            | (f, args) <- unApply term = map (\t -> delab' i t True True) args
            | otherwise = []

        -- if an argument has a non-concrete type (i.e. it's a function
        -- that calculates something from a previous argument) we'll also
        -- need to generate a placeholder pattern for it since it could be
        -- anything based on earlier values
        genPH :: IState -> Type -> [Bool]
        genPH ist (Bind n (Pi _ ty _) sc) = notConcrete ist ty : genPH ist sc
        genPH ist ty = []

        notConcrete ist t | (P _ n _, args) <- unApply t,
                           not (isConName n (tt_ctxt ist)) = True
        notConcrete _ _ = False

        pUnApply (PApp _ f args) = map getTm args
        pUnApply _ = []

        flattenArgs (PApp fc (PApp _ f as) as')
             = flattenArgs (PApp fc f (as ++ as'))
        flattenArgs t = t

        -- Return whether the given clause matches none of the input clauses
        -- (xs)
        noMatch i xs tm = all (\x -> case matchClause i x tm of
                                          Right ms -> False
                                          Left miss -> True) xs


        mergePlaceholders :: PTerm -> PTerm -> PTerm
        mergePlaceholders x Placeholder = Placeholder
        mergePlaceholders (PApp fc f args) (PApp fc' f' args')
            = PApp fc' f' (zipWith mergePArg args args')
           where mergePArg x y = let xtm = mergePlaceholders (getTm x) (getTm y) in
                                     x { getTm = xtm}
        mergePlaceholders x _ = x

        mkClauses :: [PArg] -> [[PTerm]] -> [PTerm]
        mkClauses parg args
            | all (== [Placeholder]) args = []
        mkClauses parg args
            = do args' <- mkArg args
                 let tm = PApp fc (PRef fc [] n) (zipWith upd args' parg)
                 return tm
          where
            mkArg :: [[PTerm]] -> [[PTerm]]
            mkArg [] = return []
            mkArg (a : as) = do a' <- a
                                as' <- mkArg as
                                return (a':as')

-- | Does this error result rule out a case as valid when coverage checking?
validCoverageCase :: Context -> Err -> Bool
validCoverageCase ctxt (CantUnify _ (topx, _) (topy, _) e _ _)
    = let topx' = normalise ctxt [] topx
          topy' = normalise ctxt [] topy in
          not (sameFam topx' topy' || not (validCoverageCase ctxt e))
  where sameFam topx topy
            = case (unApply topx, unApply topy) of
                   ((P _ x _, _), (P _ y _, _)) -> x == y
                   _ -> False
validCoverageCase ctxt (InfiniteUnify _ _ _) = False
validCoverageCase ctxt (CantConvert _ _ _) = False
validCoverageCase ctxt (At _ e) = validCoverageCase ctxt e
validCoverageCase ctxt (Elaborating _ _ _ e) = validCoverageCase ctxt e
validCoverageCase ctxt (ElaboratingArg _ _ _ e) = validCoverageCase ctxt e
validCoverageCase ctxt _ = True

-- | Check whether an error is recoverable in the sense needed for
-- coverage checking.
recoverableCoverage :: Context -> Err -> Bool
recoverableCoverage ctxt (CantUnify r (topx, _) (topy, _) e _ _)
    = let topx' = normalise ctxt [] topx
          topy' = normalise ctxt [] topy in
          r || checkRec topx' topy'
  where -- different notion of recoverable than in unification, since we
        -- have no metavars -- just looking to see if a constructor is failing
        -- to unify with a function that may be reduced later
        checkRec (App _ f a) p@(P _ _ _) = checkRec f p
        checkRec p@(P _ _ _) (App _ f a) = checkRec p f
        checkRec fa@(App _ _ _) fa'@(App _ _ _)
            | (f, as) <- unApply fa,
              (f', as') <- unApply fa'
                 = if (length as /= length as')
                      then checkRec f f'
                      else checkRec f f' && and (zipWith checkRec as as')
        checkRec (P xt x _) (P yt y _) = x == y || ntRec xt yt
        checkRec _ _ = False

        ntRec x y | Ref <- x = True
                  | Ref <- y = True
                  | (Bound, Bound) <- (x, y) = True
                  | otherwise = False -- name is different, unrecoverable
recoverableCoverage ctxt (At _ e) = recoverableCoverage ctxt e
recoverableCoverage ctxt (Elaborating _ _ _ e) = recoverableCoverage ctxt e
recoverableCoverage ctxt (ElaboratingArg _ _ _ e) = recoverableCoverage ctxt e
recoverableCoverage _ _ = False

genAll :: IState -> (Bool, [PTerm]) -> [PTerm]
genAll i (addPH, args)
   = case filter (/=Placeholder) $ fnub $ mergePHs $ fnub (concatMap otherPats (fnub args)) of
          [] -> [Placeholder]
          xs -> ph xs
  where
    -- Add a placeholder - this is to account for the case where an argument
    -- has a dependent type calculated from another argument, to make sure that
    -- all dependencies are covered. If they are, any generated case will
    -- match given cases.
    -- (Also this helps when checking, because if we eliminate the placeholder
    -- quickly then lots of other cases get ruled out fast)
    ph ts = if addPH then Placeholder : ts else ts

    -- Merge patterns with placeholders in other patterns, to ensure we've
    -- covered all possible generated cases
    -- e.g. if we have (True, _) (False, _) (_, True) (_, False)
    -- we should merge these to get (True, True), (False, False)
    -- (False, True) and (True, False)
    mergePHs :: [PTerm] -> [PTerm]
    mergePHs xs = mergePHs' xs xs

    mergePHs' [] all = []
    mergePHs' (x : xs) all = mergePH x all ++ mergePHs' xs all

    mergePH :: PTerm -> [PTerm] -> [PTerm]
    mergePH tm [] = []
    mergePH tm (x : xs)
          | Just merged <- mergePTerm tm x = merged : mergePH tm xs
          | otherwise = mergePH tm xs

    mergePTerm :: PTerm -> PTerm -> Maybe PTerm
    mergePTerm x Placeholder = Just x
    mergePTerm Placeholder x = Just x
    mergePTerm tm@(PRef fc1 hl1 n1) (PRef fc2 hl2 n2)
          | n1 == n2 = Just tm
    mergePTerm (PPair fc1 hl1 p1 x1 y1) (PPair fc2 hl2 p2 x2 y2)
          = do x <- mergePTerm x1 x2
               y <- mergePTerm y1 y2
               Just (PPair fc1 hl1 p1 x y)
    mergePTerm (PDPair fc1 hl1 p1 x1 t1 y1) (PDPair fc2 hl2 p2 x2 t2 y2)
          = do x <- mergePTerm x1 x2
               y <- mergePTerm y1 y2
               t <- mergePTerm t1 t2
               Just (PDPair fc1 hl1 p1 x t y)
    mergePTerm (PApp fc1 f1 args1) (PApp fc2 f2 args2)
          = do fm <- mergePTerm f1 f2
               margs <- mergeArgs args1 args2
               Just (PApp fc1 fm margs)
      where
        mergeArgs [] [] = Just []
        mergeArgs (a : as) (b : bs)
                  = do ma_in <- mergePTerm (getTm a) (getTm b)
                       let ma = a { getTm = ma_in }
                       mas <- mergeArgs as bs
                       Just (ma : mas)
        mergeArgs _ _ = Nothing
    mergePTerm x y | x == y = Just x
                   | otherwise = Nothing

    -- for every constant in a term (at any level) take next one to make sure
    -- that constants which are not explicitly handled are covered
    nextConst (PConstant fc c) = PConstant NoFC (nc' c)
    nextConst o = o

    nc' (I c) = I (c + 1)
    nc' (BI c) = BI (c + 1)
    nc' (Fl c) = Fl (c + 1)
    nc' (B8 c) = B8 (c + 1)
    nc' (B16 c) = B16 (c + 1)
    nc' (B32 c) = B32 (c + 1)
    nc' (B64 c) = B64 (c + 1)
    nc' (Ch c) = Ch (chr $ ord c + 1)
    nc' (Str c) = Str (c ++ "'")
    nc' o = o

    otherPats :: PTerm -> [PTerm]
    otherPats (PRef fc hl n) = ph $ ops fc n []
    otherPats (PApp _ (PRef fc hl n) xs) = ph $ ops fc n xs
    otherPats (PPair fc hls _ l r)
        = ph $ ops fc pairCon
                ([pimp (sUN "A") Placeholder True,
                  pimp (sUN "B") Placeholder True] ++
                 [pexp l, pexp r])
    otherPats (PDPair fc hls p t _ v)
        = ph $ ops fc sigmaCon
                ([pimp (sUN "a") Placeholder True,
                  pimp (sUN "P") Placeholder True] ++
                 [pexp t,pexp v])
    otherPats o@(PConstant _ c) = ph [o, nextConst o]
    otherPats arg = return Placeholder

    ops fc n xs 
        | (TyDecl c@(DCon _ arity _) ty : _) <- lookupDef n (tt_ctxt i)
            = do xs' <- mapM otherPats (map getExpTm xs)
                 let p = resugar (PApp fc (PRef fc [] n) (zipWith upd xs' xs))
                 let tyn = getTy n (tt_ctxt i)
                 case lookupCtxt tyn (idris_datatypes i) of
                         (TI ns _ _ _ _ : _) -> p : map (mkPat fc) (ns \\ [n])
                         _ -> [p]
    ops fc n arg = return Placeholder

    getExpTm (PImp _ True _ _ _) = Placeholder -- machine inferred, no point!
    getExpTm t = getTm t

    -- put it back to its original form
    resugar (PApp _ (PRef fc hl n) [_,_,t,v])
      | n == sigmaCon
        = PDPair fc [] TypeOrTerm (getTm t) Placeholder (getTm v)
    resugar (PApp _ (PRef fc hl n) [_,_,l,r])
      | n == pairCon
        = PPair fc [] IsTerm (getTm l) (getTm r)
    resugar t = t

    dropForce force (x : xs) i | i `elem` force
        = upd Placeholder x : dropForce force xs (i + 1)
    dropForce force (x : xs) i = x : dropForce force xs (i + 1)
    dropForce _ [] _ = []


    getTy n ctxt = case lookupTy n ctxt of
                          (t : _) -> case unApply (getRetTy t) of
                                        (P _ tyn _, _) -> tyn
                                        x -> error $ "Can't happen getTy 1 " ++ show (n, x)
                          _ -> error "Can't happen getTy 2"

    mkPat fc x = case lookupCtxt x (idris_implicits i) of
                      (pargs : _)
                         -> PApp fc (PRef fc [] x) (map (upd Placeholder) pargs)
                      _ -> error "Can't happen - genAll"

    fnub :: [PTerm] -> [PTerm]
    fnub xs = fnub' [] xs

    fnub' :: [PTerm] -> [PTerm] -> [PTerm]
    fnub' acc (x : xs) | x `qelem` acc = fnub' acc (filter (not.(quickEq x)) xs)
                       | otherwise = fnub' (x : acc) xs
    fnub' acc [] = acc

    -- quick check for constructor equality
    quickEq :: PTerm -> PTerm -> Bool
    quickEq (PConstant _ n) (PConstant _ n') = n == n'
    quickEq (PRef _ _ n) (PRef _ _ n') = n == n'
    quickEq (PPair _ _ _ l r) (PPair _ _ _ l' r') = quickEq l l' && quickEq r r'
    quickEq (PApp _ t as) (PApp _ t' as')
        | length as == length as'
           = quickEq t t' && and (zipWith quickEq (map getTm as) (map getTm as'))
    quickEq Placeholder Placeholder = True
    quickEq x y = False

    qelem :: PTerm -> [PTerm] -> Bool
    qelem x [] = False
    qelem x (y : ys) | x `quickEq` y = True
                     | otherwise = qelem x ys


upd :: t -> PArg' t -> PArg' t
upd p' p = p { getTm = p' }


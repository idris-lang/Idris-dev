{-|
Module      : Idris.Coverage
Description : Clause generation for coverage checking
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Coverage(genClauses, validCoverageCase, recoverableCoverage,
                      mkPatTm) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate
import Idris.Elab.Utils
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
--
-- This takes a type directed approach to disambiguating names. If we
-- can't immediately disambiguate by looking at the expected type, it's an
-- error (we can't do this the usual way of trying it to see what type checks
-- since the whole point of an impossible case is that it won't type check!)
mkPatTm :: PTerm -> Idris Term
mkPatTm t = do i <- getIState
               let timp = addImpl' True [] [] [] i t
               evalStateT (toTT Nothing timp) 0
  where
    toTT :: Maybe Type -> PTerm -> StateT Int Idris Term
    toTT ty (PRef _ _ n)
       = do i <- lift getIState
            case lookupDefExact n (tt_ctxt i) of
                 Just (TyDecl nt _) -> return $ P nt n Erased
                 _ -> return $ P Ref n Erased
    toTT ty (PApp _ t@(PRef _ _ n) args)
       = do i <- lift getIState
            let aTys = case lookupTyExact n (tt_ctxt i) of
                              Just nty -> map (Just . snd) (getArgTys nty)
                              Nothing -> map (const Nothing) args
            args' <- zipWithM toTT aTys (map getTm args)
            t' <- toTT Nothing t
            return $ mkApp t' args'
    toTT ty (PApp _ t args)
       = do t' <- toTT Nothing t
            args' <- mapM (toTT Nothing . getTm) args
            return $ mkApp t' args'
    toTT ty (PDPair _ _ _ l _ r)
       = do l' <- toTT Nothing l
            r' <- toTT Nothing r
            return $ mkApp (P Ref sigmaCon Erased) [Erased, Erased, l', r']
    toTT ty (PPair _ _ _ l r)
       = do l' <- toTT Nothing l
            r' <- toTT Nothing r
            return $ mkApp (P Ref pairCon Erased) [Erased, Erased, l', r']
    -- For alternatives, pick the first and drop the namespaces. It doesn't
    -- really matter which is taken since matching will ignore the namespace.
    toTT (Just ty) (PAlternative _ _ as)
       | (hd, _) <- unApply ty
          = do i <- lift getIState
               case pruneByType True [] hd ty i as of
                    [a] -> toTT (Just ty) a
                    _ -> lift $ ierror $ CantResolveAlts (map getAltName as)
    toTT Nothing (PAlternative _ _ as)
                    = lift $ ierror $ CantResolveAlts (map getAltName as)
    toTT ty _
       = do v <- get
            put (v + 1)
            return (P Bound (sMN v "imp") Erased)

    getAltName (PApp _ (PRef _ _ (UN l)) [_, _, arg])
             | l == txt "Delay" = getAltName (getTm arg)
    getAltName (PApp _ (PRef _ _ n) _) = n
    getAltName (PRef _ _ n) = n
    getAltName (PApp _ h _) = getAltName h
    getAltName (PHidden h) = getAltName h
    getAltName x = sUN "_" -- should never happen here

-- | Given a list of LHSs, generate a extra clauses which cover the remaining
-- cases. The ones which haven't been provided are marked 'absurd' so
-- that the checker will make sure they can't happen.
--
-- This will only work after the given clauses have been typechecked and the
-- names are fully explicit!
genClauses :: FC -> Name -> [([Name], Term)] -> -- (Argument names, LHS)
              [PTerm] -> Idris [PTerm]
-- No clauses (only valid via elab reflection). We should probably still do
-- a check here somehow, e.g. that one of the arguments is an obviously
-- empty type. In practice, this should only really be used for Void elimination.
genClauses fc n lhs_tms [] = return []
genClauses fc n lhs_tms given
   = do i <- getIState

        let lhs_given = zipWith removePlaceholders lhs_tms
                            (map (stripUnmatchable i) (map flattenArgs given))

        logCoverage 5 $ "Building coverage tree for:\n" ++ showSep "\n" (map showTmImpls given)
        logCoverage 10 $ "Building coverage tree for:\n" ++ showSep "\n" (map show lhs_given)
        logCoverage 10 $ "From terms:\n" ++ showSep "\n" (map show lhs_tms)
        let givenpos = mergePos (map getGivenPos given)

        (cns, ctree_in) <-
                         case simpleCase False (UnmatchedCase "Undefined") False
                              (CoverageCheck givenpos) emptyFC [] []
                              lhs_given
                              (const []) of
                           OK (CaseDef cns ctree_in _) ->
                              return (cns, ctree_in)
                           Error e -> tclift $ tfail $ At fc e

        let ctree = trimOverlapping (addMissingCons i ctree_in)
        let (coveredas, missingas) = mkNewClauses (tt_ctxt i) n cns ctree
        let covered = map (\t -> delab' i t True True) coveredas
        let missing = filter (\x -> x `notElem` covered) $
                          map (\t -> delab' i t True True) missingas

        logCoverage 5 $ "Coverage from case tree for " ++ show n ++ ": " ++ show ctree
        logCoverage 2 $ show (length missing) ++ " missing clauses for " ++ show n
        logCoverage 3 $ "Missing clauses:\n" ++ showSep "\n"
                              (map showTmImpls missing)
        logCoverage 10 $ "Covered clauses:\n" ++ showSep "\n"
                              (map showTmImpls covered)
        return missing
    where
        flattenArgs (PApp fc (PApp _ f as) as')
             = flattenArgs (PApp fc f (as ++ as'))
        flattenArgs t = t

getGivenPos :: PTerm -> [Int]
getGivenPos (PApp _ _ pargs) = getGiven 0 (map getTm pargs)
  where
    getGiven i (Placeholder : tms) = getGiven (i + 1) tms
    getGiven i (_ : tms) = i : getGiven (i + 1) tms
    getGiven i [] = []
getGivenPos _ = []

-- Return a list of Ints which are in every list
mergePos :: [[Int]] -> [Int]
mergePos [] = []
mergePos [x] = x
mergePos (x : xs) = intersect x (mergePos xs)

removePlaceholders :: ([Name], Term) -> PTerm -> ([Name], Term, Term)
removePlaceholders (ns, tm) ptm = (ns, rp tm ptm, Erased)
  where
    rp Erased Placeholder = Erased
    rp tm Placeholder = Inferred tm
    rp tm (PApp _ pf pargs)
       | (tf, targs) <- unApply tm
           = let tf' = rp tf pf
                 targs' = zipWith rp targs (map getTm pargs) in
                 mkApp tf' targs'
    rp tm (PPair _ _ _ pl pr)
       | (tf, [tyl, tyr, tl, tr]) <- unApply tm
           = let tl' = rp tl pl
                 tr' = rp tr pr in
                 mkApp tf [Erased, Erased, tl', tr']
    rp tm (PDPair _ _ _ pl pt pr)
       | (tf, [tyl, tyr, tl, tr]) <- unApply tm
           = let tl' = rp tl pl
                 tr' = rp tr pr in
                 mkApp tf [Erased, Erased, tl', tr']
    rp tm _ = tm

mkNewClauses :: Context -> Name -> [Name] -> SC -> ([Term], [Term])
mkNewClauses ctxt fn ns sc
     = (map (mkPlApp (P Ref fn Erased)) $
            mkFromSC True (map (\n -> P Ref n Erased) ns) sc,
        map (mkPlApp (P Ref fn Erased)) $
            mkFromSC False (map (\n -> P Ref n Erased) ns) sc)
  where
    mkPlApp f args = mkApp f (map erasePs args)

    erasePs ap@(App t f a)
        | (f, args) <- unApply ap = mkApp f (map erasePs args)
    erasePs (P _ n _) | not (isConName n ctxt) = Erased
    erasePs tm = tm

    mkFromSC cov args sc = evalState (mkFromSC' cov args sc) []

    mkFromSC' :: Bool -> [Term] -> SC -> State [[Term]] [[Term]]
    mkFromSC' cov args (STerm _)
        = if cov then return [args] else return [] -- leaf of provided case
    mkFromSC' cov args (UnmatchedCase _)
        = if cov then return [] else return [args] -- leaf of missing case
    mkFromSC' cov args ImpossibleCase = return []
    mkFromSC' cov args (Case _ x alts)
       = do done <- get
            if (args `elem` done)
               then return []
               else do alts' <- mapM (mkFromAlt cov args x) alts
                       put (args : done)
                       return (concat alts')
    mkFromSC' cov args _ = return [] -- Should never happen

    mkFromAlt :: Bool -> [Term] -> Name -> CaseAlt -> State [[Term]] [[Term]]
    mkFromAlt cov args x (ConCase c t conargs sc)
       = let argrep = mkApp (P (DCon t (length args) False) c Erased)
                            (map (\n -> P Ref n Erased) conargs)
             args' = map (subst x argrep) args in
             mkFromSC' cov args' sc
    mkFromAlt cov args x (ConstCase c sc)
       = let argrep = Constant c
             args' = map (subst x argrep) args in
             mkFromSC' cov args' sc
    mkFromAlt cov args x (DefaultCase sc)
       = mkFromSC' cov args sc
    mkFromAlt cov _ _ _ = return []

-- Modify the generated case tree (the case tree builder doesn't have access
-- to the context, so can't do this itself).
-- Replaces any missing cases with explicit cases for the missing constructors
addMissingCons :: IState -> SC -> SC
addMissingCons ist sc = evalState (addMissingConsSt ist sc) 0

addMissingConsSt :: IState -> SC -> State Int SC
addMissingConsSt ist (Case t n alts) = liftM (Case t n) (addMissingAlts n alts)
  where
    addMissingAlt :: CaseAlt -> State Int CaseAlt
    addMissingAlt (ConCase n i ns sc)
         = liftM (ConCase n i ns) (addMissingConsSt ist sc)
    addMissingAlt (FnCase n ns sc)
         = liftM (FnCase n ns) (addMissingConsSt ist sc)
    addMissingAlt (ConstCase c sc)
         = liftM (ConstCase c) (addMissingConsSt ist sc)
    addMissingAlt (SucCase n sc)
         = liftM (SucCase n) (addMissingConsSt ist sc)
    addMissingAlt (DefaultCase sc)
         = liftM DefaultCase (addMissingConsSt ist sc)

    addMissingAlts argn as
--          | any hasDefault as = map addMissingAlt as
         | cons@(n:_) <- mapMaybe collectCons as,
           Just tyn <- getConType n,
           Just ti <- lookupCtxtExact tyn (idris_datatypes ist)
             -- If we've fallen through on this argument earlier, then the
             -- things which were matched in other cases earlier can't be missing
             -- cases now
             = let missing = con_names ti \\ cons in
                   do as' <- addCases missing as
                      mapM addMissingAlt as'
         | consts@(n:_) <- mapMaybe collectConsts as
             = let missing = nub (map nextConst consts) \\ consts in
                   mapM addMissingAlt (addCons missing as)
    addMissingAlts n as = mapM addMissingAlt as

    addCases missing [] = return []
    addCases missing (DefaultCase rhs : rest)
       = do missing' <- mapM (genMissingAlt rhs) missing
            return (mapMaybe id missing' ++ rest)
    addCases missing (c : rest)
       = liftM (c :) $ addCases missing rest

    addCons missing [] = []
    addCons missing (DefaultCase rhs : rest)
       = map (genMissingConAlt rhs) missing ++ rest
    addCons missing (c : rest) = c : addCons missing rest

    genMissingAlt rhs n
         | Just (TyDecl (DCon tag arity _) ty) <- lookupDefExact n (tt_ctxt ist)
             = do name <- get
                  put (name + arity)
                  let args = map (name +) [0..arity-1]
                  return $ Just $ ConCase n tag (map (\i -> sMN i "m") args) rhs
         | otherwise = return Nothing

    genMissingConAlt rhs n = ConstCase n rhs

    collectCons (ConCase n i args sc) = Just n
    collectCons _ = Nothing

    collectConsts (ConstCase c sc) = Just c
    collectConsts _ = Nothing

    hasDefault (DefaultCase (UnmatchedCase _)) = False
    hasDefault (DefaultCase _) = True
    hasDefault _ = False

    getConType n = do ty <- lookupTyExact n (tt_ctxt ist)
                      case unApply (getRetTy (normalise (tt_ctxt ist) [] ty)) of
                           (P _ tyn _, _) -> Just tyn
                           _ -> Nothing

    -- for every constant in a term (at any level) take next one to make sure
    -- that constants which are not explicitly handled are covered
    nextConst (I c) = I (c + 1)
    nextConst (BI c) = BI (c + 1)
    nextConst (Fl c) = Fl (c + 1)
    nextConst (B8 c) = B8 (c + 1)
    nextConst (B16 c) = B16 (c + 1)
    nextConst (B32 c) = B32 (c + 1)
    nextConst (B64 c) = B64 (c + 1)
    nextConst (Ch c) = Ch (chr $ ord c + 1)
    nextConst (Str c) = Str (c ++ "'")
    nextConst o = o

addMissingConsSt ist sc = return sc

trimOverlapping :: SC -> SC
trimOverlapping sc = trim [] [] sc
  where
    trim :: [(Name, (Name, [Name]))] -> -- Variable - constructor+args already matched
            [(Name, [Name])] -> -- Variable - constructors which it can't be
            SC -> SC
    trim mustbes nots (Case t vn alts)
       | Just (c, args) <- lookup vn mustbes
            = Case t vn (trimAlts mustbes nots vn (substMatch (c, args) alts))
       | Just cantbe <- lookup vn nots
            = let alts' = filter (notConMatch cantbe) alts in
                  Case t vn (trimAlts mustbes nots vn alts')
       | otherwise = Case t vn (trimAlts mustbes nots vn alts)
    trim cs nots sc = sc

    trimAlts cs nots vn [] = []
    trimAlts cs nots vn (ConCase cn t args sc : rest)
        = ConCase cn t args (trim (addMatch vn (cn, args) cs) nots sc) :
            trimAlts cs (addCantBe vn cn nots) vn rest
    trimAlts cs nots vn (FnCase n ns sc : rest)
        = FnCase n ns (trim cs nots sc) : trimAlts cs nots vn rest
    trimAlts cs nots vn (ConstCase c sc : rest)
        = ConstCase c (trim cs nots sc) : trimAlts cs nots vn rest
    trimAlts cs nots vn (SucCase n sc : rest)
        = SucCase n (trim cs nots sc) : trimAlts cs nots vn rest
    trimAlts cs nots vn (DefaultCase sc : rest)
        = DefaultCase (trim cs nots sc) : trimAlts cs nots vn rest

    isConMatch c (ConCase cn t args sc) = c == cn
    isConMatch _ _ = False

    substMatch :: (Name, [Name]) -> [CaseAlt] -> [CaseAlt]
    substMatch ca [] = []
    substMatch (c,args) (ConCase cn t args' sc : _)
        | c == cn = [ConCase c t args (substNames (zip args' args) sc)]
    substMatch ca (_:cs) = substMatch ca cs

    substNames [] sc = sc
    substNames ((n, n') : ns) sc
       = substNames ns (substSC n n' sc)

    notConMatch cs (ConCase cn t args sc) = cn `notElem` cs
    notConMatch cs _ = True

    addMatch vn cn cs = (vn, cn) : cs

    addCantBe :: Name -> Name -> [(Name, [Name])] -> [(Name, [Name])]
    addCantBe vn cn [] = [(vn, [cn])]
    addCantBe vn cn ((n, cbs) : nots)
          | vn == n = ((n, nub (cn : cbs)) : nots)
          | otherwise = ((n, cbs) : addCantBe vn cn nots)

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
validCoverageCase ctxt (CantConvert topx topy _)
    = let topx' = normalise ctxt [] topx
          topy' = normalise ctxt [] topy in
          not (sameFam topx' topy')
  where sameFam topx topy
            = case (unApply topx, unApply topy) of
                   ((P _ x _, _), (P _ y _, _)) -> x == y
                   _ -> False
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
          evalState (checkRec topx' topy') []
recoverableCoverage ctxt (CantConvert topx topy _)
    = let topx' = normalise ctxt [] topx
          topy' = normalise ctxt [] topy in
          evalState (checkRec topx' topy') []
recoverableCoverage ctxt (InfiniteUnify _ _ _) = False -- always unrecoverable
recoverableCoverage ctxt (At _ e) = recoverableCoverage ctxt e
recoverableCoverage ctxt (Elaborating _ _ _ e) = recoverableCoverage ctxt e
recoverableCoverage ctxt (ElaboratingArg _ _ _ e) = recoverableCoverage ctxt e
recoverableCoverage _ _ = False

-- different notion of recoverable than in unification, since we
-- have no metavars -- just looking to see if a constructor is failing
-- to unify with a function that may be reduced later, or if any
-- variables need to have two different constructor forms

-- The state is a mapping of name to what it has failed to unify
-- with
checkRec :: Term -> Term -> State [(Name, Term)] Bool
checkRec (P Bound x _) tm
   | (P yt _ _, _) <- unApply tm,
     conType yt = do nmap <- get
                     case lookup x nmap of
                          Nothing -> do put ((x, tm) : nmap)
                                        return True
                          Just y' -> checkRec tm y'
 where
   conType (DCon _ _ _) = True
   conType (TCon _ _) = True
   conType _ = False

checkRec tm (P Bound y _)
   | (P xt _ _, _) <- unApply tm,
     conType xt = do nmap <- get
                     case lookup y nmap of
                          Nothing -> do put ((y, tm) : nmap)
                                        return True
                          Just x' -> checkRec tm x'
 where
   conType (DCon _ _ _) = True
   conType (TCon _ _) = True
   conType _ = False

checkRec (App _ f a) p@(P _ _ _) = checkRec f p
checkRec p@(P _ _ _) (App _ f a) = checkRec p f
checkRec fa@(App _ _ _) fa'@(App _ _ _)
    | (f, as) <- unApply fa,
      (f', as') <- unApply fa'
         = if (length as /= length as')
              then checkRec f f'
              -- Same function but different args is recoverable,
              -- and vice versa, if it's an ordinary function
              -- If a constructor, everything has to be recoverable
              else do fok <- checkRec f f'
                      argok <- checkRecs (f : as) (f : as')
                      return (if conType f then fok && argok
                                           else fok || argok)
  where
    checkRecs [] [] = return True
    checkRecs (a : as) (b : bs) = do aok <- checkRec a b
                                     asok <- checkRecs as bs
                                     return (aok && asok)
    conType (P (DCon _ _ _) _ _) = True
    conType (P (TCon _ _) _ _) = True
    conType _ = False

checkRec (P xt x _) (P yt y _)
   | x == y = return True
   | ntRec xt yt = return True
 where
    -- If either name is a reference or a bound variable, then further
    -- development may fix the error, so consider it recoverable.
    -- If both names are constructors, and the name is different, then
    -- it's not recoverable
    ntRec x y | Ref <- x = True
              | Ref <- y = True
              | Bound <- x = True
              | Bound <- y = True
              | otherwise = False -- name is different, unrecoverable
checkRec _ _ = return False

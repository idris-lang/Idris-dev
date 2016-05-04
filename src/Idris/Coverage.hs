{-# LANGUAGE PatternGuards #-}
{-| The coverage and totality checkers for Idris are in this module.
-}
module Idris.Coverage where

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.CaseTree

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Error
import Idris.Output (iWarn, iputStrLn)

import Data.List
import Data.Either
import Data.Maybe
import Debug.Trace

import Control.Monad.State.Strict

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
        logCoverage 5 $ show (map length argss) ++ "\n" ++ show (map length all_args)
        logCoverage 10 $ show argss ++ "\n" ++ show all_args
        logCoverage 3 $ "Original: \n" ++
             showSep "\n" (map (\t -> showTm i (delab' i t True True)) xs)
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
        let new = filter (noMatch i) (nub tryclauses)
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
        noMatch i tm = all (\x -> case matchClause i (stripUnmatchable i (delab' i x True True)) tm of
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
   = case filter (/=Placeholder) $ fnub (concatMap otherPats (fnub args)) of
          [] -> [Placeholder]
          xs -> ph $ inventConsts xs
  where
    ph ts = if addPH then Placeholder : ts else ts

    -- if they're constants, invent a new one to make sure that
    -- constants which are not explicitly handled are covered
    inventConsts cs@(PConstant fc c : _) = map (PConstant NoFC) (ic' (mapMaybe getConst cs))
      where getConst (PConstant _ c) = Just c
            getConst _ = Nothing
    inventConsts xs = xs

    -- try constants until they're not in the list.
    -- FIXME: It is, of course, possible that someone has enumerated all
    -- the constants and matched on them (maybe in generated code) and this
    -- will be really slow. This is sufficiently unlikely that we won't
    -- worry for now...

    ic' xs@(I _ : _) = firstMissing xs (lotsOfNums I)
    ic' xs@(BI _ : _) = firstMissing xs (lotsOfNums BI)
    ic' xs@(Fl _ : _) = firstMissing xs (lotsOfNums Fl)
    ic' xs@(B8 _ : _) = firstMissing xs (lotsOfNums B8)
    ic' xs@(B16 _ : _) = firstMissing xs (lotsOfNums B16)
    ic' xs@(B32 _ : _) = firstMissing xs (lotsOfNums B32)
    ic' xs@(B64 _ : _) = firstMissing xs (lotsOfNums B64)
    ic' xs@(Ch _ : _) = firstMissing xs lotsOfChars
    ic' xs@(Str _ : _) = firstMissing xs lotsOfStrings
    -- The rest are types with only one case
    ic' xs = xs

    firstMissing cs (x : xs) | x `elem` cs = firstMissing cs xs
                             | otherwise = x : cs

    lotsOfNums t = map t [0..]
    lotsOfChars = map Ch ['a'..]
    lotsOfStrings = map Str (map (("some string " ++).show) [1..])

    nubMap f acc [] = acc
    nubMap f acc (x : xs) = nubMap f (fnub' acc (f x)) xs

    otherPats :: PTerm -> [PTerm]
    otherPats o@(PRef fc hl n) = ph $ ops fc n [] o
    otherPats o@(PApp _ (PRef fc hl n) xs) = ph $ ops fc n xs o
    otherPats o@(PPair fc hls _ l r)
        = ph $ ops fc pairCon
                ([pimp (sUN "A") Placeholder True,
                  pimp (sUN "B") Placeholder True] ++
                 [pexp l, pexp r]) o
    otherPats o@(PDPair fc hls p t _ v)
        = ph $ ops fc sigmaCon
                ([pimp (sUN "a") Placeholder True,
                  pimp (sUN "P") Placeholder True] ++
                 [pexp t,pexp v]) o
    otherPats o@(PConstant _ c) = ph $ inventConsts [o] -- return o
    otherPats arg = return Placeholder

    ops fc n xs o
        | (TyDecl c@(DCon _ arity _) ty : _) <- lookupDef n (tt_ctxt i)
            = do xs' <- mapM otherPats (map getExpTm xs)
                 let p = resugar (PApp fc (PRef fc [] n) (zipWith upd xs' xs))
                 let tyn = getTy n (tt_ctxt i)
                 case lookupCtxt tyn (idris_datatypes i) of
                         (TI ns _ _ _ _ : _) -> p : map (mkPat fc) (ns \\ [n])
                         _ -> [p]
    ops fc n arg o = return Placeholder

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

-- Check whether function and all descendants cover all cases (partial is
-- okay, as long as it's due to recursion)

checkAllCovering :: FC -> [Name] -> Name -> Name -> Idris ()
checkAllCovering fc done top n | not (n `elem` done)
   = do i <- get
        case lookupTotal n (tt_ctxt i) of
             [tot@(Partial NotCovering)] ->
                    do let msg = show top ++ " is " ++ show tot ++ " due to " ++ show n
                       putIState i { idris_totcheckfail = (fc, msg) : idris_totcheckfail i }
                       addIBC (IBCTotCheckErr fc msg)
             [Partial _] ->
                case lookupCtxt n (idris_callgraph i) of
                     [cg] -> mapM_ (checkAllCovering fc (n : done) top)
                                   (calls cg)
                     _ -> return ()
             x -> return () -- stop if total
checkAllCovering _ _ _ _ = return ()

-- | Check if, in a given group of type declarations mut_ns,
-- the constructor cn : ty is strictly positive,
-- and update the context accordingly
checkPositive :: [Name] -- ^ the group of type declarations
              -> (Name, Type) -- ^ the constructor
              -> Idris Totality
checkPositive mut_ns (cn, ty')
    = do i <- getIState
         let ty = delazy' True (normalise (tt_ctxt i) [] ty')
         let p = cp ty
         let tot = if p then Total (args ty) else Partial NotPositive
         let ctxt' = setTotal cn tot (tt_ctxt i)
         putIState (i { tt_ctxt = ctxt' })
         logCoverage 5 $ "Constructor " ++ show cn ++ " is " ++ show tot ++ " with " ++ show mut_ns
         addIBC (IBCTotal cn tot)
         return tot
  where
    args t = [0..length (getArgTys t)-1]

    cp (Bind n (Pi _ aty _) sc) = posArg aty && cp sc
    cp t | (P _ n' _, args) <- unApply t,
           n' `elem` mut_ns = all noRec args
    cp _ = True

    posArg (Bind _ (Pi _ nty _) sc)
        | (P _ n' _, args) <- unApply nty
            = n' `notElem` mut_ns && all noRec args && posArg sc
    posArg t | (P _ n' _, args) <- unApply t,
               n' `elem` mut_ns = all noRec args
    posArg _ = True

    noRec arg = all (\x -> x `notElem` mut_ns) (allTTNames arg)


-- | Calculate the totality of a function from its patterns.
-- Either follow the size change graph (if inductive) or check for
-- productivity (if coinductive)
calcTotality :: FC -> Name -> [([Name], Term, Term)] -> Idris Totality
calcTotality fc n pats
    = do i <- getIState
         let opts = case lookupCtxt n (idris_flags i) of
                            [fs] -> fs
                            _ -> []
         case mapMaybe (checkLHS i) (map (\ (_, l, r) -> l) pats) of
            (failure : _) -> return failure
            _ -> checkSizeChange n
  where
    checkLHS i (P _ fn _)
        = case lookupTotalExact fn (tt_ctxt i) of
               Just (Partial _) -> return (Partial (Other [fn]))
               _ -> Nothing
    checkLHS i (App _ f a) = mplus (checkLHS i f) (checkLHS i a)
    checkLHS _ _ = Nothing

checkTotality :: [Name] -> FC -> Name -> Idris Totality
checkTotality path fc n
    | n `elem` path = return (Partial (Mutual (n : path)))
    | otherwise = do
        t <- getTotality n
        i <- getIState
        ctxt' <- do ctxt <- getContext
                    tclift $ simplifyCasedef n (getErasureInfo i) ctxt
        setContext ctxt'
        ctxt <- getContext
        i <- getIState
        let opts = case lookupCtxt n (idris_flags i) of
                            [fs] -> fs
                            _ -> []
        t' <- case t of
                Unchecked ->
                    case lookupDef n ctxt of
                        [CaseOp _ _ _ _ pats _] ->
                            do t' <- if AssertTotal `elem` opts
                                        then return $ Total []
                                        else calcTotality fc n pats
                               logCoverage 2 $ "Set to " ++ show t'
                               setTotality n t'
                               addIBC (IBCTotal n t')
                               return t'
                        [TyDecl (DCon _ _ _) ty] ->
                            case unApply (getRetTy ty) of
                              (P _ tyn _, _) -> do
                                 let ms = case lookupCtxt tyn (idris_datatypes i) of
                                       [TI _ _ _ _ xs@(_:_)] -> xs
                                       ts -> [tyn]
                                 checkPositive ms (n, ty)
                              _-> return $ Total []
                        _ -> return $ Total []
                x -> return x
        case t' of
            Total _ -> return t'
            Productive -> return t'
            e -> do w <- cmdOptType WarnPartial
                    if TotalFn `elem` opts
                       then do totalityError t'; return t'
                       else do when (w && not (PartialFn `elem` opts)) $
                                   warnPartial n t'
                               return t'
  where
    totalityError t = do i <- getIState
                         let msg = show n ++ " is " ++ show t
                         putIState i { idris_totcheckfail = (fc, msg) : idris_totcheckfail i}
                         addIBC (IBCTotCheckErr fc msg)

    warnPartial n t
       = do i <- getIState
            case lookupDef n (tt_ctxt i) of
               [x] -> do
                  iWarn fc . pprintErr i . Msg $ "Warning - " ++ show n ++ " is " ++ show t
--                                ++ "\n" ++ show x
--                   let cg = lookupCtxtName Nothing n (idris_callgraph i)
--                   iputStrLn (show cg)


checkDeclTotality :: (FC, Name) -> Idris Totality
checkDeclTotality (fc, n)
    = do logCoverage 2 $ "Checking " ++ show n ++ " for totality"
--          buildSCG (fc, n)
--          logCoverage 2 $ "Built SCG"
         i <- getIState
         let opts = case lookupCtxt n (idris_flags i) of
                              [fs] -> fs
                              _ -> []
         when (CoveringFn `elem` opts) $ checkAllCovering fc [] n n
         t <- checkTotality [] fc n
         return t


-- | Calculate the size change graph for this definition
--
-- SCG for a function f consists of a list of:
--    (g, [(a1, sizechange1), (a2, sizechange2), ..., (an, sizechangen)])
--
-- where g is a function called
-- a1 ... an are the arguments of f in positions 1..n of g
-- sizechange1 ... sizechange2 is how their size has changed wrt the input
-- to f
--    Nothing, if the argument is unrelated to the input
buildSCG :: (FC, Name) -> Idris ()
buildSCG (_, n) = do
   ist <- getIState
   case lookupCtxt n (idris_callgraph ist) of
       [cg] -> case lookupDefExact n (tt_ctxt ist) of
           Just (CaseOp _ _ _ pats _ cd) ->
             let (args, sc) = cases_totcheck cd in
               do logCoverage 2 $ "Building SCG for " ++ show n ++ " from\n"
                                ++ show pats ++ "\n" ++ show sc
                  let newscg = buildSCG' ist n (rights pats) args
                  logCoverage 5 $ "SCG is: " ++ show newscg
                  addToCG n ( cg { scg = newscg } )
           _ -> return () -- CG comes from a type declaration only
       [] -> logCoverage 5 $ "Could not build SCG for " ++ show n ++ "\n"
       x -> error $ "buildSCG: " ++ show (n, x)

delazy = delazy' False -- not lazy codata
delazy' all t@(App _ f a)
     | (P _ (UN l) _, [_, _, arg]) <- unApply t,
       l == txt "Force" = delazy' all arg
     | (P _ (UN l) _, [P _ (UN lty) _, _, arg]) <- unApply t,
       l == txt "Delay" && (all || lty == txt "LazyEval") = delazy arg
     | (P _ (UN l) _, [P _ (UN lty) _, arg]) <- unApply t,
       l == txt "Lazy'" && (all || lty == txt "LazyEval") = delazy' all arg
delazy' all (App s f a) = App s (delazy' all f) (delazy' all a)
delazy' all (Bind n b sc) = Bind n (fmap (delazy' all) b) (delazy' all sc)
delazy' all t = t

data Guardedness = Toplevel | Unguarded | Guarded | Delayed
  deriving Show

buildSCG' :: IState -> Name -> [(Term, Term)] -> [Name] -> [SCGEntry]
buildSCG' ist topfn pats args = nub $ concatMap scgPat pats where
  scgPat (lhs, rhs) = let lhs' = delazy lhs
                          rhs' = delazy rhs
                          (f, pargs) = unApply (dePat lhs') in
                            findCalls [] Toplevel (dePat rhs') (patvars lhs') 
                                      (zip pargs [0..])

  findCalls cases Delayed ap@(P _ n _) pvs args
     | n == topfn = []
  findCalls cases guarded ap@(App _ f a) pvs pargs
     -- under a call to "assert_total", don't do any checking, just believe
     -- that it is total.
     | (P _ (UN at) _, [_, _]) <- unApply ap,
       at == txt "assert_total" = []
     -- under a guarded call to "Delay LazyCodata", we are 'Delayed', so don't
     -- check under guarded constructors.
     | (P _ (UN del) _, [_,_,arg]) <- unApply ap,
       Guarded <- guarded,
       del == txt "Delay" 
           = findCalls cases Delayed arg pvs pargs
     | (P _ n _, args) <- unApply ap,
       Delayed <- guarded,
       n == topfn -- Under a delayed recursive call to the top level function,
                  -- just check the arguments
           = concatMap (\x -> findCalls cases Unguarded x pvs pargs) args
     | (P _ n _, args) <- unApply ap,
       Delayed <- guarded,
       isConName n (tt_ctxt ist)
           = -- Still under a 'Delay' and constructor guarded, so check 
             -- just the arguments to the constructor, remaining Delayed
             concatMap (\x -> findCalls cases guarded x pvs pargs) args
     | (P _ n _, args) <- unApply ap,
       caseName n && n /= topfn,
       notPartial (lookupTotalExact n (tt_ctxt ist))
       -- case block - look inside the block, as long as it was covering
       -- (i.e. not currently set at Partial) to get a more accurate size
       -- change result from the top level patterns (also to help pass
       -- information through from guarded corecursion accurately)
       = concatMap (\x -> findCalls cases Unguarded x pvs pargs) args ++
             if n `notElem` cases
                then findCallsCase (n : cases) guarded n args pvs pargs
                else []
     | (P _ n _, args) <- unApply ap
        -- Ordinary call, not under a delay. 
        -- If n is a constructor, set 'args' as Guarded
        = let nguarded = case guarded of
                              Unguarded -> Unguarded
                              x -> if isConName n (tt_ctxt ist)
                                      then Guarded
                                      else Unguarded in
              mkChange n args pargs ++
                 concatMap (\x -> findCalls cases nguarded x pvs pargs) args
    where notPartial (Just (Partial NotCovering)) = False
          notPartial _ = True
  findCalls cases guarded (App _ f a) pvs pargs
        = findCalls cases Unguarded f pvs pargs ++ findCalls cases Unguarded a pvs pargs
  findCalls cases guarded (Bind n (Let t v) e) pvs pargs
        = findCalls cases Unguarded t pvs pargs ++
          findCalls cases Unguarded v pvs pargs ++ findCalls cases guarded e (n : pvs) pargs
  findCalls cases guarded (Bind n t e) pvs pargs
        = findCalls cases Unguarded (binderTy t) pvs pargs ++
          findCalls cases guarded e (n : pvs) pargs
  findCalls cases guarded (P _ f _ ) pvs pargs
      | not (f `elem` pvs) = [(f, [])]
  findCalls _ _ _ _ _ = []

  -- Assumption is that names are preserved in the case block (shadowing
  -- dealt with by the elaborator) so we can just assume the top level names
  -- are okay for building the size change
  findCallsCase cases guarded n args pvs pargs
      = case lookupDefExact n (tt_ctxt ist) of
           Just (CaseOp _ _ _ pats _ cd) -> 
                concatMap (fccPat cases pvs pargs args guarded) (rights pats)
           Nothing -> []

  fccPat cases pvs pargs args g (lhs, rhs) 
      = let lhs' = delazy lhs
            rhs' = delazy rhs
            (f, pargs_case) = unApply (dePat lhs') 
            -- pargs is a pair of a term, and the argument position that
            -- term appears in. If any of the arguments to the case block
            -- are also on the lhs, we also want those patterns to appear
            -- in the parg list so that we'll spot patterns which are
            -- smaller than then
            newpargs = newPArg args pargs 
            -- Now need to update the rhs of the case with the names in the
            -- outer definition: In rhs', wherever we see what's in pargs_case,
            -- replace it with the corresponding thing in pargs
            csubs = zip pargs_case args
            newrhs = doCaseSubs csubs (dePat rhs')
            pargs' = pargs ++ addPArg newpargs pargs_case in
               findCalls cases g newrhs pvs pargs'
    where
      doCaseSubs [] tm = tm
      doCaseSubs ((x, x') : cs) tm 
           = doCaseSubs (subIn x x' cs) (substTerm x x' tm)
      
      subIn x x' [] = []
      subIn x x' ((l, r) : cs) 
          = (substTerm x x' l, substTerm x x' r) : subIn x x' cs

  addPArg (Just (t, i) : ts) (t' : ts') = (t', i) : addPArg ts ts'
  addPArg (Nothing : ts) (t' : ts') = addPArg ts ts'
  addPArg _ _ = []

  newPArg :: [Term] -> [(Term, Int)] -> [Maybe (Term, Int)]
  newPArg (t : ts) pargs = case lookup t pargs of
                                Just i -> Just (t, i) : newPArg ts pargs
                                Nothing -> Nothing : newPArg ts pargs
  newPArg [] pargs = []

  expandToArity n args
     = case lookupTy n (tt_ctxt ist) of
            [ty] -> expand 0 (normalise (tt_ctxt ist) [] ty) args
            _ -> args
     where expand i (Bind n (Pi _ _ _) sc) (x : xs) = x : expand (i + 1) sc xs
           expand i (Bind n (Pi _ _ _) sc) [] = Just (i, Same) : expand (i + 1) sc []
           expand i _ xs = xs

  mkChange n args pargs = [(n, expandToArity n (sizes args))]
    where
      sizes [] = []
      sizes (a : as) = checkSize a pargs : sizes as

      -- find which argument in pargs <a> is smaller than, if any
      checkSize a ((p, i) : ps)
          | a == p = Just (i, Same)
          | (P _ (UN as) _, [_,_,arg,_]) <- unApply a,
            as == txt "assert_smaller" && arg == p
                  = Just (i, Smaller)
          | smaller Nothing a (p, Nothing) = Just (i, Smaller)
          | otherwise = checkSize a ps 
      checkSize a [] = Nothing

      -- the smaller thing we find must be defined in the same group of mutally
      -- defined types as <a>, and not be coinductive - so carry the type of
      -- the constructor we've gone under.

      smaller (Just tyn) a (t, Just tyt)
         | a == t = isInductive (fst (unApply (getRetTy tyn)))
                                (fst (unApply (getRetTy tyt)))
      smaller ty a (ap@(App _ f s), _)
          | (P (DCon _ _ _) n _, args) <- unApply ap
               = let tyn = getType n in
                     any (smaller (ty `mplus` Just tyn) a)
                         (zip args (map toJust (getArgTys tyn)))
      -- check higher order recursive arguments
      smaller ty (App _ f s) a = smaller ty f a
      smaller _ _ _ = False

      toJust (n, t) = Just t

      getType n = case lookupTyExact n (tt_ctxt ist) of
                       Just ty -> delazy (normalise (tt_ctxt ist) [] ty) -- must exist

      isInductive (P _ nty _) (P _ nty' _) =
          let (co, muts) = case lookupCtxt nty (idris_datatypes ist) of
                                [TI _ x _ _ muts] -> (x, muts)
                                _ -> (False, []) in
              (nty == nty' || any (== nty') muts) && not co
      isInductive _ _ = False

  dePat (Bind x (PVar ty) sc) = dePat (instantiate (P Bound x ty) sc)
  dePat t = t

  patvars (Bind x (PVar _) sc) = x : patvars sc
  patvars _ = []

checkSizeChange :: Name -> Idris Totality
checkSizeChange n = do
   ist <- getIState
   case lookupCtxt n (idris_callgraph ist) of
       [cg] -> do let ms = mkMultiPaths ist [] (scg cg)
                  logCoverage 5 ("Multipath for " ++ show n ++ ":\n" ++
                            "from " ++ show (scg cg) ++ "\n" ++
                            show (length ms) ++ "\n" ++
                            showSep "\n" (map show ms))
                  logCoverage 6 (show cg)
                  -- every multipath must have an infinitely descending
                  -- thread, then the function terminates
                  -- also need to checks functions called are all total
                  -- (Unchecked is okay as we'll spot problems here)
                  let tot = map (checkMP ist n (getArity ist n)) ms
                  logCoverage 4 $ "Generated " ++ show (length tot) ++ " paths"
                  logCoverage 5 $ "Paths for " ++ show n ++ " yield " ++ 
                       (showSep "\n" (map show (zip ms tot)))
                  return (noPartial tot)
       [] -> do logCoverage 5 $ "No paths for " ++ show n
                return Unchecked
  where getArity ist n
          = case lookupTy n (tt_ctxt ist) of
                 [ty] -> arity (normalise (tt_ctxt ist) [] ty)
                 _ -> error "Can't happen: checkSizeChange.getArity"

type MultiPath = [SCGEntry]

mkMultiPaths :: IState -> MultiPath -> [SCGEntry] -> [MultiPath]
mkMultiPaths ist path [] = [reverse path]
mkMultiPaths ist path cg
    = concat (map extend cg)
  where extend (nextf, args)
           | (nextf, args) `elem` path = [ reverse ((nextf, args) : path) ]
           | [Unchecked] <- lookupTotal nextf (tt_ctxt ist)
               = case lookupCtxt nextf (idris_callgraph ist) of
                    [ncg] -> mkMultiPaths ist ((nextf, args) : path) (scg ncg)
                    _ -> [ reverse ((nextf, args) : path) ]
           | otherwise = [ reverse ((nextf, args) : path) ]

-- If any route along the multipath leads to infinite descent, we're fine.
-- Try a route beginning with every argument.
--   If we reach a point we've been to before, but with a smaller value,
--   that means there is an infinitely descending path from that argument.

checkMP :: IState -> Name -> Int -> MultiPath -> Totality
checkMP ist topfn i mp = if i > 0
                     then let paths = (map (tryPath 0 [] mp) [0..i-1]) in
--                               trace ("Paths " ++ show paths) $
                               collapse paths
                     else tryPath 0 [] mp 0
  where
    tryPath' d path mp arg
           = let res = tryPath d path mp arg in
                 trace (show mp ++ "\n" ++ show arg ++ " " ++ show res) res

    mkBig (e, d) = (e, 10000)

    tryPath :: Int -> [((SCGEntry, Int), Int)] -> MultiPath -> Int -> Totality
    tryPath desc path [] _ = Total []
--     tryPath desc path ((UN "believe_me", _) : _) arg
--             = Partial BelieveMe
    -- if we get to a constructor, it's fine as long as it's strictly positive
    tryPath desc path ((f, _) : es) arg
        | [TyDecl (DCon _ _ _) _] <- lookupDef f (tt_ctxt ist)
            = case lookupTotalExact f (tt_ctxt ist) of
                   Just (Total _) -> Unchecked -- okay so far
                   Just (Partial _) -> Partial (Other [f])
                   x -> Unchecked -- An error elsewhere, set as Unchecked to make
                                  -- some progress
        | [TyDecl (TCon _ _) _] <- lookupDef f (tt_ctxt ist)
            = Total []
    tryPath desc path (e@(f, args) : es) arg
        | e `elem` es && allNothing args = Partial (Mutual [f])
    tryPath desc path (e@(f, nextargs) : es) arg
        | Just d <- lookup (e, arg) path
            = if desc - d > 0 -- Now lower than when we were last here
                   then -- trace ("Descent " ++ show (desc - d) ++ " "
                        --      ++ show (path, e)) $
                        Total []
                   else Partial (Mutual (map (fst . fst . fst) path ++ [f]))
        | e `elem` map (fst . fst) path
           && not (f `elem` map fst es)
              = Partial (Mutual (map (fst . fst . fst) path ++ [f]))
        | [Unchecked] <- lookupTotal f (tt_ctxt ist) =
            let argspos = zip nextargs [0..]
                pathres =
                  do (a, pos) <- argspos
                     case a of
                        Nothing -> -- gone up, but if the
                                   -- rest definitely terminates without any
                                   -- cycles (including the path so far, which
                                   -- we take as inaccessible) the path is fine
                            return $ tryPath 0 (map mkBig (((e, arg), desc) : path)) es pos
                        Just (nextarg, sc) ->
                          if nextarg == arg then
                            case sc of
                              Same -> return $ tryPath desc (((e, arg), desc) : path)
                                                       es pos
                              Smaller -> return $ tryPath (desc+1)
                                                          (((e, arg), desc) : path)
                                                          es
                                                          pos
                              _ -> trace ("Shouldn't happen " ++ show e) $
                                      return (Partial Itself)
                            else return Unchecked in
--                   trace (show (desc, argspos, path, es, pathres)) $
                   collapse pathres

        | [Total a] <- lookupTotal f (tt_ctxt ist) = Total a
        | [Partial _] <- lookupTotal f (tt_ctxt ist) = Partial (Other [f])
        | otherwise = Unchecked

allNothing :: [Maybe a] -> Bool
allNothing xs = null (collapseNothing (zip xs [0..]))

collapseNothing :: [(Maybe a, b)] -> [(Maybe a, b)]
collapseNothing ((Nothing, t) : xs)
   = (Nothing, t) : filter (\ (x, _) -> case x of
                                             Nothing -> False
                                             _ -> True) xs
collapseNothing (x : xs) = x : collapseNothing xs
collapseNothing [] = []

noPartial :: [Totality] -> Totality
noPartial (Partial p : xs) = Partial p
noPartial (_ : xs)         = noPartial xs
noPartial []               = Total []

collapse :: [Totality] -> Totality
collapse xs = collapse' Unchecked xs
collapse' def (Total r : xs)   = Total r
collapse' def (Unchecked : xs) = collapse' def xs
collapse' def (d : xs)         = collapse' d xs
-- collapse' Unchecked []         = Total []
collapse' def []               = def

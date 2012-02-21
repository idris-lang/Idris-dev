{-# LANGUAGE PatternGuards #-}

module Idris.Coverage where

import Core.TT
import Core.Evaluate
import Core.CaseTree

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Error

import Data.List
import Data.Either
import Debug.Trace

-- Given a list of LHSs, generate a extra clauses which cover the remaining
-- cases. The ones which haven't been provided are marked 'absurd' so that the
-- checker will make sure they can't happen.

-- This will only work after the given clauses have been typechecked and the
-- names are fully explicit!

genClauses :: FC -> Name -> [Term] -> [PClause] -> Idris [PTerm]
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
        let tryclauses = mkClauses parg all_args
        let new = mnub i $ filter (noMatch i) tryclauses 
        logLvl 7 $ "New clauses: \n" ++ showSep "\n" (map (showImp True) new)
--                     ++ " from:\n" ++ showSep "\n" (map (showImp True) tryclauses) 
        return new
--         return (map (\t -> PClause n t [] PImpossible []) new)
  where getLHS i term 
            | (f, args) <- unApply term = map (\t -> delab' i t True) args
            | otherwise = []

        lhsApp (PClause _ _ l _ _ _) = l
        lhsApp (PWith _ _ l _ _ _) = l

        mnub i [] = []
        mnub i (x : xs) = 
            if (any (\t -> case matchClause i x t of
                                Right _ -> True
                                Left _ -> False) xs) then mnub i xs 
                                                     else x : mnub i xs

        noMatch i tm = all (\x -> case matchClause i (delab' i x True) tm of
                                          Right _ -> False
                                          Left miss -> True) xs 


        mkClauses :: [PArg] -> [[PTerm]] -> [PTerm]
        mkClauses parg args
            | all (== [Placeholder]) args = []
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

-- FIXME: Just look for which one is the deepest, then generate all possibilities
-- up to that depth.

genAll :: IState -> [PTerm] -> [PTerm]
genAll i args = case filter (/=Placeholder) $ concatMap otherPats (nub args) of
                    [] -> [Placeholder]
                    xs -> xs
  where 
    conForm (PApp _ (PRef fc n) _) = isConName Nothing n (tt_ctxt i)
    conForm (PRef fc n) = isConName Nothing n (tt_ctxt i)
    conForm _ = False

    otherPats :: PTerm -> [PTerm]
    otherPats o@(PRef fc n) = ops fc n [] o
    otherPats o@(PApp _ (PRef fc n) xs) = ops fc n xs o
    otherPats arg = return Placeholder 

    ops fc n xs o
        | (TyDecl c@(DCon _ arity) ty : _) <- lookupDef Nothing n (tt_ctxt i)
            = do xs' <- mapM otherPats (map getTm xs)
                 let p = PApp fc (PRef fc n) (zipWith upd xs' xs)
                 let tyn = getTy n (tt_ctxt i)
                 case lookupCtxt Nothing tyn (idris_datatypes i) of
                         (TI ns : _) -> p : map (mkPat fc) (ns \\ [n])
                         _ -> [p]
    ops fc n arg o = return Placeholder

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

-- Check if, in a given type n, the constructor cn : ty is strictly positive,
-- and update the context accordingly

checkPositive :: Name -> (Name, Type) -> Idris ()
checkPositive n (cn, ty) 
    = do let p = cp ty
         i <- getIState
         let tot = if p then Total (args ty) else Partial NotPositive
         let ctxt' = setTotal cn tot (tt_ctxt i)
         putIState (i { tt_ctxt = ctxt' })
         addIBC (IBCTotal cn tot)
  where
    args t = [0..length (getArgTys t)-1]

    cp (Bind n (Pi aty) sc) = posArg aty && cp sc
    cp t = True

    posArg (Bind _ (Pi nty) sc)
        | (P _ n' _, args) <- unApply nty
            = n /= n' && posArg sc
    posArg t = True

-- Totality checking - check for structural recursion (no mutual definitions yet)

data LexOrder = LexXX | LexEQ | LexLT
    deriving (Show, Eq, Ord)

calcTotality :: [Name] -> FC -> Name -> [(Term, Term)] -> Idris Totality
calcTotality path fc n pats 
    = do orders <- mapM ctot pats 
         let order = sortBy cmpOrd $ concat orders
         let (errs, valid) = partitionEithers order
         let lex = stripNoLT (stripXX valid)
         case errs of
            [] -> do logLvl 3 $ show n ++ ":\n" ++ showSep "\n" (map show lex) 
                     logLvl 10 $ show pats
                     checkDecreasing lex
            (e : _) -> return e -- FIXME: should probably combine them
  where
    cmpOrd (Left _) (Left _) = EQ
    cmpOrd (Left _) (Right _) = LT
    cmpOrd (Right _) (Left _) = GT
    cmpOrd (Right x) (Right y) = compare x y

    checkDecreasing [] = return (Total [])
    checkDecreasing (c : cs) | dec c = checkDecreasing cs
                             | otherwise = return (Partial Itself)
    
    dec [] = False
    dec (LexLT : _) = True
    dec (LexEQ : xs) = dec xs
    dec (LexXX : xs) = False

    stripXX [] = []
    stripXX v@(c : cs) 
        = case span (==LexXX) c of
               (ns, rest) -> map (drop (length ns)) v

    -- argument positions which are never LT are no use to us
    stripNoLT [] = [] -- no recursive calls
    stripNoLT xs = case transpose (filter (any (==LexLT)) (transpose xs)) of
                        [] -> [[]] -- recursive calls are all useless...
                        xs -> xs

    ctot (lhs, rhs) 
        | (_, args) <- unApply lhs
            = do -- check lhs doesn't use any dodgy names
                    lhsOK <- mapM (chkOrd [] []) args
                    chkOrd (filter isLeft (concat lhsOK)) args rhs

    isLeft (Left _) = True
    isLeft _ = False

    chkOrd ords args (Bind n (Let t v) sc) 
        = do ov <- chkOrd ords args v
             chkOrd ov args sc
    chkOrd ords args (Bind n b sc) = chkOrd ords (args ++ [P Ref n Erased]) sc
    chkOrd ords args ap@(App f a)
        | (P _ fn _, args') <- unApply ap
            = if fn == n && length args == length args'
                 then do orf <- chkOrd (Right (zipWith lexOrd args args') : ords) args f
                         chkOrd orf args a
                 else do orf <- chkOrd ords args f
                         chkOrd orf args a
        | otherwise = do orf <- chkOrd ords args f
                         chkOrd orf args a
    chkOrd ords args (P _ fn _)
        | n /= fn
            = do tf <- checkTotality (n : path) fc fn
                 case tf of
                    Total _ -> return ords
                    p@(Partial (Mutual x)) -> return ((Left p) : ords)
                    _ -> return (Left (Partial (Other [fn])) : ords)
        | null args = return (Left (Partial Itself) : ords)
    chkOrd ords args _ = return ords

    lexOrd x y | x == y = LexEQ
    lexOrd f@(App _ _) x 
        | (f', args) <- unApply f
            = let ords = map (\x' -> lexOrd x' x) args in
                if any (\o -> o == LexEQ || o == LexLT) ords
                    then LexLT
                    else LexXX
    lexOrd _ _ = LexXX

checkTotality :: [Name] -> FC -> Name -> Idris Totality
checkTotality path fc n 
    | n `elem` path = return (Partial (Mutual (n : path)))
    | otherwise = do
        t <- getTotality n
        ctxt <- getContext
        i <- getIState
        let opts = case lookupCtxt Nothing n (idris_flags i) of
                            [fs] -> fs
                            _ -> []
        t' <- case t of 
                Unchecked -> 
                    case lookupDef Nothing n ctxt of
                        [CaseOp _ _ pats _ _ _ _] -> 
                            do t' <- if AssertTotal `elem` opts
                                        then return $ Total []
                                        else calcTotality path fc n pats
                               setTotality n t'
                               addIBC (IBCTotal n t')
                            -- if it's not total, it can't reduce, to keep
                            -- typechecking decidable
                               case t' of
-- FIXME: Put this back when we can handle mutually recursive things
--                                            p@(Partial _) -> 
--                                                 do setAccessibility n Frozen 
--                                                    addIBC (IBCAccess n Frozen)
--                                                    iputStrLn $ "HIDDEN: " ++ show n ++ show p
                                           _ -> return ()
                               return t'
                        _ -> return $ Total []
                x -> return x
        if TotalFn `elem` opts
            then case t' of
                    Total _ -> return t'
                    e -> totalityError t'
            else return t'
  where
    totalityError t = tclift $ tfail (At fc (Msg (show n ++ " is " ++ show t)))

checkDeclTotality :: (FC, Name) -> Idris Totality
checkDeclTotality (fc, n) 
    = do logLvl 2 $ "Checking " ++ show n ++ " for totality"
         checkTotality [] fc n


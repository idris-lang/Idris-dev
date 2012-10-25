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

import Control.Monad.State

-- Generate the LHSes which are missing from a case tree
-- Eliminate the ones which cannot be well typed

genMissing :: Name -> [Name] -> SC -> Idris [PTerm] 
genMissing fn args sc 
   = do sc' <- expandTree sc
        logLvl 5 $ "Checking missing cases for " ++ show fn ++ "\n" ++ (show sc')
        (got, missing) <- gm fn (map (\x -> P Bound x Erased) args) sc'
        return $ filter (\x -> not (x `elem` got)) missing

-- Make a term to feed to the pattern matcher from a LHS declared impossible
-- (we can't type check it, but we need the case analysis to check for covering...)

mkPatTm :: PTerm -> Idris Term
mkPatTm t = do i <- get
               let timp = addImpl' True [] i t
               evalStateT (toTT timp) 0
  where
    toTT (PRef _ n) = do i <- lift $ get
                         case lookupDef Nothing n (tt_ctxt i) of
                              [TyDecl nt _] -> return $ P nt n Erased
                              _ -> return $ P Ref n Erased
    toTT (PApp _ t args) = do t' <- toTT t
                              args' <- mapM (toTT . getTm) args
                              return $ mkApp t' args'
    toTT _ = do v <- get 
                put (v + 1)
                return (P Bound (MN v "imp") Erased) 

mkPTerm :: Name -> [TT Name] -> Idris PTerm
mkPTerm f args = do i <- get
                    let fapp = mkApp (P Bound f Erased) (map eraseName args)
                    return $ delab i fapp
  where eraseName (App f a) = App (eraseName f) (eraseName a)
        eraseName (P _ (MN _ _) _) = Erased
        eraseName t                = t

gm :: Name -> [TT Name] -> SC -> Idris ([PTerm], [PTerm])
gm fn args (Case n alts) = do m <- mapM (gmAlt fn args n) alts
                              let (got, missing) = unzip m
                              return (concat got, concat missing)
gm fn args (STerm tm)    = do logLvl 3 ("Covered: " ++ show args)
                              t <- mkPTerm fn args
                              return ([t], [])
gm fn args ImpossibleCase = do logLvl 3 ("Impossible: " ++ show args)
                               t <- mkPTerm fn args
                               return ([], [])
gm fn args (UnmatchedCase _) = do logLvl 3 ("Missing: " ++ show args)
                                  t <- mkPTerm fn args
                                  return ([], [t])

gmAlt fn args n (ConCase cn t cargs sc)
   = do let args' = map (subst n (mkApp (P Bound cn Erased)
                                        (map (\x -> P Bound x Erased) cargs))) args
        gm fn args' sc
gmAlt fn args n (ConstCase c sc)
   = do let args' = map (subst n (Constant c)) args
        gm fn args' sc
gmAlt fn args n (DefaultCase sc)
   = do gm fn args sc

getDefault (DefaultCase sc : _) = sc
getDefault (_ : cs) = getDefault cs
getDefault [] = UnmatchedCase ""

dropDefault (DefaultCase sc : rest) = dropDefault rest
dropDefault (c : cs) = c : dropDefault cs
dropDefault [] = [] 

expandTree :: SC -> Idris SC
expandTree (Case n alts) = do i <- get
                              as <- expandAlts i (dropDefault alts) (getDefault alts)
                              alts' <- mapM expandTreeA as
                              return (Case n alts')
    where expandTreeA (ConCase n i ns sc) = do sc' <- expandTree sc
                                               return (ConCase n i ns sc')
          expandTreeA (ConstCase i sc) = do sc' <- expandTree sc
                                            return (ConstCase i sc')
          expandTreeA (DefaultCase sc) = do sc' <- expandTree sc
                                            return (DefaultCase sc')
expandTree t = return t

expandAlts :: IState -> [CaseAlt] -> SC -> Idris [CaseAlt]
expandAlts i all@(ConstCase c _ : alts) def
    = return $ all ++ [DefaultCase def]
expandAlts i all@(ConCase n _ _ _ : alts) def
    | (TyDecl c@(DCon _ arity) ty : _) <- lookupDef Nothing n (tt_ctxt i)
         = do let tyn = getTy n (tt_ctxt i)
              case lookupCtxt Nothing tyn (idris_datatypes i) of
                  (TI ns _ : _) -> do let ps = map mkPat ns
                                      return $ addAlts ps (altsFor all) all
                  _ -> return all
  where
    altsFor [] = []
    altsFor (ConCase n _ _ _ : alts) = n : altsFor alts
    altsFor (_ : alts) = altsFor alts

    addAlts [] got alts = alts
    addAlts ((n, arity) : ps) got alts
        | n `elem` got = addAlts ps got alts
        | otherwise = addAlts ps got (alts ++ [ConCase n (-1) (argList arity) def])

    argList i = take i (map (\x -> (MN x "ign")) [0..])

    getTy n ctxt = case lookupTy Nothing n ctxt of
                          (t : _) -> case unApply (getRetTy t) of
                                        (P _ tyn _, _) -> tyn
                                        x -> error $ "Can't happen getTy 1 " ++ show (n, x)
                          _ -> error "Can't happen getTy 2"

    mkPat x = case lookupCtxt Nothing x (idris_implicits i) of
                    (pargs : _)
                       -> (x, length pargs)  
                    _ -> error "Can't happen - genAll"
expandAlts i alts def = return alts 
        


-- OLD STUFF: probably broken...

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
                         (TI ns _ : _) -> p : map (mkPat fc) (ns \\ [n])
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

calcProd :: IState -> FC -> Name -> [([Name], Term, Term)] -> Idris Totality
calcProd i fc n pats = do patsprod <- mapM prodRec pats
                          if (and patsprod) 
                             then return Productive
                             else return (Partial NotProductive)
   where
     -- every application of n must be in an argument of a coinductive constructor

     prodRec :: ([Name], Term, Term) -> Idris Bool
     prodRec (_, _, tm) = prod False tm 

     prod ok ap@(App _ _)
        | (P _ (UN "lazy") _, [_, arg]) <- unApply ap = prod ok arg
        | (P _ f ty, args) <- unApply ap
            = let co = cotype ty in
                  if f == n 
                     then do argsprod <- mapM (prod co) args
                             return (and (ok : argsprod) )
                     else do argsprod <- mapM (prod co) args
                             return (and argsprod)
     prod ok (App f a) = liftM2 (&&) (prod False f) (prod False a)
     prod ok (Bind _ (Let t v) sc) = liftM2 (&&) (prod False v) (prod False v)
     prod ok (Bind _ b sc) = prod ok sc
     prod ok t = return True 
    
     cotype ty 
        | (P _ t _, _) <- unApply (getRetTy ty)
            = case lookupCtxt Nothing t (idris_datatypes i) of
                   [TI _ True] -> True
                   _ -> False
        | otherwise = False

calcTotality :: [Name] -> FC -> Name -> [([Name], Term, Term)] -> Idris Totality
calcTotality path fc n pats 
    = do i <- get
         let opts = case lookupCtxt Nothing n (idris_flags i) of
                            [fs] -> fs
                            _ -> []
         if (Coinductive `elem` opts) then calcProd i fc n pats
           else do orders <- mapM ctot pats 
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

    ctot (_, lhs, rhs) 
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
                    Productive -> return t'
                    e -> totalityError t'
            else return t'
  where
    totalityError t = tclift $ tfail (At fc (Msg (show n ++ " is " ++ show t)))

checkDeclTotality :: (FC, Name) -> Idris Totality
checkDeclTotality (fc, n) 
    = do logLvl 2 $ "Checking " ++ show n ++ " for totality"
         checkTotality [] fc n

-- Calculate the size change graph for this definition

-- SCG for a function f consists of a list of:
--    (g, [(a1, sizechange1), (a2, sizechange2), ..., (an, sizechangen)])

-- where g is a function called
-- a1 ... an are the arguments of f in positions 1..n of g
-- sizechange1 ... sizechange2 is how their size has changed wrt the input to f
--    Nothing, if the argument is unrelated to the input

buildSCG :: IState -> SC -> [Name] -> [(Name, [Maybe (Name, SizeChange)])] 
buildSCG ist sc args = scg sc (zip args args) (zip args (zip args (repeat Same)))
   where
      scg :: SC -> [(Name, Name)] -> -- local var, originating top level var
             [(Name, (Name, SizeChange))] -> -- map from orig to new and relationship
             [(Name, [Maybe (Name, SizeChange)])]
      scg (Case x alts) vars szs = concatMap (scgAlt x vars szs) alts
      scg (STerm tm) vars szs = scgTerm tm vars szs
      scg _ _ _ = []

      -- how the arguments relate - either Smaller or Unknown
      argRels :: Name -> [(Name, SizeChange)]
      argRels n = let ctxt = tt_ctxt ist
                      [ty] = lookupTy Nothing n ctxt -- must exist!
                      P _ nty _ = fst (unApply (getRetTy ty))
                      args = map snd (getArgTys ty) in
                      map (getRel nty) (map (fst . unApply) args)
        where
          getRel ty (P _ n' _) | n' == ty = (n, Smaller)
          getRel ty _ = (n, Unknown)

      scgAlt x vars szs (ConCase n _ args sc)
           -- all args smaller than top variable of x in sc
           -- (as long as they are in the same type family)
         | Just tvar <- lookup x vars
              = let arel = argRels n
                    szs' = zipWith (\arg (_,t) -> (arg, (x, t))) args arel ++ szs
                    vars' = zip args (repeat tvar) ++ vars in
                    scg sc vars' szs'
         | otherwise = scg sc vars szs
      scgAlt x vars szs (ConstCase _ sc) = scg sc vars szs
      scgAlt x vars szs (DefaultCase sc) = scg sc vars szs

      scgTerm f@(App _ _) vars szs
         | (P _ fn _, args) <- unApply f
            = let rest = concatMap (\x -> scgTerm x vars szs) args in
                  case lookup fn vars of
                       Just _ -> rest
                       Nothing -> (fn, map (mkChange szs) args) : rest 
      scgTerm (App f a) vars szs
            = scgTerm f vars szs ++ scgTerm a vars szs
      scgTerm (Bind n (Let t v) e) vars szs
            = scgTerm v vars szs ++ scgTerm e vars szs
      scgTerm (Bind n _ e) vars szs
            = scgTerm e ((n, n) : vars) szs
      scgTerm _ _ _ = []

      mkChange :: [(Name, (Name, SizeChange))] -> Term -> Maybe (Name, SizeChange)
      mkChange szs (P _ n ty) = case lookup n szs of
                                     Just (_, Unknown) -> Nothing
                                     t -> t
      mkChange _ _ = Nothing


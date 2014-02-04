{-# LANGUAGE PatternGuards #-}

module Idris.Coverage where

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.CaseTree

import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Error

import Data.List
import Data.Either
import Data.Maybe
import Debug.Trace

import Control.Monad.State.Strict

mkPatTm :: PTerm -> Idris Term
mkPatTm t = do i <- getIState
               let timp = addImpl' True [] [] i t
               evalStateT (toTT timp) 0
  where
    toTT (PRef _ n) = do i <- lift getIState
                         case lookupDef n (tt_ctxt i) of
                              [TyDecl nt _] -> return $ P nt n Erased
                              _ -> return $ P Ref n Erased
    toTT (PApp _ t args) = do t' <- toTT t
                              args' <- mapM (toTT . getTm) args
                              return $ mkApp t' args'
    toTT _ = do v <- get
                put (v + 1)
                return (P Bound (sMN v "imp") Erased)

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
        logLvl 5 $ "COVERAGE of " ++ show n
        logLvl 5 $ show (map length argss) ++ "\n" ++ show (map length all_args)
        logLvl 10 $ show argss ++ "\n" ++ show all_args
        logLvl 10 $ "Original: \n" ++
             showSep "\n" (map (\t -> showTm i (delab' i t True True)) xs)
        -- add an infinite supply of explicit arguments to update the possible
        -- cases for (the return type may be variadic, or function type, sp
        -- there may be more case splitting that the idris_implicits record
        -- suggests)
        let parg = case lookupCtxt n (idris_implicits i) of
                        (p : _) -> p ++ repeat (PExp 0 [] Placeholder "")
                        _ -> repeat (pexp Placeholder)
        let tryclauses = mkClauses parg all_args
        logLvl 2 $ show (length tryclauses) ++ " initially to check"
        logLvl 5 $ showSep "\n" (map (showTm i) tryclauses)
        let new = filter (noMatch i) (nub tryclauses)
        logLvl 1 $ show (length new) ++ " clauses to check for impossibility"
        logLvl 5 $ "New clauses: \n" ++ showSep "\n" (map (showTm i) new)
--           ++ " from:\n" ++ showSep "\n" (map (showImp True) tryclauses)
        return new
--         return (map (\t -> PClause n t [] PImpossible []) new)
  where getLHS i term
            | (f, args) <- unApply term = map (\t -> delab' i t True True) args
            | otherwise = []

        lhsApp (PClause _ _ l _ _ _) = l
        lhsApp (PWith _ _ l _ _ _) = l

        noMatch i tm = all (\x -> case matchClause i (delab' i x True True) tm of
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

fnub xs = fnub' [] xs

fnub' acc (x : xs) | x `qelem` acc = fnub' acc (filter (not.(quickEq x)) xs)
                   | otherwise = fnub' (x : acc) xs
fnub' acc [] = acc

-- quick check for constructor equality
quickEq :: PTerm -> PTerm -> Bool
quickEq (PRef _ n) (PRef _ n') = n == n'
quickEq (PApp _ t as) (PApp _ t' as')
    | length as == length as'
       = quickEq t t' && and (zipWith quickEq (map getTm as) (map getTm as'))
quickEq Placeholder Placeholder = True
quickEq x y = False

qelem x [] = False
qelem x (y : ys) | x `quickEq` y = True
                 | otherwise = qelem x ys

-- FIXME: Just look for which one is the deepest, then generate all
-- possibilities up to that depth.

genAll :: IState -> [PTerm] -> [PTerm]
genAll i args
   = case filter (/=Placeholder) $ fnub (concatMap otherPats (fnub args)) of
          [] -> [Placeholder]
          xs -> inventConsts xs
  where
    -- if they're constants, invent a new one to make sure that
    -- constants which are not explicitly handled are covered
    inventConsts cs@(PConstant c : _) = map PConstant (ic' (mapMaybe getConst cs))
      where getConst (PConstant c) = Just c
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
    -- TODO: Bit vectors
    -- The rest are types with only one case
    ic' xs = xs

    firstMissing cs (x : xs) | x `elem` cs = firstMissing cs xs
                             | otherwise = x : cs

    lotsOfNums t = map t [0..]
    lotsOfChars = map Ch ['a'..]
    lotsOfStrings = map Str (map (("some string " ++).show) [1..])

    conForm (PApp _ (PRef fc n) _) = isConName n (tt_ctxt i)
    conForm (PRef fc n) = isConName n (tt_ctxt i)
    conForm _ = False

    nubMap f acc [] = acc
    nubMap f acc (x : xs) = nubMap f (fnub' acc (f x)) xs

    otherPats :: PTerm -> [PTerm]
    otherPats o@(PRef fc n) = ops fc n [] o
    otherPats o@(PApp _ (PRef fc n) xs) = ops fc n xs o
    otherPats o@(PPair fc _ l r)
        = ops fc pairCon
                ([pimp (sUN "A") Placeholder True,
                  pimp (sUN "B") Placeholder True] ++
                 [pexp l, pexp r]) o
    otherPats o@(PDPair fc t _ v)
        = ops fc (sUN "Ex_intro")
                ([pimp (sUN "a") Placeholder True,
                  pimp (sUN "P") Placeholder True] ++
                 [pexp t,pexp v]) o
    otherPats o@(PConstant c) = return o
    otherPats arg = return Placeholder

    ops fc n xs o
        | (TyDecl c@(DCon _ arity) ty : _) <- lookupDef n (tt_ctxt i)
            = do xs' <- mapM otherPats (map getExpTm xs)
                 let p = resugar (PApp fc (PRef fc n) (zipWith upd xs' xs))
                 let tyn = getTy n (tt_ctxt i)
                 case lookupCtxt tyn (idris_datatypes i) of
                         (TI ns _ _ _ : _) -> p : map (mkPat fc) (ns \\ [n])
                         _ -> [p]
    ops fc n arg o = return Placeholder

    getExpTm (PImp _ True _ _ _ _) = Placeholder -- machine inferred, no point!
    getExpTm t = getTm t

    -- put it back to its original form
    resugar (PApp _ (PRef fc (UN ei)) [_,_,t,v])
      | ei == txt "Ex_intro"
        = PDPair fc (getTm t) Placeholder (getTm v)
    resugar (PApp _ (PRef fc n) [_,_,l,r])
      | n == pairCon
        = PPair fc IsTerm (getTm l) (getTm r)
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
         logLvl 5 $ "Constructor " ++ show cn ++ " is " ++ show tot
         addIBC (IBCTotal cn tot)
  where
    args t = [0..length (getArgTys t)-1]

    cp (Bind n (Pi aty) sc) = posArg aty && cp sc
    cp t = True

    posArg (Bind _ (Pi nty) sc)
        | (P _ n' _, args) <- unApply nty
            = n /= n' && posArg sc
    posArg t = True

calcProd :: IState -> FC -> Name -> [([Name], Term, Term)] -> Idris Totality
calcProd i fc topn pats
    = cp topn pats []
   where
     -- every application of n must be in an argument of a coinductive
     -- constructor, in every function reachable from here in the
     -- call graph.
     cp n pats done = do patsprod <- mapM (prodRec n done) pats
                         if (and patsprod)
                            then return Productive
                            else return (Partial NotProductive)

     prodRec :: Name -> [Name] -> ([Name], Term, Term) -> Idris Bool
     prodRec n done _ | n `elem` done = return True
     prodRec n done (_, _, tm) = prod n done False tm

     prod :: Name -> [Name] -> Bool -> Term -> Idris Bool
     prod n done ok ap@(App _ _)
        | (P _ (UN l) _, [_, arg]) <- unApply ap,
          l == txt "lazy" = prod n done ok arg
        | (P nt f _, args) <- unApply ap
            = do recOK <- checkProdRec (n:done) f
                 let ctxt = tt_ctxt i
                 let [ty] = lookupTy f ctxt -- must exist!
                 let co = cotype nt f ty in
                     if (not recOK) then return False else
                       if f == topn
                         then do argsprod <- mapM (prod n done co) args
                                 return (and (ok : argsprod) )
                         else do argsprod <- mapM (prod n done co) args
                                 return (and argsprod)
     prod n done ok (App f a) = liftM2 (&&) (prod n done False f)
                                            (prod n done False a)
     prod n done ok (Bind _ (Let t v) sc)
         = liftM2 (&&) (prod n done False v) (prod n done False v)
     prod n done ok (Bind _ b sc) = prod n done ok sc
     prod n done ok t = return True

     checkProdRec :: [Name] -> Name -> Idris Bool
     checkProdRec done f
        = case lookupCtxt f (idris_patdefs i) of
               [(def, _)] -> do ok <- mapM (prodRec f done) def
                                return (and ok)
               _ -> return True -- defined elsewhere, can't call topn

     cotype (DCon _ _) n ty
        | (P _ t _, _) <- unApply (getRetTy ty)
            = case lookupCtxt t (idris_datatypes i) of
                   [TI _ True _ _] -> True
                   _ -> False
     cotype nt n ty = False

calcTotality :: [Name] -> FC -> Name -> [([Name], Term, Term)]
                -> Idris Totality
calcTotality path fc n pats
    = do i <- getIState
         let opts = case lookupCtxt n (idris_flags i) of
                            [fs] -> fs
                            _ -> []
         case mapMaybe (checkLHS i) (map (\ (_, l, r) -> l) pats) of
            (failure : _) -> return failure
            _ -> if (Coinductive `elem` opts)
                      then calcProd i fc n pats
                      else checkSizeChange n
  where
    checkLHS i (P _ fn _)
        = case lookupTotal fn (tt_ctxt i) of
               [Partial _] -> return (Partial (Other [fn]))
               _ -> Nothing
    checkLHS i (App f a) = mplus (checkLHS i f) (checkLHS i a)
    checkLHS _ _ = Nothing

checkTotality :: [Name] -> FC -> Name -> Idris Totality
checkTotality path fc n
    | n `elem` path = return (Partial (Mutual (n : path)))
    | otherwise = do
        t <- getTotality n
        updateContext (simplifyCasedef n)
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
                                        else calcTotality path fc n pats
                               setTotality n t'
                               addIBC (IBCTotal n t')
                               return t'
                            -- if it's not total, it can't reduce, to keep
                            -- typechecking decidable
--                                case t' of
--                                  p@(Partial _) ->
--                                      do setAccessibility n Frozen
--                                         addIBC (IBCAccess n Frozen)
--                                         logLvl 5 $ "HIDDEN: "
--                                               ++ show n ++ show p
--                                  _ -> return ()
--                                return t'
                        _ -> return $ Total []
                x -> return x
        case t' of
            Total _ -> return t'
            Productive -> return t'
            e -> do w <- cmdOptType WarnPartial
                    if TotalFn `elem` opts
                       then totalityError t'
                       else do when (w && not (PartialFn `elem` opts)) $
                                   warnPartial n t'
                               return t'
  where
    totalityError t = tclift $ tfail (At fc (Msg (show n ++ " is " ++ show t)))

    warnPartial n t
       = do i <- getIState
            case lookupDef n (tt_ctxt i) of
               [x] -> do
                  iputStrLn $ show fc ++ ":Warning - " ++ show n ++ " is " ++ show t
--                                ++ "\n" ++ show x
--                   let cg = lookupCtxtName Nothing n (idris_callgraph i)
--                   iputStrLn (show cg)


checkDeclTotality :: (FC, Name) -> Idris Totality
checkDeclTotality (fc, n)
    = do logLvl 2 $ "Checking " ++ show n ++ " for totality"
--          buildSCG (fc, n)
--          logLvl 2 $ "Built SCG"
         i <- getIState 
         t <- checkTotality [] fc n
         case t of
              -- if it's not total, it can't reduce, to keep
              -- typechecking decidable
              p@(Partial _) -> do setAccessibility n Frozen
                                  addIBC (IBCAccess n Frozen)
                                  logLvl 5 $ "HIDDEN: "
                                               ++ show n ++ show p
              _ -> return ()
         return t


-- Calculate the size change graph for this definition

-- SCG for a function f consists of a list of:
--    (g, [(a1, sizechange1), (a2, sizechange2), ..., (an, sizechangen)])

-- where g is a function called
-- a1 ... an are the arguments of f in positions 1..n of g
-- sizechange1 ... sizechange2 is how their size has changed wrt the input
-- to f
--    Nothing, if the argument is unrelated to the input

buildSCG :: (FC, Name) -> Idris ()
buildSCG (_, n) = do
   ist <- getIState
   case lookupCtxt n (idris_callgraph ist) of
       [cg] -> case lookupDef n (tt_ctxt ist) of
           [CaseOp _ _ _ pats _ cd] ->
             let (args, sc) = cases_totcheck cd in
               do logLvl 2 $ "Building SCG for " ++ show n ++ " from\n"
                                ++ show pats ++ "\n" ++ show sc
                  let newscg = buildSCG' ist (rights pats) args
                  logLvl 5 $ show newscg
                  addToCG n ( cg { scg = newscg } )
       [] -> logLvl 5 $ "Could not build SCG for " ++ show n ++ "\n"
       x -> error $ "buildSCG: " ++ show (n, x)

buildSCG' :: IState -> [(Term, Term)] -> [Name] -> [SCGEntry]
buildSCG' ist pats args = nub $ concatMap scgPat pats where
  scgPat (lhs, rhs) = let (f, pargs) = unApply (dePat lhs) in
                          findCalls (dePat rhs) (patvars lhs) pargs

  findCalls ap@(App f a) pvs pargs
     | (P _ (UN l) _, [_, arg]) <- unApply ap,
       l == txt "lazy"
        = findCalls arg pvs pargs
     -- under a call to "assert_total", don't do any checking, just believe
     -- that it is total.
     | (P _ (UN at) _, [_, _]) <- unApply ap,
       at == txt "assert_total" = []
     | (P _ n _, args) <- unApply ap
        = mkChange n args pargs ++
              concatMap (\x -> findCalls x pvs pargs) args
  findCalls (App f a) pvs pargs
        = findCalls f pvs pargs ++ findCalls a pvs pargs
  findCalls (Bind n (Let t v) e) pvs pargs
        = findCalls v pvs pargs ++ findCalls e (n : pvs) pargs
  findCalls (Bind n _ e) pvs pargs
        = findCalls e (n : pvs) pargs
  findCalls (P _ f _ ) pvs pargs
      | not (f `elem` pvs) = [(f, [])]
  findCalls _ _ _ = []

  expandToArity n args 
     = case lookupTy n (tt_ctxt ist) of
            [ty] -> expand 0 (normalise (tt_ctxt ist) [] ty) args
            _ -> args
     where expand i (Bind n (Pi _) sc) (x : xs) = x : expand (i + 1) sc xs
           expand i (Bind n (Pi _) sc) [] = Just (i, Same) : expand (i + 1) sc []
           expand i _ xs = xs

  mkChange n args pargs = [(n, expandToArity n (sizes args))]
    where
      sizes [] = []
      sizes (a : as) = checkSize a pargs 0 : sizes as

      -- find which argument in pargs <a> is smaller than, if any
      checkSize a (p : ps) i
          | a == p = Just (i, Same)
          | (P _ (UN as) _, [_,arg,_]) <- unApply a,
            as == txt "assert_smaller" && arg == p
                  = Just (i, Smaller)
          | smaller Nothing a (p, Nothing) = Just (i, Smaller)
          | otherwise = checkSize a ps (i + 1)
      checkSize a [] i = Nothing

      -- the smaller thing we find must be the same type as <a>, and
      -- not be coinductive - so carry the type of the constructor we've
      -- gone under.

      smaller (Just tyn) a (t, Just tyt)
         | a == t = isInductive (fst (unApply (getRetTy tyn)))
                                (fst (unApply (getRetTy tyt)))
      smaller ty a (ap@(App f s), _)
          | (P (DCon _ _) n _, args) <- unApply ap
               = let tyn = getType n in
                     any (smaller (ty `mplus` Just tyn) a)
                         (zip args (map toJust (getArgTys tyn)))
      -- check higher order recursive arguments
      smaller ty (App f s) a = smaller ty f a
      smaller _ _ _ = False

      toJust (n, t) = Just t

      getType n = case lookupTy n (tt_ctxt ist) of
                       [ty] -> ty -- must exist

      isInductive (P _ nty _) (P _ nty' _) =
          let co = case lookupCtxt nty (idris_datatypes ist) of
                        [TI _ x _ _] -> x
                        _ -> False in
              nty == nty' && not co
      isInductive _ _ = False

--       getTypeFam t | (P _ n _, _) <- unApply t

  dePat (Bind x (PVar ty) sc) = dePat (instantiate (P Bound x ty) sc)
  dePat t = t

  patvars (Bind x (PVar _) sc) = x : patvars sc
  patvars _ = []

{-
buildSCG' :: IState -> SC -> [Name] -> [SCGEntry]
buildSCG' ist sc args = -- trace ("Building SCG for " ++ show sc) $
                           nub $ scg sc (zip args args)
                                 (zip args (zip args (repeat Same)))
   where
      scg :: SC -> [(Name, Name)] -> -- local var, originating top level var
             [(Name, (Name, SizeChange))] -> -- orig to new,  and relationship
             [SCGEntry]
      scg (Case x alts) vars szs
          = let x' = findTL x vars in
                concatMap (scgAlt x' vars szs) alts
        where
          findTL x vars
            | Just x' <- lookup x vars
               = if x' `elem`  args then x'
                    else findTL x' vars
            | otherwise = x

      scg (STerm tm) vars szs = scgTerm tm vars szs
      scg _ _ _ = []

      -- how the arguments relate - either Smaller or Unknown
      argRels :: Name -> [(Name, SizeChange)]
      argRels n = let ctxt = tt_ctxt ist
                      [ty] = lookupTy n ctxt -- must exist!
                      P _ nty _ = fst (unApply (getRetTy ty))
                      co = case lookupCtxt nty (idris_datatypes ist) of
                              [TI _ x _ _] -> x
                              _ -> False
                      args = map snd (getArgTys ty) in
                      map (getRel co nty) (map (fst . unApply . getRetTy) args)
        where
          getRel True _ _ = (n, Unknown) -- coinductive
          getRel _ ty (P _ n' _) | n' == ty = (n, Smaller)
          getRel _ ty t = (n, Unknown)

      scgAlt x vars szs (ConCase n _ args sc)
           -- all args smaller than top variable of x in sc
           -- (as long as they are in the same type family, and it's
           -- not coinductive)
         | Just tvar <- lookup x vars
              = let arel = argRels n
                    szs' = zipWith (\arg (_,t) -> (arg, (x, t))) args arel
                                                       ++ szs
                    vars' = nub (zip args (repeat tvar) ++ vars) in
                    scg sc vars' szs'
         | otherwise = scg sc vars szs
      scgAlt x vars szs (ConstCase _ sc) = scg sc vars szs
      scgAlt x vars szs (DefaultCase sc) = scg sc vars szs

      scgTerm f@(App _ _) vars szs
         | (P _ (UN "lazy") _, [_, arg]) <- unApply f
             = scgTerm arg vars szs
         | (P _ fn _, args) <- unApply f
            = let rest = concatMap (\x -> scgTerm x vars szs) args in
                  case lookup fn vars of
                       Just _ -> rest
                       Nothing -> nub $ (fn, map (mkChange szs) args) : rest
      scgTerm (App f a) vars szs
            = scgTerm f vars szs ++ scgTerm a vars szs
      scgTerm (Bind n (Let t v) e) vars szs
            = scgTerm v vars szs ++ scgTerm e vars szs
      scgTerm (Bind n _ e) vars szs
            = scgTerm e (nub ((n, n) : vars)) szs
      scgTerm (P _ fn _) vars szs
            = case lookup fn vars of
                   Just _ -> []
                   Nothing -> [(fn, [])]
      scgTerm _ _ _ = []

      mkChange :: [(Name, (Name, SizeChange))] -> Term
                   -> Maybe (Int, SizeChange)
      mkChange szs tm
         | (P _ (UN "lazy") _, [_, arg]) <- unApply tm = mkChange szs arg
         | (P _ n ty, _) <- unApply tm -- get higher order args too
          = do sc <- lookup n szs
               case sc of
                  (_, Unknown) -> Nothing
                  (o, sc) -> do i <- getArgPos 0 o args
                                return (i, sc)
      mkChange _ _ = Nothing

      getArgPos :: Int -> Name -> [Name] -> Maybe Int
      getArgPos i n [] = Nothing
      getArgPos i n (x : xs) | n == x = Just i
                             | otherwise = getArgPos (i + 1) n xs
-}

checkSizeChange :: Name -> Idris Totality
checkSizeChange n = do
   ist <- getIState
   case lookupCtxt n (idris_callgraph ist) of
       [cg] -> do let ms = mkMultiPaths ist [] (scg cg)
                  logLvl 5 ("Multipath for " ++ show n ++ ":\n" ++
                            "from " ++ show (scg cg) ++ "\n" ++
                            show (length ms) ++ "\n" ++
                            showSep "\n" (map show ms))
                  logLvl 6 (show cg)
                  -- every multipath must have an infinitely descending
                  -- thread, then the function terminates
                  -- also need to checks functions called are all total
                  -- (Unchecked is okay as we'll spot problems here)
                  let tot = map (checkMP ist (getArity ist n)) ms
                  logLvl 4 $ "Generated " ++ show (length tot) ++ " paths"
                  logLvl 6 $ "Paths for " ++ show n ++ " yield " ++ (show tot)
                  return (noPartial tot)
       [] -> do logLvl 5 $ "No paths for " ++ show n
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

--     do (nextf, args) <- cg
--          if ((nextf, args) `elem` path)
--             then return (reverse ((nextf, args) : path))
--             else case lookupCtxt nextf (idris_callgraph ist) of
--                     [ncg] -> mkMultiPaths ist ((nextf, args) : path) (scg ncg)
--                     _ -> return (reverse ((nextf, args) : path))

-- If any route along the multipath leads to infinite descent, we're fine.
-- Try a route beginning with every argument.
--   If we reach a point we've been to before, but with a smaller value,
--   that means there is an infinitely descending path from that argument.

checkMP :: IState -> Int -> MultiPath -> Totality
checkMP ist i mp = if i > 0
                     then let paths = (map (tryPath 0 [] mp) [0..i-1]) in
--                               trace ("Paths " ++ show paths) $
                               collapse paths
                     else tryPath 0 [] mp 0
  where
    tryPath' d path mp arg
           = let res = tryPath d path mp arg in
                 trace (show mp ++ "\n" ++ show arg ++ " " ++ show res) res

    tryPath :: Int -> [((SCGEntry, Int), Int)] -> MultiPath -> Int -> Totality
    tryPath desc path [] _ = Total []
--     tryPath desc path ((UN "believe_me", _) : _) arg
--             = Partial BelieveMe
    -- if we get to a constructor, it's fine as long as it's strictly positive
    tryPath desc path ((f, _) : es) arg
        | [TyDecl (DCon _ _) _] <- lookupDef f (tt_ctxt ist)
            = case lookupTotal f (tt_ctxt ist) of
                   [Total _] -> Unchecked -- okay so far
                   [Partial _] -> Partial (Other [f])
                   x -> error (show x)
        | [TyDecl (TCon _ _) _] <- lookupDef f (tt_ctxt ist)
            = Total []
    tryPath desc path (e@(f, args) : es) arg
        | e `elem` es && allNothing args = Partial (Mutual [f])
    tryPath desc path (e@(f, nextargs) : es) arg
        | Just d <- lookup (e, arg) path
            = if desc > 0
                   then -- trace ("Descent " ++ show (desc - d) ++ " "
                        --      ++ show (path, e)) $
                        Total []
                   else Partial (Mutual (map (fst . fst . fst) path ++ [f]))
        | e `elem` map (fst . fst) path
           && not (f `elem` map fst es) 
              = Partial (Mutual (map (fst . fst . fst) path ++ [f]))
        | [Unchecked] <- lookupTotal f (tt_ctxt ist) =
            let argspos = case collapseNothing (zip nextargs [0..]) of
                               [] -> [(Nothing, 0)]
                               x -> x
--               trace (show (argspos, nextargs, path)) $
                pathres = 
                  do (a, pos) <- argspos
                     case a of
                        Nothing -> -- don't know, but if the
                                   -- rest definitely terminates without
                                   -- any cycles with route so far,
                                   -- then we might yet be total
                            case collapse (map (tryPath 0 (((e, arg), 0):path) es)
                                          [0..length nextargs - 1]) of
                                Total _ -> return Unchecked
                                x -> return x
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
                   collapse' Unchecked pathres

        | [Total a] <- lookupTotal f (tt_ctxt ist) = Total a
        | [Partial _] <- lookupTotal f (tt_ctxt ist) = Partial (Other [f])
        | otherwise = Unchecked

allNothing xs = null (collapseNothing (zip xs [0..]))

collapseNothing ((Nothing, _) : xs)
   = filter (\ (x, _) -> case x of
                             Nothing -> False
                             _ -> True) xs
collapseNothing (x : xs) = x : collapseNothing xs
collapseNothing [] = []

noPartial (Partial p : xs) = Partial p
noPartial (_ : xs)         = noPartial xs
noPartial []               = Total []

collapse xs = collapse' Unchecked xs
collapse' def (Total r : xs)   = Total r
collapse' def (Unchecked : xs) = collapse' def xs
collapse' def (d : xs)         = collapse' d xs
-- collapse' Unchecked []         = Total []
collapse' def []               = def


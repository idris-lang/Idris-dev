{-# LANGUAGE PatternGuards, DeriveFunctor, TypeSynonymInstances #-}

module Idris.Core.CaseTree(CaseDef(..), SC, SC'(..), CaseAlt, CaseAlt'(..),
                     Phase(..), CaseTree,
                     simpleCase, small, namesUsed, findCalls, findUsedArgs) where

import Idris.Core.TT

import Control.Monad.State
import Data.Maybe
import Data.List hiding (partition)
import Debug.Trace

data CaseDef = CaseDef [Name] !SC [Term]
    deriving Show

data SC' t = Case Name [CaseAlt' t] -- ^ invariant: lowest tags first
           | ProjCase t [CaseAlt' t] -- ^ special case for projections
           | STerm !t
           | UnmatchedCase String -- ^ error message
           | ImpossibleCase -- ^ already checked to be impossible
    deriving (Eq, Ord, Functor)
{-!
deriving instance Binary SC'
deriving instance NFData SC'
!-}

type SC = SC' Term

data CaseAlt' t = ConCase Name Int [Name] !(SC' t)
                | FnCase Name [Name]      !(SC' t) -- ^ reflection function
                | ConstCase Const         !(SC' t)
                | SucCase Name            !(SC' t)
                | DefaultCase             !(SC' t)
    deriving (Show, Eq, Ord, Functor)
{-!
deriving instance Binary CaseAlt'
deriving instance NFData CaseAlt'
!-}

type CaseAlt = CaseAlt' Term

instance Show t => Show (SC' t) where
    show sc = show' 1 sc
      where
        show' i (Case n alts) = "case " ++ show n ++ " of\n" ++ indent i ++
                                    showSep ("\n" ++ indent i) (map (showA i) alts)
        show' i (ProjCase tm alts) = "case " ++ show tm ++ " of " ++
                                      showSep ("\n" ++ indent i) (map (showA i) alts)
        show' i (STerm tm) = show tm
        show' i (UnmatchedCase str) = "error " ++ show str
        show' i ImpossibleCase = "impossible"

        indent i = concat $ take i (repeat "    ")

        showA i (ConCase n t args sc)
           = show n ++ "(" ++ showSep (", ") (map show args) ++ ") => "
                ++ show' (i+1) sc
        showA i (FnCase n args sc)
           = "FN " ++ show n ++ "(" ++ showSep (", ") (map show args) ++ ") => "
                ++ show' (i+1) sc
        showA i (ConstCase t sc)
           = show t ++ " => " ++ show' (i+1) sc
        showA i (SucCase n sc)
           = show n ++ "+1 => " ++ show' (i+1) sc
        showA i (DefaultCase sc)
           = "_ => " ++ show' (i+1) sc


type CaseTree = SC
type Clause   = ([Pat], (Term, Term))
type CS = ([Term], Int, [(Name, Type)])

instance TermSize SC where
    termsize n (Case n' as) = termsize n as
    termsize n (ProjCase n' as) = termsize n as
    termsize n (STerm t) = termsize n t
    termsize n _ = 1

instance TermSize CaseAlt where
    termsize n (ConCase _ _ _ s) = termsize n s
    termsize n (FnCase _ _ s) = termsize n s
    termsize n (ConstCase _ s) = termsize n s
    termsize n (SucCase _ s) = termsize n s
    termsize n (DefaultCase s) = termsize n s

-- simple terms can be inlined trivially - good for primitives in particular
-- To avoid duplicating work, don't inline something which uses one
-- of its arguments in more than one place

small :: Name -> [Name] -> SC -> Bool
small n args t = let as = findAllUsedArgs t args in
                     length as == length (nub as) &&
                     termsize n t < 10

namesUsed :: SC -> [Name]
namesUsed sc = nub $ nu' [] sc where
    nu' ps (Case n alts) = nub (concatMap (nua ps) alts) \\ [n]
    nu' ps (ProjCase t alts) = nub $ (nut ps t ++
                                      (concatMap (nua ps) alts))
    nu' ps (STerm t)     = nub $ nut ps t
    nu' ps _ = []

    nua ps (ConCase n i args sc) = nub (nu' (ps ++ args) sc) \\ args
    nua ps (FnCase n args sc) = nub (nu' (ps ++ args) sc) \\ args
    nua ps (ConstCase _ sc) = nu' ps sc
    nua ps (SucCase _ sc) = nu' ps sc
    nua ps (DefaultCase sc) = nu' ps sc

    nut ps (P _ n _) | n `elem` ps = []
                     | otherwise = [n]
    nut ps (App f a) = nut ps f ++ nut ps a
    nut ps (Proj t _) = nut ps t
    nut ps (Bind n (Let t v) sc) = nut ps v ++ nut (n:ps) sc
    nut ps (Bind n b sc) = nut (n:ps) sc
    nut ps _ = []

-- Return all called functions, and which arguments are used in each argument position
-- for the call, in order to help reduce compilation time, and trace all unused
-- arguments

findCalls :: SC -> [Name] -> [(Name, [[Name]])]
findCalls sc topargs = nub $ nu' topargs sc where
    nu' ps (Case n alts) = nub (concatMap (nua (n : ps)) alts)
    nu' ps (ProjCase t alts) = nub (nut ps t ++ concatMap (nua ps) alts)
    nu' ps (STerm t)     = nub $ nut ps t
    nu' ps _ = []

    nua ps (ConCase n i args sc) = nub (nu' (ps ++ args) sc)
    nua ps (FnCase n args sc) = nub (nu' (ps ++ args) sc)
    nua ps (ConstCase _ sc) = nu' ps sc
    nua ps (SucCase _ sc) = nu' ps sc
    nua ps (DefaultCase sc) = nu' ps sc

    nut ps (P Ref n _) | n `elem` ps = []
                     | otherwise = [(n, [])] -- tmp
    nut ps fn@(App f a)
        | (P Ref n _, args) <- unApply fn
             = if n `elem` ps then nut ps f ++ nut ps a
                  else [(n, map argNames args)] ++ concatMap (nut ps) args
        | (P (TCon _ _) n _, _) <- unApply fn = []
        | otherwise = nut ps f ++ nut ps a
    nut ps (Bind n (Let t v) sc) = nut ps v ++ nut (n:ps) sc
    nut ps (Proj t _) = nut ps t
    nut ps (Bind n b sc) = nut (n:ps) sc
    nut ps _ = []

    argNames tm = let ns = directUse tm in
                      filter (\x -> x `elem` ns) topargs

-- Find names which are used directly (i.e. not in a function call) in a term

directUse :: Eq n => TT n -> [n]
directUse (P _ n _) = [n]
directUse (Bind n (Let t v) sc) = nub $ directUse v ++ (directUse sc \\ [n])
                                        ++ directUse t
directUse (Bind n b sc) = nub $ directUse (binderTy b) ++ (directUse sc \\ [n])
directUse fn@(App f a)
    | (P Ref n _, args) <- unApply fn = [] -- need to know what n does with them
    | (P (TCon _ _) n _, args) <- unApply fn = [] -- type constructors not used at runtime 
    | otherwise = nub $ directUse f ++ directUse a
directUse (Proj x i) = nub $ directUse x
directUse _ = []

-- Find all directly used arguments (i.e. used but not in function calls)

findUsedArgs :: SC -> [Name] -> [Name]
findUsedArgs sc topargs = nub (findAllUsedArgs sc topargs)

findAllUsedArgs sc topargs = filter (\x -> x `elem` topargs) (nu' sc) where
    nu' (Case n alts) = n : concatMap nua alts
    nu' (ProjCase t alts) = directUse t ++ concatMap nua alts
    nu' (STerm t)     = directUse t
    nu' _             = []

    nua (ConCase n i args sc) = nu' sc
    nua (FnCase n  args sc)   = nu' sc
    nua (ConstCase _ sc)      = nu' sc
    nua (SucCase _ sc)        = nu' sc
    nua (DefaultCase sc)      = nu' sc

data Phase = CompileTime | RunTime
    deriving (Show, Eq)

-- Generate a simple case tree
-- Work Right to Left

simpleCase :: Bool -> Bool -> Bool ->
              Phase -> FC -> [Type] ->
              [([Name], Term, Term)] ->
              TC CaseDef
simpleCase tc cover reflect phase fc argtys cs
      = sc' tc cover phase fc (filter (\(_, _, r) ->
                                          case r of
                                            Impossible -> False
                                            _ -> True) cs)
          where
 sc' tc cover phase fc []
                 = return $ CaseDef [] (UnmatchedCase "No pattern clauses") []
 sc' tc cover phase fc cs
      = let proj       = phase == RunTime
            vnames     = fstT (head cs)
            pats       = map (\ (avs, l, r) ->
                                   (avs, toPats reflect tc l, (l, r))) cs
            chkPats    = mapM chkAccessible pats in
            case chkPats of
                OK pats ->
                    let numargs    = length (fst (head pats))
                        ns         = take numargs args
                        (ns', ps') = order ns pats
                        (tree, st) = runState
                                         (match ns' ps' (defaultCase cover)) 
                                         ([], numargs, [])
                        t          = CaseDef ns (prune proj (depatt ns' tree)) (fstT st) in
                        if proj then return (stripLambdas t) 
                                else if checkSameTypes (lstT st) tree
                                        then return t
                                        else Error (At fc (Msg "Typecase is not allowed"))
                Error err -> Error (At fc err)
    where args = map (\i -> sMN i "e") [0..]
          defaultCase True = STerm Erased
          defaultCase False = UnmatchedCase "Error"
          fstT (x, _, _) = x
          lstT (_, _, x) = x

          chkAccessible (avs, l, c)
               | phase == RunTime || reflect = return (l, c)
               | otherwise = do mapM_ (acc l) avs
                                return (l, c)

          acc [] n = Error (Inaccessible n)
          acc (PV x t : xs) n | x == n = OK ()
          acc (PCon _ _ ps : xs) n = acc (ps ++ xs) n
          acc (PSuc p : xs) n = acc (p : xs) n
          acc (_ : xs) n = acc xs n

-- For each 'Case', make sure every choice is in the same type family,
-- as directed by the variable type (i.e. there is no implicit type casing
-- going on).

checkSameTypes :: [(Name, Type)] -> SC -> Bool
checkSameTypes tys (Case n alts)
        = case lookup n tys of
               Just t -> and (map (checkAlts t) alts)
               _ -> and (map ((checkSameTypes tys).getSC) alts)
  where
    checkAlts t (ConCase n _ _ sc) = isType n t && checkSameTypes tys sc
    checkAlts (Constant t) (ConstCase c sc) = isConstType c t && checkSameTypes tys sc
    checkAlts _ (ConstCase c sc) = False
    checkAlts _ _ = True

    getSC (ConCase _ _ _ sc) = sc
    getSC (FnCase _ _ sc) = sc
    getSC (ConstCase _ sc) = sc
    getSC (SucCase _ sc) = sc
    getSC (DefaultCase sc) = sc
checkSameTypes _ _ = True

-- FIXME: All we're actually doing here is checking that we haven't arrived
-- at a specific constructor for a polymorphic argument. I *think* this
-- is sufficient, but if it turns out not to be, fix it!
isType n t | (P (TCon _ _) _ _, _) <- unApply t = True
isType n t | (P Ref _ _, _) <- unApply t = True
isType n t = False

isConstType (I _) (AType (ATInt ITNative)) = True 
isConstType (BI _) (AType (ATInt ITBig)) = True 
isConstType (Fl _) (AType ATFloat) = True 
isConstType (Ch _) (AType (ATInt ITChar)) = True 
isConstType (Str _) StrType = True 
isConstType (B8 _) (AType (ATInt _)) = True 
isConstType (B16 _) (AType (ATInt _)) = True 
isConstType (B32 _) (AType (ATInt _)) = True 
isConstType (B64 _) (AType (ATInt _)) = True 
isConstType (B8V _) (AType (ATInt _)) = True 
isConstType (B16V _) (AType (ATInt _)) = True 
isConstType (B32V _) (AType (ATInt _)) = True 
isConstType (B64V _) (AType (ATInt _)) = True 
isConstType _ _ = False

data Pat = PCon Name Int [Pat]
         | PConst Const
         | PV Name Type
         | PSuc Pat -- special case for n+1 on Integer
         | PReflected Name [Pat]
         | PAny
         | PTyPat -- typecase, not allowed, inspect last
    deriving Show

-- If there are repeated variables, take the *last* one (could be name shadowing
-- in a where clause, so take the most recent).

toPats :: Bool -> Bool -> Term -> [Pat]
toPats reflect tc f = reverse (toPat reflect tc (getArgs f)) where
   getArgs (App f a) = a : getArgs f
   getArgs _ = []

toPat :: Bool -> Bool -> [Term] -> [Pat]
toPat reflect tc tms = evalState (mapM (\x -> toPat' x []) tms) []
  where
    toPat' (P (DCon t a) n _) args = do args' <- mapM (\x -> toPat' x []) args
                                        return $ PCon n t args'
    -- n + 1
    toPat' (P _ (UN pabi) _)
                  [p, Constant (BI 1)] | pabi == txt "prim__addBigInt"
                                   = do p' <- toPat' p []
                                        return $ PSuc p'
    -- Typecase
--     toPat' (P (TCon t a) n _) args | tc
--                                    = do args' <- mapM (\x -> toPat' x []) args
--                                         return $ PCon n t args'
--     toPat' (Constant (AType (ATInt ITNative))) []
--         | tc = return $ PCon (UN "Int")    1 []
--     toPat' (Constant (AType ATFloat))  [] | tc = return $ PCon (UN "Float")  2 []
--     toPat' (Constant (AType (ATInt ITChar)))  [] | tc = return $ PCon (UN "Char")   3 []
--     toPat' (Constant StrType) [] | tc = return $ PCon (UN "String") 4 []
--     toPat' (Constant PtrType) [] | tc = return $ PCon (UN "Ptr")    5 []
--     toPat' (Constant (AType (ATInt ITBig))) []
--         | tc = return $ PCon (UN "Integer") 6 []
--     toPat' (Constant (AType (ATInt (ITFixed n)))) []
--         | tc = return $ PCon (UN (fixedN n)) (7 + fromEnum n) [] -- 7-10 inclusive
    toPat' (P Bound n ty)     []   = -- trace (show (n, ty)) $
                                     do ns <- get
                                        if n `elem` ns
                                          then return PAny
                                          else do put (n : ns)
                                                  return (PV n ty)
    toPat' (App f a)  args = toPat' f (a : args)
    toPat' (Constant (AType _)) [] = return PTyPat
    toPat' (Constant StrType) [] = return PTyPat
    toPat' (Constant PtrType) [] = return PTyPat
    toPat' (Constant VoidType) [] = return PTyPat
    toPat' (Constant x) [] = return $ PConst x
    toPat' (Bind n (Pi t) sc) [] | reflect && noOccurrence n sc
          = do t' <- toPat' t []
               sc' <- toPat' sc []
               return $ PReflected (sUN "->") (t':sc':[])
    toPat' (P _ n _) args | reflect
          = do args' <- mapM (\x -> toPat' x []) args
               return $ PReflected n args'
    toPat' t            _  = return PAny

    fixedN IT8 = "Bits8"
    fixedN IT16 = "Bits16"
    fixedN IT32 = "Bits32"
    fixedN IT64 = "Bits64"


data Partition = Cons [Clause]
               | Vars [Clause]
    deriving Show

isVarPat (PV _ _ : ps , _) = True
isVarPat (PAny   : ps , _) = True
isVarPat (PTyPat : ps , _) = True
isVarPat _                 = False

isConPat (PCon _ _ _ : ps, _) = True
isConPat (PReflected _ _ : ps, _) = True
isConPat (PSuc _   : ps, _) = True
isConPat (PConst _   : ps, _) = True
isConPat _                    = False

partition :: [Clause] -> [Partition]
partition [] = []
partition ms@(m : _)
    | isVarPat m = let (vars, rest) = span isVarPat ms in
                       Vars vars : partition rest
    | isConPat m = let (cons, rest) = span isConPat ms in
                       Cons cons : partition rest
partition xs = error $ "Partition " ++ show xs

-- reorder the patterns so that the one with most distinct names
-- comes next. Take rightmost first, otherwise (i.e. pick value rather
-- than dependency)

order :: [Name] -> [Clause] -> ([Name], [Clause])
order [] cs = ([], cs)
order ns [] = (ns, [])
order ns cs = let patnames = transpose (map (zip ns) (map fst cs))
                  pats' = transpose (sortBy moreDistinct (reverse patnames)) in
                  (getNOrder pats', zipWith rebuild pats' cs)
  where
    getNOrder [] = error $ "Failed order on " ++ show (ns, cs)
    getNOrder (c : _) = map fst c

    rebuild patnames clause = (map snd patnames, snd clause)

    moreDistinct xs ys = compare (numNames [] (map snd ys))
                                 (numNames [] (map snd xs))

    numNames xs (PCon n _ _ : ps)
        | not (Left n `elem` xs) = numNames (Left n : xs) ps
    numNames xs (PConst c : ps)
        | not (Right c `elem` xs) = numNames (Right c : xs) ps
    numNames xs (_ : ps) = numNames xs ps
    numNames xs [] = length xs

match :: [Name] -> [Clause] -> SC -- error case
                            -> State CS SC
match [] (([], ret) : xs) err
    = do (ts, v, ntys) <- get
         put (ts ++ (map (fst.snd) xs), v, ntys)
         case snd ret of
            Impossible -> return ImpossibleCase
            tm -> return $ STerm tm -- run out of arguments
match vs cs err = do let ps = partition cs
                     mixture vs ps err

mixture :: [Name] -> [Partition] -> SC -> State CS SC
mixture vs [] err = return err
mixture vs (Cons ms : ps) err = do fallthrough <- mixture vs ps err
                                   conRule vs ms fallthrough
mixture vs (Vars ms : ps) err = do fallthrough <- mixture vs ps err
                                   varRule vs ms fallthrough

data ConType = CName Name Int -- named constructor
             | CFn Name -- reflected function name
             | CSuc -- n+1
             | CConst Const -- constant, not implemented yet
   deriving (Show, Eq)

data Group = ConGroup ConType -- Constructor
                      [([Pat], Clause)] -- arguments and rest of alternative
   deriving Show

conRule :: [Name] -> [Clause] -> SC -> State CS SC
conRule (v:vs) cs err = do groups <- groupCons cs
                           caseGroups (v:vs) groups err

caseGroups :: [Name] -> [Group] -> SC -> State CS SC
caseGroups (v:vs) gs err = do g <- altGroups gs
                              return $ Case v (sort g)
  where
    altGroups [] = return [DefaultCase err]
    altGroups (ConGroup (CName n i) args : cs)
        = do g <- altGroup n i args
             rest <- altGroups cs
             return (g : rest)
    altGroups (ConGroup (CFn n) args : cs)
        = do g <- altFnGroup n args
             rest <- altGroups cs
             return (g : rest)
    altGroups (ConGroup CSuc args : cs)
        = do g <- altSucGroup args
             rest <- altGroups cs
             return (g : rest)
    altGroups (ConGroup (CConst c) args : cs)
        = do g <- altConstGroup c args
             rest <- altGroups cs
             return (g : rest)

    altGroup n i gs = do (newArgs, nextCs) <- argsToAlt gs
                         matchCs <- match (newArgs ++ vs) nextCs err
                         return $ ConCase n i newArgs matchCs
    altFnGroup n gs = do (newArgs, nextCs) <- argsToAlt gs
                         matchCs <- match (newArgs ++ vs) nextCs err
                         return $ FnCase n newArgs matchCs
    altSucGroup gs = do ([newArg], nextCs) <- argsToAlt gs
                        matchCs <- match (newArg:vs) nextCs err
                        return $ SucCase newArg matchCs
    altConstGroup n gs = do (_, nextCs) <- argsToAlt gs
                            matchCs <- match vs nextCs err
                            return $ ConstCase n matchCs

argsToAlt :: [([Pat], Clause)] -> State CS ([Name], [Clause])
argsToAlt [] = return ([], [])
argsToAlt rs@((r, m) : rest)
    = do newArgs <- getNewVars r
         return (newArgs, addRs rs)
  where
    getNewVars [] = return []
    getNewVars ((PV n t) : ns) = do v <- getVar "e" 
                                    (cs, i, ntys) <- get
                                    put (cs, i, (v, t) : ntys)
                                    nsv <- getNewVars ns
                                    return (v : nsv)
    getNewVars (PAny : ns) = do v <- getVar "i"
                                nsv <- getNewVars ns
                                return (v : nsv)
    getNewVars (PTyPat : ns) = do v <- getVar "t"
                                  nsv <- getNewVars ns
                                  return (v : nsv)
    getNewVars (_ : ns) = do v <- getVar "e"
                             nsv <- getNewVars ns
                             return (v : nsv)
    addRs [] = []
    addRs ((r, (ps, res)) : rs) = ((r++ps, res) : addRs rs)

    uniq i (UN n) = MN i n
    uniq i n = n

getVar :: String -> State CS Name
getVar b = do (t, v, ntys) <- get; put (t, v+1, ntys); return (sMN v b)

groupCons :: [Clause] -> State CS [Group]
groupCons cs = gc [] cs
  where
    gc acc [] = return acc
    gc acc ((p : ps, res) : cs) =
        do acc' <- addGroup p ps res acc
           gc acc' cs
    addGroup p ps res acc = case p of
        PCon con i args -> return $ addg (CName con i) args (ps, res) acc
        PConst cval -> return $ addConG cval (ps, res) acc
        PSuc n -> return $ addg CSuc [n] (ps, res) acc
        PReflected fn args -> return $ addg (CFn fn) args (ps, res) acc
        pat -> fail $ show pat ++ " is not a constructor or constant (can't happen)"

    addg c conargs res []
           = [ConGroup c [(conargs, res)]]
    addg c conargs res (g@(ConGroup c' cs):gs)
        | c == c' = ConGroup c (cs ++ [(conargs, res)]) : gs
        | otherwise = g : addg c conargs res gs

    addConG con res [] = [ConGroup (CConst con) [([], res)]]
    addConG con res (g@(ConGroup (CConst n) cs) : gs)
        | con == n = ConGroup (CConst n) (cs ++ [([], res)]) : gs
--         | otherwise = g : addConG con res gs
    addConG con res (g : gs) = g : addConG con res gs

varRule :: [Name] -> [Clause] -> SC -> State CS SC
varRule (v : vs) alts err =
    do alts' <- mapM (repVar v) alts
       match vs alts' err
  where
    repVar v (PV p ty : ps , (lhs, res))
           = do (cs, i, ntys) <- get
                put (cs, i, (v, ty) : ntys)
                return (ps, (lhs, subst p (P Bound v ty) res))
    repVar v (PAny : ps , res) = return (ps, res)
    repVar v (PTyPat : ps , res) = return (ps, res)

-- fix: case e of S k -> f (S k)  ==> case e of S k -> f e

depatt :: [Name] -> SC -> SC
depatt ns tm = dp [] tm
  where
    dp ms (STerm tm) = STerm (applyMaps ms tm)
    dp ms (Case x alts) = Case x (map (dpa ms x) alts)
    dp ms sc = sc

    dpa ms x (ConCase n i args sc)
        = ConCase n i args (dp ((x, (n, args)) : ms) sc)
    dpa ms x (FnCase n args sc)
        = FnCase n args (dp ((x, (n, args)) : ms) sc)
    dpa ms x (ConstCase c sc) = ConstCase c (dp ms sc)
    dpa ms x (SucCase n sc) = SucCase n (dp ms sc)
    dpa ms x (DefaultCase sc) = DefaultCase (dp ms sc)

    applyMaps ms f@(App _ _)
       | (P nt cn pty, args) <- unApply f
            = let args' = map (applyMaps ms) args in
                  applyMap ms nt cn pty args'
        where
          applyMap [] nt cn pty args' = mkApp (P nt cn pty) args'
          applyMap ((x, (n, args)) : ms) nt cn pty args'
            | and ((length args == length args') :
                     (n == cn) : zipWith same args args') = P Ref x Erased
            | otherwise = applyMap ms nt cn pty args'
          same n (P _ n' _) = n == n'
          same _ _ = False

    applyMaps ms (App f a) = App (applyMaps ms f) (applyMaps ms a)
    applyMaps ms t = t

-- FIXME: Do this for SucCase too
prune :: Bool -- ^ Convert single branches to projections (only useful at runtime)
      -> SC -> SC
prune proj (Case n alts)
    = let alts' = filter notErased (map pruneAlt alts) in
          case alts' of
            [] -> ImpossibleCase
            as@[ConCase cn i args sc] -> if proj then mkProj n 0 args sc
                                                 else Case n as
            as@[SucCase cn sc] -> if proj then mkProj n (-1) [cn] sc 
                                          else Case n as
            as@[ConstCase _ sc] -> prune proj sc
            -- Bit of a hack here! The default case will always be 0, make sure
            -- it gets caught first.
            [s@(SucCase _ _), DefaultCase dc]
                -> Case n [ConstCase (BI 0) dc, s]
            as  -> Case n as
    where pruneAlt (ConCase cn i ns sc) = ConCase cn i ns (prune proj sc)
          pruneAlt (FnCase cn ns sc) = FnCase cn ns (prune proj sc)
          pruneAlt (ConstCase c sc) = ConstCase c (prune proj sc)
          pruneAlt (SucCase n sc) = SucCase n (prune proj sc)
          pruneAlt (DefaultCase sc) = DefaultCase (prune proj sc)

          notErased (DefaultCase (STerm Erased)) = False
          notErased (DefaultCase ImpossibleCase) = False
          notErased _ = True

          mkProj n i []       sc = prune proj sc
          mkProj n i (x : xs) sc = mkProj n (i + 1) xs (projRep x n i sc)

          -- Change every 'n' in sc to 'n-1'
--           mkProjS n cn sc = prune proj (fmap projn sc) where
--              projn pn@(P _ n' _) 
--                 | cn == n' = App (App (P Ref (UN "prim__subBigInt") Erased)
--                                       (P Bound n Erased)) (Constant (BI 1))
--              projn t = t

          projRep :: Name -> Name -> Int -> SC -> SC
          projRep arg n i (Case x alts)
                | x == arg = ProjCase (Proj (P Bound n Erased) i)
                                      (map (projRepAlt arg n i) alts)
                | otherwise = Case x (map (projRepAlt arg n i) alts)
          projRep arg n i (ProjCase t alts)
                = ProjCase (projRepTm arg n i t) (map (projRepAlt arg n i) alts)
          projRep arg n i (STerm t) = STerm (projRepTm arg n i t)
          projRep arg n i c = c -- unmatched

          projRepAlt arg n i (ConCase cn t args rhs)
              = ConCase cn t args (projRep arg n i rhs)
          projRepAlt arg n i (FnCase cn args rhs)
              = FnCase cn args (projRep arg n i rhs)
          projRepAlt arg n i (ConstCase t rhs)
              = ConstCase t (projRep arg n i rhs)
          projRepAlt arg n i (SucCase sn rhs)
              = SucCase sn (projRep arg n i rhs)
          projRepAlt arg n i (DefaultCase rhs)
              = DefaultCase (projRep arg n i rhs)

          projRepTm arg n i t = subst arg (Proj (P Bound n Erased) i) t

prune _ t = t

stripLambdas :: CaseDef -> CaseDef
stripLambdas (CaseDef ns (STerm (Bind x (Lam _) sc)) tm)
    = stripLambdas (CaseDef (ns ++ [x]) (STerm (instantiate (P Bound x Erased) sc)) tm)
stripLambdas x = x





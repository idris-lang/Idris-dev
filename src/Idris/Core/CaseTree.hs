{-# LANGUAGE PatternGuards, DeriveFunctor, TypeSynonymInstances #-}

module Idris.Core.CaseTree(CaseDef(..), SC, SC'(..), CaseAlt, CaseAlt'(..), ErasureInfo,
                     Phase(..), CaseTree, CaseType(..),
                     simpleCase, small, namesUsed, findCalls, findUsedArgs,
                     substSC, substAlt, mkForce) where

import Idris.Core.TT

import Control.Applicative hiding (Const)
import Control.Monad.State
import Control.Monad.Reader
import Data.Maybe
import Data.List hiding (partition)
import qualified Data.List(partition)
import Debug.Trace

data CaseDef = CaseDef [Name] !SC [Term]
    deriving Show

-- Note: The case-tree elaborator only produces (Case n alts)-cases;
-- in other words, it never inspects anything else than variables.
--
-- ProjCase is a special powerful case construct that allows inspection
-- of compound terms. Occurrences of ProjCase arise no earlier than
-- in the function `prune` as a means of optimisation
-- of already built case trees.
--
-- While the intermediate representation (follows in the pipeline, named LExp)
-- allows casing on arbitrary terms, here we choose to maintain the distinction
-- in order to allow for better optimisation opportunities.
--
data SC' t = Case CaseType Name [CaseAlt' t]  -- ^ invariant: lowest tags first
           | ProjCase t [CaseAlt' t] -- ^ special case for projections/thunk-forcing before inspection
           | STerm !t
           | UnmatchedCase String -- ^ error message
           | ImpossibleCase -- ^ already checked to be impossible
    deriving (Eq, Ord, Functor)
{-!
deriving instance Binary SC'
deriving instance NFData SC'
!-}

data CaseType = Updatable | Shared   
   deriving (Eq, Ord, Show)

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
        show' i (Case up n alts) = "case" ++ u ++ show n ++ " of\n" ++ indent i ++
                                    showSep ("\n" ++ indent i) (map (showA i) alts)
            where u = case up of
                           Updatable -> "! "
                           Shared -> " "
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
    termsize n (Case _ n' as) = termsize n as
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
    nu' ps (Case _ n alts) = nub (concatMap (nua ps) alts) \\ [n]
    nu' ps (ProjCase t alts) = nub $ nut ps t ++ concatMap (nua ps) alts
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
    nu' ps (Case _ n alts) = nub (concatMap (nua (n : ps)) alts)
    nu' ps (ProjCase t alts) = nub $ nut ps t ++ concatMap (nua ps) alts
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

directUse :: TT Name -> [Name]
directUse (P _ n _) = [n]
directUse (Bind n (Let t v) sc) = nub $ directUse v ++ (directUse sc \\ [n])
                                        ++ directUse t
directUse (Bind n b sc) = nub $ directUse (binderTy b) ++ (directUse sc \\ [n])
directUse fn@(App f a)
    | (P Ref (UN pfk) _, [App e w]) <- unApply fn,
         pfk == txt "prim_fork"
             = directUse e ++ directUse w -- HACK so that fork works
    | (P Ref (UN fce) _, [_, _, a]) <- unApply fn,
         fce == txt "Force"
             = directUse a -- forcing a value counts as a use
    | (P Ref n _, args) <- unApply fn = [] -- need to know what n does with them
    | (P (TCon _ _) n _, args) <- unApply fn = [] -- type constructors not used at runtime 
    | otherwise = nub $ directUse f ++ directUse a
directUse (Proj x i) = nub $ directUse x
directUse _ = []

-- Find all directly used arguments (i.e. used but not in function calls)

findUsedArgs :: SC -> [Name] -> [Name]
findUsedArgs sc topargs = nub (findAllUsedArgs sc topargs)

findAllUsedArgs sc topargs = filter (\x -> x `elem` topargs) (nu' sc) where
    nu' (Case _ n alts) = n : concatMap nua alts
    nu' (ProjCase t alts) = directUse t ++ concatMap nua alts
    nu' (STerm t)     = directUse t
    nu' _             = []

    nua (ConCase n i args sc) = nu' sc
    nua (FnCase n  args sc)   = nu' sc
    nua (ConstCase _ sc)      = nu' sc
    nua (SucCase _ sc)        = nu' sc
    nua (DefaultCase sc)      = nu' sc

-- Return whether name is used anywhere in a case tree
isUsed :: SC -> Name -> Bool
isUsed sc n = used sc where

  used (Case _ n' alts) = n == n' || or (map usedA alts)
  used (ProjCase t alts) = n `elem` freeNames t || or (map usedA alts)
  used (STerm t) = n `elem` freeNames t
  used _ = False

  usedA (ConCase _ _ args sc) = used sc
  usedA (FnCase _ args sc) = used sc
  usedA (ConstCase _ sc) = used sc
  usedA (SucCase _ sc) = used sc
  usedA (DefaultCase sc) = used sc

type ErasureInfo = Name -> [Int]  -- name to list of inaccessible arguments; empty list if name not found
type CaseBuilder a = ReaderT ErasureInfo (State CS) a

runCaseBuilder :: ErasureInfo -> CaseBuilder a -> (CS -> (a, CS))
runCaseBuilder ei bld = runState $ runReaderT bld ei

data Phase = CompileTime | RunTime
    deriving (Show, Eq)

-- Generate a simple case tree
-- Work Right to Left

simpleCase :: Bool -> Bool -> Bool ->
              Phase -> FC -> [Int] -> [Type] ->
              [([Name], Term, Term)] ->
              ErasureInfo ->
              TC CaseDef
simpleCase tc cover reflect phase fc inacc argtys cs erInfo
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
                        (ns', ps') = order [(n, i `elem` inacc) | (i,n) <- zip [0..] ns] pats
                        (tree, st) = runCaseBuilder erInfo
                                         (match ns' ps' (defaultCase cover)) 
                                         ([], numargs, [])
                        t          = CaseDef ns (prune proj (depatt ns' tree)) (fstT st) in
                        if proj then return (stripLambdas t) 
                                else return t
-- FIXME: This check is not quite right in some cases, and is breaking
-- perfectly valid code!
--                                      if checkSameTypes (lstT st) tree
--                                         then return t
--                                         else Error (At fc (Msg "Typecase is not allowed"))
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
          acc (PCon _ _ _ ps : xs) n = acc (ps ++ xs) n
          acc (PSuc p : xs) n = acc (p : xs) n
          acc (_ : xs) n = acc xs n

-- For each 'Case', make sure every choice is in the same type family,
-- as directed by the variable type (i.e. there is no implicit type casing
-- going on).

checkSameTypes :: [(Name, Type)] -> SC -> Bool
checkSameTypes tys (Case _ n alts)
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

data Pat = PCon Bool Name Int [Pat]
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
toPat reflect tc = map $ toPat' []
  where
    toPat' [_,_,arg] (P (DCon t a uniq) nm@(UN n) _)
        | n == txt "Delay"
        = PCon uniq nm t [PAny, PAny, toPat' [] arg]

    toPat' args (P (DCon t a uniq) nm@(NS (UN n) [own]) _)
        | n == txt "Read" && own == txt "Ownership"
        = PCon False nm t (map shareCons (map (toPat' []) args))
      where shareCons (PCon _ n i ps) = PCon False n i (map shareCons ps)
            shareCons p = p

    toPat' args (P (DCon t a uniq) n _)
        = PCon uniq n t $ map (toPat' []) args

    -- n + 1
    toPat' [p, Constant (BI 1)] (P _ (UN pabi) _)
        | pabi == txt "prim__addBigInt"
        = PSuc $ toPat' [] p

    toPat' []   (P Bound n ty) = PV n ty
    toPat' args (App f a)      = toPat' (a : args) f
    toPat' [] (Constant (AType _)) = PTyPat
    toPat' [] (Constant StrType)   = PTyPat
    toPat' [] (Constant PtrType)   = PTyPat
    toPat' [] (Constant VoidType)  = PTyPat
    toPat' [] (Constant x)         = PConst x

    toPat' [] (Bind n (Pi t _) sc)
        | reflect && noOccurrence n sc
        = PReflected (sUN "->") [toPat' [] t, toPat' [] sc]

    toPat' args (P _ n _)
        | reflect
        = PReflected n $ map (toPat' []) args

    toPat' _ t = PAny

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

isConPat (PCon _ _ _ _ : ps, _) = True
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
--
-- The first argument means [(Name, IsInaccessible)].

order :: [(Name, Bool)] -> [Clause] -> ([Name], [Clause])
order []  cs = ([], cs)
order ns' [] = (map fst ns', [])
order ns' cs = let patnames = transpose (map (zip ns') (map fst cs))
                   -- only sort the arguments where there is no clash in
                   -- constructor tags between families, and no constructor/constant
                   -- clash, because otherwise we can't reliable make the
                   -- case distinction on evaluation
                   (patnames_ord, patnames_rest) 
                        = Data.List.partition (noClash . map snd) patnames
                   -- note: sortBy . reverse is not nonsense because sortBy is stable
                   pats' = transpose (sortBy moreDistinct (reverse patnames_ord) 
                                         ++ patnames_rest) in
                   (getNOrder pats', zipWith rebuild pats' cs)
  where
    getNOrder [] = error $ "Failed order on " ++ show (map fst ns', cs)
    getNOrder (c : _) = map (fst . fst) c

    rebuild patnames clause = (map snd patnames, snd clause)

    noClash [] = True
    noClash (p : ps) = not (any (clashPat p) ps) && noClash ps

    clashPat (PCon _ _ _ _) (PConst _) = True
    clashPat (PConst _) (PCon _ _ _ _) = True
    clashPat (PCon _ _ _ _) (PSuc _) = True
    clashPat (PSuc _) (PCon _ _ _ _) = True
    clashPat (PCon _ n i _) (PCon _ n' i' _) | i == i' = n /= n'
    clashPat _ _ = False

    -- this compares (+isInaccessible, -numberOfCases)
    moreDistinct xs ys = compare (snd . fst . head $ xs, numNames [] (map snd ys))
                                 (snd . fst . head $ ys, numNames [] (map snd xs))

    numNames xs (PCon _ n _ _ : ps)
        | not (Left n `elem` xs) = numNames (Left n : xs) ps
    numNames xs (PConst c : ps)
        | not (Right c `elem` xs) = numNames (Right c : xs) ps
    numNames xs (_ : ps) = numNames xs ps
    numNames xs [] = length xs

match :: [Name] -> [Clause] -> SC -- error case
                            -> CaseBuilder SC
match [] (([], ret) : xs) err
    = do (ts, v, ntys) <- get
         put (ts ++ (map (fst.snd) xs), v, ntys)
         case snd ret of
            Impossible -> return ImpossibleCase
            tm -> return $ STerm tm -- run out of arguments
match vs cs err = do let ps = partition cs
                     mixture vs ps err

mixture :: [Name] -> [Partition] -> SC -> CaseBuilder SC
mixture vs [] err = return err
mixture vs (Cons ms : ps) err = do fallthrough <- mixture vs ps err
                                   conRule vs ms fallthrough
mixture vs (Vars ms : ps) err = do fallthrough <- mixture vs ps err
                                   varRule vs ms fallthrough

-- Return the list of inaccessible arguments of a data constructor.
inaccessibleArgs :: Name -> CaseBuilder [Int]
inaccessibleArgs n = do
    getInaccessiblePositions <- ask  -- this function is the only thing in the environment
    return $ getInaccessiblePositions n

data ConType = CName Name Int -- named constructor
             | CFn Name -- reflected function name
             | CSuc -- n+1
             | CConst Const -- constant, not implemented yet
   deriving (Show, Eq)

data Group = ConGroup Bool -- Uniqueness flag
                      ConType -- Constructor
                      [([Pat], Clause)] -- arguments and rest of alternative
   deriving Show

conRule :: [Name] -> [Clause] -> SC -> CaseBuilder SC
conRule (v:vs) cs err = do groups <- groupCons cs
                           caseGroups (v:vs) groups err

caseGroups :: [Name] -> [Group] -> SC -> CaseBuilder SC
caseGroups (v:vs) gs err = do g <- altGroups gs
                              return $ Case (getShared gs) v (sort g)
  where
    getShared (ConGroup True _ _ : _) = Updatable
    getShared _ = Shared

    altGroups [] = return [DefaultCase err]

    altGroups (ConGroup _ (CName n i) args : cs)
        = (:) <$> altGroup n i args <*> altGroups cs

    altGroups (ConGroup _ (CFn n) args : cs)
        = (:) <$> altFnGroup n args <*> altGroups cs

    altGroups (ConGroup _ CSuc args : cs)
        = (:) <$> altSucGroup args <*> altGroups cs

    altGroups (ConGroup _ (CConst c) args : cs)
        = (:) <$> altConstGroup c args <*> altGroups cs

    altGroup n i args 
         = do inacc <- inaccessibleArgs n
              (newVars, accVars, inaccVars, nextCs) <- argsToAlt inacc args
              matchCs <- match (accVars ++ vs ++ inaccVars) nextCs err
              return $ ConCase n i newVars matchCs

    altFnGroup n args = do (newVars, _, [], nextCs) <- argsToAlt [] args
                           matchCs <- match (newVars ++ vs) nextCs err
                           return $ FnCase n newVars matchCs

    altSucGroup args = do ([newVar], _, [], nextCs) <- argsToAlt [] args
                          matchCs <- match (newVar:vs) nextCs err
                          return $ SucCase newVar matchCs

    altConstGroup n args = do (_, _, [], nextCs) <- argsToAlt [] args
                              matchCs <- match vs nextCs err
                              return $ ConstCase n matchCs

-- Returns:
--   * names of all variables arising from match
--   * names of accessible variables (subset of all variables)
--   * names of inaccessible variables (subset of all variables)
--   * clauses corresponding to (accVars ++ origVars ++ inaccVars)
argsToAlt :: [Int] -> [([Pat], Clause)] -> CaseBuilder ([Name], [Name], [Name], [Clause])
argsToAlt _ [] = return ([], [], [], [])
argsToAlt inacc rs@((r, m) : rest) = do
    newVars <- getNewVars r
    let (accVars, inaccVars) = partitionAcc newVars
    return (newVars, accVars, inaccVars, addRs rs)
  where
    -- Create names for new variables arising from the given patterns.
    getNewVars :: [Pat] -> CaseBuilder [Name]
    getNewVars [] = return []
    getNewVars ((PV n t) : ns) = do v <- getVar "e" 
                                    nsv <- getNewVars ns

                                    -- Record the type of the variable.
                                    --
                                    -- It seems that the ordering is not important
                                    -- and we can put (v,t) always in front of "ntys"
                                    -- (the varName-type pairs seem to represent a mapping).
                                    --
                                    -- The code that reads this is currently
                                    -- commented out, anyway.
                                    (cs, i, ntys) <- get
                                    put (cs, i, (v, t) : ntys)

                                    return (v : nsv)

    getNewVars (PAny   : ns) = (:) <$> getVar "i" <*> getNewVars ns
    getNewVars (PTyPat : ns) = (:) <$> getVar "t" <*> getNewVars ns
    getNewVars (_      : ns) = (:) <$> getVar "e" <*> getNewVars ns

    -- Partition a list of things into (accessible, inaccessible) things,
    -- according to the list of inaccessible indices.
    partitionAcc xs =
        ( [x | (i,x) <- zip [0..] xs, i `notElem` inacc]
        , [x | (i,x) <- zip [0..] xs, i    `elem` inacc]
        )

    addRs [] = []
    addRs ((r, (ps, res)) : rs) = ((acc++ps++inacc, res) : addRs rs)
      where
        (acc, inacc) = partitionAcc r

    uniq i (UN n) = MN i n
    uniq i n = n

getVar :: String -> CaseBuilder Name
getVar b = do (t, v, ntys) <- get; put (t, v+1, ntys); return (sMN v b)

groupCons :: [Clause] -> CaseBuilder [Group]
groupCons cs = gc [] cs
  where
    gc acc [] = return acc
    gc acc ((p : ps, res) : cs) =
        do acc' <- addGroup p ps res acc
           gc acc' cs
    addGroup p ps res acc = case p of
        PCon uniq con i args -> return $ addg uniq (CName con i) args (ps, res) acc
        PConst cval -> return $ addConG cval (ps, res) acc
        PSuc n -> return $ addg False CSuc [n] (ps, res) acc
        PReflected fn args -> return $ addg False (CFn fn) args (ps, res) acc
        pat -> fail $ show pat ++ " is not a constructor or constant (can't happen)"

    addg uniq c conargs res []
           = [ConGroup uniq c [(conargs, res)]]
    addg uniq c conargs res (g@(ConGroup _ c' cs):gs)
        | c == c' = ConGroup uniq c (cs ++ [(conargs, res)]) : gs
        | otherwise = g : addg uniq c conargs res gs

    addConG con res [] = [ConGroup False (CConst con) [([], res)]]
    addConG con res (g@(ConGroup False (CConst n) cs) : gs)
        | con == n = ConGroup False (CConst n) (cs ++ [([], res)]) : gs
--         | otherwise = g : addConG con res gs
    addConG con res (g : gs) = g : addConG con res gs

varRule :: [Name] -> [Clause] -> SC -> CaseBuilder SC
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
    dp ms (Case up x alts) = Case up x (map (dpa ms x) alts)
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
prune proj (Case up n alts) = case alts' of
    [] -> ImpossibleCase

    -- Projection transformations prevent us from seeing some uses of ctor fields
    -- because they delete information about which ctor is being used.
    -- Consider:
    --   f (X x) = ...  x  ...
    -- vs.
    --   f  x    = ... x!0 ...
    --
    -- Hence, we disable this step.
    -- TODO: re-enable this in toIR
    --
    -- as@[ConCase cn i args sc]
    --     | proj -> mkProj n 0 args (prune proj sc)
    -- mkProj n i xs sc = foldr (\x -> projRep x n i) sc xs

    -- If none of the args are used in the sc, however, we can just replace it
    -- with sc
    as@[ConCase cn i args sc]
        | proj -> let sc' = prune proj sc in
                      if any (isUsed sc') args  
                         then Case up n [ConCase cn i args sc']
                         else sc' 

    [SucCase cn sc]
        | proj
        -> projRep cn n (-1) $ prune proj sc

    [ConstCase _ sc]
        -> prune proj sc

    -- Bit of a hack here! The default case will always be 0, make sure
    -- it gets caught first.
    [s@(SucCase _ _), DefaultCase dc]
        -> Case up n [ConstCase (BI 0) dc, s]

    as  -> Case up n as
  where
    alts' = filter (not . erased) $ map pruneAlt alts

    pruneAlt (ConCase cn i ns sc) = ConCase cn i ns (prune proj sc)
    pruneAlt (FnCase cn ns sc) = FnCase cn ns (prune proj sc)
    pruneAlt (ConstCase c sc) = ConstCase c (prune proj sc)
    pruneAlt (SucCase n sc) = SucCase n (prune proj sc)
    pruneAlt (DefaultCase sc) = DefaultCase (prune proj sc)

    erased (DefaultCase (STerm Erased)) = True
    erased (DefaultCase ImpossibleCase) = True
    erased _ = False

    projRep :: Name -> Name -> Int -> SC -> SC
    projRep arg n i (Case up x alts) | x == arg
        = ProjCase (Proj (P Bound n Erased) i) $ map (projRepAlt arg n i) alts
    projRep arg n i (Case up x alts)
        = Case up x (map (projRepAlt arg n i) alts)
    projRep arg n i (ProjCase t alts)
        = ProjCase (projRepTm arg n i t) $ map (projRepAlt arg n i) alts
    projRep arg n i (STerm t) = STerm (projRepTm arg n i t)
    projRep arg n i c = c

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

substSC :: Name -> Name -> SC -> SC
substSC n repl (Case up n' alts)
    | n == n'   = Case up repl (map (substAlt n repl) alts)
    | otherwise = Case up n'   (map (substAlt n repl) alts)
substSC n repl (STerm t) = STerm $ subst n (P Bound repl Erased) t
substSC n repl (UnmatchedCase errmsg) = UnmatchedCase errmsg
substSC n repl  ImpossibleCase = ImpossibleCase
substSC n repl sc = error $ "unsupported in substSC: " ++ show sc

substAlt :: Name -> Name -> CaseAlt -> CaseAlt
substAlt n repl (ConCase cn a ns sc) = ConCase cn a ns (substSC n repl sc)
substAlt n repl (FnCase fn ns sc)    = FnCase fn ns (substSC n repl sc)
substAlt n repl (ConstCase c sc)     = ConstCase c (substSC n repl sc)
substAlt n repl (SucCase n' sc)
    | n == n'   = SucCase n  (substSC n repl sc)
    | otherwise = SucCase n' (substSC n repl sc)
substAlt n repl (DefaultCase sc)     = DefaultCase (substSC n repl sc)

-- mkForce n' n t updates the tree t under the assumption that
-- n' = force n (so basically updating n to n')
mkForce :: Name -> Name -> SC -> SC
mkForce = mkForceSC
  where
    mkForceSC n arg (Case up x alts) | x == arg
        = Case up n $ map (mkForceAlt n arg) alts

    mkForceSC n arg (Case up x alts)
        = Case up x (map (mkForceAlt n arg) alts)

    mkForceSC n arg (ProjCase t alts)
        = ProjCase t $ map (mkForceAlt n arg) alts

    mkForceSC n arg c = c

    mkForceAlt n arg (ConCase cn t args rhs)
        = ConCase cn t args (mkForceSC n arg rhs)
    mkForceAlt n arg (FnCase cn args rhs)
        = FnCase cn args (mkForceSC n arg rhs)
    mkForceAlt n arg (ConstCase t rhs)
        = ConstCase t (mkForceSC n arg rhs)
    mkForceAlt n arg (SucCase sn rhs)
        = SucCase sn (mkForceSC n arg rhs)
    mkForceAlt n arg (DefaultCase rhs)
        = DefaultCase (mkForceSC n arg rhs)

    forceTm n arg t = subst n arg t

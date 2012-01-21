module Core.CaseTree(CaseDef(..), SC(..), CaseAlt(..), CaseTree,
                     simpleCase, small) where

import Core.TT

import Control.Monad.State
import Debug.Trace

data CaseDef = CaseDef [Name] SC
    deriving Show

data SC = Case Name [CaseAlt]
        | STerm Term
        | UnmatchedCase String -- error message
    deriving Show
{-! 
deriving instance Binary SC 
!-}

data CaseAlt = ConCase Name Int [Name] SC
             | ConstCase Const         SC
             | DefaultCase             SC
    deriving Show
{-! 
deriving instance Binary CaseAlt 
!-}

type CaseTree = SC
type Clause   = ([Pat], (Term, Term))
type CS = ([Term], Int)

-- simple terms can be inlined trivially - good for primitives in particular
small :: SC -> Bool
-- small (STerm t) = True
small _ = False

simpleCase :: Bool -> Bool -> [(Term, Term)] -> CaseDef
simpleCase tc cover [] 
                 = CaseDef [] (UnmatchedCase "No pattern clauses") []
simpleCase tc cover cs 
      = let pats       = map (\ (l, r) -> (toPats tc l, (l, r))) cs
            numargs    = length (fst (head pats)) 
            ns         = take numargs args
            (tree, st) = runState (match ns pats (defaultCase cover)) ([], numargs) in
            CaseDef ns (prune tree) (fst st)
    where args = map (\i -> MN i "e") [0..]
          defaultCase True = STerm Erased
          defaultCase False = UnmatchedCase "Error"

data Pat = PCon Name Int [Pat]
         | PConst Const
         | PV Name
         | PAny
    deriving Show

-- If there are repeated variables, take the *last* one (could be name shadowing
-- in a where clause, so take the most recent).

toPats :: Bool -> Term -> [Pat]
toPats tc f = reverse (toPat tc (getArgs f)) where
   getArgs (App f a) = a : getArgs f
   getArgs _ = []

toPat :: Bool -> [Term] -> [Pat]
toPat tc tms = evalState (mapM (\x -> toPat' x []) tms) []
  where
    toPat' (P (DCon t a) n _) args = do args' <- mapM (\x -> toPat' x []) args
                                        return $ PCon n t args'
    -- Typecase
    toPat' (P (TCon t a) n _) args | tc 
                                   = do args' <- mapM (\x -> toPat' x []) args
                                        return $ PCon n t args'
    toPat' (Constant IType)   [] | tc = return $ PCon (UN "Int")    1 [] 
    toPat' (Constant FlType)  [] | tc = return $ PCon (UN "Float")  2 [] 
    toPat' (Constant ChType)  [] | tc = return $ PCon (UN "Char")   3 [] 
    toPat' (Constant StrType) [] | tc = return $ PCon (UN "String") 4 [] 
    toPat' (Constant PtrType) [] | tc = return $ PCon (UN "Ptr")    5 [] 
    toPat' (Constant BIType)  [] | tc = return $ PCon (UN "Integer") 6 [] 

    toPat' (P Bound n _)      []   = do ns <- get
                                        if n `elem` ns 
                                          then return PAny 
                                          else do put (n : ns)
                                                  return (PV n)
    toPat' (App f a)          args = toPat' f (a : args)
    toPat' (Constant (I c)) [] = return $ PConst (I c) 
    toPat' _                _  = return PAny


data Partition = Cons [Clause]
               | Vars [Clause]

isVarPat (PV _ : ps , _) = True
isVarPat (PAny : ps , _) = True
isVarPat _               = False

isConPat (PCon _ _ _ : ps, _) = True
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

match :: [Name] -> [Clause] -> SC -- error case
                            -> State CS SC
match [] (([], ret) : xs) err 
    = do (ts, v) <- get
         put (ts ++ (map (fst.snd) xs), v)
         return $ STerm (snd ret) -- run out of arguments
match vs cs err = do cs <- mixture vs (partition cs) err
                     return cs

mixture :: [Name] -> [Partition] -> SC -> State CS SC
mixture vs [] err = return err
mixture vs (Cons ms : ps) err = do fallthrough <- mixture vs ps err
                                   conRule vs ms fallthrough
mixture vs (Vars ms : ps) err = do fallthrough <- mixture vs ps err
                                   varRule vs ms fallthrough

data ConType = CName Name Int -- named constructor
             | CConst Const -- constant, not implemented yet

data Group = ConGroup ConType -- Constructor
                      [([Pat], Clause)] -- arguments and rest of alternative

conRule :: [Name] -> [Clause] -> SC -> State CS SC
conRule (v:vs) cs err = do groups <- groupCons cs
                           caseGroups (v:vs) groups err

caseGroups :: [Name] -> [Group] -> SC -> State CS SC
caseGroups (v:vs) gs err = do g <- altGroups gs
                              return $ Case v g
  where
    altGroups [] = return [DefaultCase err]
    altGroups (ConGroup (CName n i) args : cs)
        = do g <- altGroup n i args
             rest <- altGroups cs
             return (g : rest)
    altGroups (ConGroup (CConst c) args : cs) 
        = do g <- altConstGroup c args
             rest <- altGroups cs
             return (g : rest)

    altGroup n i gs = do (newArgs, nextCs) <- argsToAlt gs
                         matchCs <- match (newArgs ++ vs) nextCs err
                         return $ ConCase n i newArgs matchCs
    altConstGroup n gs = do (_, nextCs) <- argsToAlt gs
                            matchCs <- match vs nextCs err
                            return $ ConstCase n matchCs

argsToAlt :: [([Pat], Clause)] -> State CS ([Name], [Clause])
argsToAlt [] = return ([], [])
argsToAlt rs@((r, m) : _)
    = do newArgs <- getNewVars r
         return (newArgs, addRs rs)
  where 
    getNewVars [] = return []
    getNewVars ((PV n) : ns) = do nsv <- getNewVars ns
                                  return (n : nsv)
    getNewVars (_ : ns) = do v <- getVar
                             nsv <- getNewVars ns
                             return (v : nsv)
    addRs [] = []
    addRs ((r, (ps, res)) : rs) = ((r++ps, res) : addRs rs)

getVar :: State CS Name
getVar = do (t, v) <- get; put (t, v+1); return (MN v "e")

groupCons :: [Clause] -> State CS [Group]
groupCons cs = gc [] cs
  where
    gc acc [] = return acc
    gc acc ((p : ps, res) : cs) = 
        do acc' <- addGroup p ps res acc
           gc acc' cs
    addGroup p ps res acc = case p of
        PCon con i args -> return $ addg con i args (ps, res) acc
        PConst cval -> return $ addConG cval (ps, res) acc
        pat -> fail $ show pat ++ " is not a constructor or constant (can't happen)"

    addg con i conargs res [] = [ConGroup (CName con i) [(conargs, res)]]
    addg con i conargs res (g@(ConGroup (CName n j) cs):gs)
        | i == j = ConGroup (CName n i) (cs ++ [(conargs, res)]) : gs
        | otherwise = g : addg con i conargs res gs

    addConG con res [] = [ConGroup (CConst con) [([], res)]]
    addConG con res (g@(ConGroup (CConst n) cs) : gs)
        | con == n = ConGroup (CConst n) (cs ++ [([], res)]) : gs
        | otherwise = g : addConG con res gs

varRule :: [Name] -> [Clause] -> SC -> State CS SC
varRule (v : vs) alts err =
    do let alts' = map (repVar v) alts
       match vs alts' err
  where
    repVar v (PV p : ps , (lhs, res)) = (ps, (lhs, subst p (P Bound v (V 0)) res))
    repVar v (PAny : ps , res) = (ps, res)

prune :: SC -> SC
prune (Case n alts) 
    = let alts' = map pruneAlt $ 
                      filter notErased alts in
          case alts' of
            [] -> STerm Erased
            as  -> Case n as
    where pruneAlt (ConCase n i ns sc) = ConCase n i ns (prune sc)
          pruneAlt (ConstCase c sc) = ConstCase c (prune sc)
          pruneAlt (DefaultCase sc) = DefaultCase (prune sc)

          notErased (DefaultCase (STerm Erased)) = False
          notErased _ = True
prune t = t



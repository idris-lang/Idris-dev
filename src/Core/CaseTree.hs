module Core.CaseTree(CaseDef(..), SC(..), CaseAlt(..), CaseTree,
                     simpleCase) where

import Core.TT

import Control.Monad.State
import Debug.Trace

data CaseDef = CaseDef [Name] SC
    deriving Show

data SC = Case Name [CaseAlt]
        | STerm Term
        | UnmatchedCase String -- error message
    deriving Show

data CaseAlt = ConCase Name Int [Name] SC
             | ConstCase Const         SC
             | DefaultCase             SC
    deriving Show

type CaseTree = SC
type Clause   = ([Pat], Term)
type CS = Int

simpleCase :: [(Term, Term)] -> CaseDef
simpleCase [] = CaseDef [] (UnmatchedCase "No pattern clauses")
simpleCase cs = let pats    = map (\ (l, r) -> (toPats l, r)) cs
                    numargs = length (fst (head pats)) 
                    ns      = take numargs args in
                    CaseDef ns (evalState (match ns pats (UnmatchedCase "Error")) numargs)
    where args = map (\i -> MN i "e") [0..]

data Pat = PCon Name Int [Pat]
         | PConst Const
         | PV Name
         | PAny
    deriving Show

-- If there are repeated variables, take the *last* one (could be name shadowing
-- in a where clause, so take the most recent).

toPats :: Term -> [Pat]
toPats f = reverse (toPat (getArgs f)) where
   getArgs (App f a) = a : getArgs f
   getArgs _ = []

toPat :: [Term] -> [Pat]
toPat tms = evalState (mapM (\x -> toPat' x []) tms) []
  where
    toPat' (P (DCon t a) n _) args = do args' <- mapM (\x -> toPat' x []) args
                                        return $ PCon n t args'
    toPat' (P Bound n _)      []   = do ns <- get
                                        if n `elem` ns 
                                          then return PAny 
                                          else do put (n : ns)
                                                  return (PV n)
    toPat' (App f a)          args = toPat' f (a : args)
    toPat' (Constant c)       args 
        | isType c  = return PAny
        | otherwise = return $ PConst c
    toPat' _                  _    = return PAny

    isType (I _) = False
    isType (Fl _) = False
    isType (Str _) = False
    isType (Ch _) = False
    isType _ = True

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
match [] (([], ret) : _) err = return $ STerm ret -- run out of arguments
match vs cs err = mixture vs (partition cs) err

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
getVar = do v <- get; put (v+1); return (MN v "e")

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
    repVar v (PV p : ps , res) = (ps, subst p (P Bound v undefined) res)
    repVar v (PAny : ps , res) = (ps, res)

{-
mkOperator :: CaseDef -> [Value] -> Maybe Value
mkOperator (CaseDef ns casetree) args 
    | length args /= length ns = Nothing
    | otherwise = evalArgs (zip ns args) casetree
  where
    evalArgs map (Case n alts) = 
        do v <- lookup n map
           (altmap, tm) <- findAlt (getValArgs v) alts map
           evalArgs altmap tm
    evalArgs map (STerm tm) = 
    evalArgs map (UnmatchedCase _) = Nothing

    getValArgs tm = getValArgs' tm []
    getValArgs' (VApp f a) as = getValArgs' f (a:as)
    getValArgs' f as = (f, as)

-}

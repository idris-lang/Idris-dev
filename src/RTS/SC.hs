{-# LANGUAGE PatternGuards #-}

module RTS.SC where

import Core.TT
import Core.Evaluate
import Core.CaseTree

import Control.Monad.State

type CType = Maybe Const
type Tag = Int
type Arity = Int

data SCDef = SCDef { sc_args :: [(Name, CType)],
                     sc_def :: SCExp }
    deriving Show

data SCExp = SRef Name
           | SApp SCExp [SCExp]
           | SLet Name SCExp SCExp
           | SFCall String CType [(SCExp, CType)] -- foreign call with types
           | SCon Tag [SCExp] -- constructor, assume saturated (forcing does this)
           | SConst Const
           | SError String
           | SCase Name [SAlt]
           | SPrimOp SPrim [SCExp]
    deriving Show

data SPrim = AddI | SubI | MulI | DivI 
           | EqI | LtI | LteI | GtI | GteI 
           | EqC | LtC | LteC | GtC | GteC 
           | AddBI | SubBI | MulBI | DivBI 
           | EqBI | LtBI | LteBI | GtBI | GteBI 
           | AddF | SubF | MulF | DivF 
           | EqF | LtF | LteF | GtF | GteF 
           | ConcatS | EqS | LtS
           | StoI | ItoS
           | CtoI | ItoC
           | ItoBI | BItoI
           | StoBI | BItoS
           | StoF  | FtoS
           | ItoF  | FtoI
           | ExpF | LogF | SinF | CosF | TanF 
           | ASinF | ACosF | ATanF | SqrtF | FloorF | CeilF
           | HeadS | TailS | ConsS | IndexS | RevS
           | BelieveMe
    deriving Show

data SAlt = SConCase Tag [Name] SCExp
          | SConstCase Const SCExp
          | SDefaultCase SCExp
    deriving Show

sInt, sFloat, sChar, sString, sPtr, sBigInt :: CType
sInt = Just IType
sFloat = Just FlType
sChar = Just ChType
sString = Just StrType
sPtr = Just PtrType
sBigInt = Just BIType

type SCState = ([(Name, SCDef)], Name)

sclift :: (Name, Def) -> [(Name, SCDef)]
sclift (n, d) = fst (execState (sc [] d) ([], n))

add x = do (xs, b) <- get
           put (x : xs, b)

nextSC :: State SCState Name
nextSC = do (xs, n) <- get
            let n' = getNext n
            put (xs, n')
            return n'
    where getNext (UN n) = MN 0 n
          getNext (MN i n) = MN (i+1) n
          getNext (NS n ns) = NS (getNext n) ns

sname :: State SCState Name
sname = do (xs, n) <- get
           return n

class Lift s t | s -> t where
    sc :: [Name] -> s -> State SCState t

instance Lift Def () where
    sc env (Function ty tm) = do n <- sname
                                 tm' <- sc env tm
                                 add (n, SCDef (zip env (repeat Nothing)) tm')
    sc env (TyDecl _ _) = do n <- sname
                             add (n, SCDef (zip env (repeat Nothing)) 
                                           (SError $ "undefined " ++ show n))
    sc env (Operator _ _ _) = return ()
    sc env (CaseOp _ _ _ _ _ args cases) 
        = do n <- sname
             cases' <- sc (env ++ args) cases
             add (n, SCDef (zip (env ++ args) (repeat Nothing)) cases')

instance Lift (TT Name) SCExp where
    sc env (P _ n _)    = return $ SRef n
    sc env (V i)        = return $ SRef (env!!i)
    sc env fn@(App _ _)
        = do let (f, args) = unApply fn
             prim <- sPrim env f args
             case prim of
                Just t -> return t
                Nothing -> do args' <- mapM (sc env) args
                              case f of
                                (P (DCon t a) _ _) -> return $ SCon t args'
                                (P (TCon t a) _ _) -> return $ SCon t args'
                                _ -> do f' <- sc env f
                                        return $ SApp f' args'
    sc env (Constant c) = return $ SConst c
    sc env (Bind n (Let _ v) e) = do v' <- sc env v
                                     e' <- sc (n : env) e
                                     return (SLet n v' e')
    sc env (Bind n (Lam _) e) = scLam [n] e
      where
        scLam args (Bind n (Lam _) e) = scLam (n : args) e
        scLam args x = do x' <- sc (args ++ env) x
                          fn <- nextSC
                          add (fn, SCDef (zip (env ++ reverse args) (repeat Nothing)) x')
                          return $ SApp (SRef fn) (map SRef env)
    sc _ _ = return $ SConst (I 42424242)
    

instance Lift SC SCExp where
    sc env (Case n alts) = do alts' <- mapM (sc env) alts
                              return (SCase n alts')
    sc env (STerm t)     = do t' <- sc env t
                              return t'
    sc env (UnmatchedCase s) = return (SError s)

instance Lift CaseAlt SAlt where
    sc env (ConCase n t args e) = do e' <- sc env e
                                     return (SConCase t args e')
    sc env (ConstCase c e)      = do e' <- sc env e
                                     return (SConstCase c e')
    sc env (DefaultCase e)      = do e' <- sc env e
                                     return (SDefaultCase e')

-- Deal with primitives: mkForeign, -- lazy, prim__IO, io_bind, malloc, trace_malloc

sPrim :: [Name] -> TT Name -> [TT Name] -> State SCState (Maybe SCExp)
sPrim env (P _ (UN "mkForeign") _) args = do x <- doForeign env args
                                             return (Just x)
sPrim env f args = return Nothing

doForeign env (_ : fgn : args)
   | (_, (Constant (Str fgnName) : fgnArgTys : ret : [])) <- unApply fgn
        = let tys = getFTypes fgnArgTys
              rty = mkEty' ret in
              do args' <- mapM (sc env) args
                 -- wrap it in a prim__IO
                 -- return $ con_ 0 @@ impossible @@ 
                 return $ SFCall fgnName rty (zip args' tys)
   | otherwise = fail "Badly formed foreign function call"

getFTypes :: TT Name -> [CType]
getFTypes tm = case unApply tm of
                 (nil, []) -> []
                 (cons, [ty, xs]) -> 
                    let rest = getFTypes xs in
                        mkEty' ty : rest

mkEty' (P _ (UN ty) _) = mkEty ty
mkEty' _ = Nothing 

mkEty "FInt"    = Just IType
mkEty "FFloat"  = Just FlType
mkEty "FChar"   = Just ChType
mkEty "FString" = Just StrType
mkEty "FPtr"    = Just PtrType
mkEty "FUnit"   = Just VoidType


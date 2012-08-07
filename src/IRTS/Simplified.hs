module IRTS.Simplified where

import IRTS.Lang
import Core.TT
import Data.Maybe
import Control.Monad.State

-- Simplified expressions, where functions/constructors can only be applied 
-- to variables

data SExp = SV LVar
          | SApp Bool Name [LVar]
          | SLet Name SExp SExp
          | SCon Int Name [LVar]
          | SCase LVar [SAlt]
          | SConst Const
          | SOp PrimFn [LVar]
  deriving Show

data SAlt = SConCase Int Name [Name] SExp
          | SConstCase Const SExp
          | SDefaultCase SExp
  deriving Show

data SDecl = SFun Name [Name] SExp
  deriving Show

hvar :: State Int Int
hvar = do h <- get
          put (h + 1)
          return h

simplify :: LExp -> State Int SExp
simplify (LV (Loc i)) = return (SV (Loc i))
simplify (LV x) = return (SV x)
simplify (LApp tc n args) = do args' <- mapM sVar args
                               mkapp (SApp tc n) args'
simplify (LLet n v e) = do v' <- simplify v
                           e' <- simplify e
                           return (SLet n v' e')
simplify (LCon i n args) = do args' <- mapM sVar args
                              mkapp (SCon i n) args'
simplify (LCase e alts) = do v <- sVar e
                             alts' <- mapM sAlt alts
                             case v of 
                                  (x, Nothing) -> return (SCase x alts')
                                  (Glob x, Just e) -> 
                                      return (SLet x e (SCase (Glob x) alts'))
simplify (LConst c) = return (SConst c)
simplify (LOp p args) = do args' <- mapM sVar args
                           mkapp (SOp p) args'

sVar (LV x) = return (x, Nothing)
sVar e = do e' <- simplify e
            i <- hvar
            return (Glob (MN i "R"), Just e')

mkapp f args = mkapp' f args [] where
   mkapp' f [] args = return $ f (reverse args)
   mkapp' f ((x, Nothing) : xs) args = mkapp' f xs (x : args)
   mkapp' f ((Glob x, Just e) : xs) args 
       = do sc <- mkapp' f xs (Glob x : args)
            return (SLet x e sc)

sAlt (LConCase i n args e) = do e' <- simplify e
                                return (SConCase i n args e')
sAlt (LConstCase c e) = do e' <- simplify e
                           return (SConstCase c e')
sAlt (LDefaultCase e) = do e' <- simplify e
                           return (SDefaultCase e')

checkDefs :: LDefs -> [(Name, LDecl)] -> TC [(Name, SDecl)]
checkDefs ctxt [] = return []
checkDefs ctxt (con@(n, LConstructor _ _ _) : xs) 
    = do xs' <- checkDefs ctxt xs
         return xs'
checkDefs ctxt ((n, LFun n' args exp) : xs) 
    = do let sexp = evalState (simplify exp) 0
         exp' <- scopecheck ctxt (zip args [0..]) sexp
         xs' <- checkDefs ctxt xs
         return ((n, SFun n' args exp') : xs')

scopecheck :: LDefs -> [(Name, Int)] -> SExp -> TC SExp 
scopecheck ctxt env tm = sc env tm where
    sc env (SV (Glob n)) 
       = case lookup n (reverse env) of -- most recent first
              Just i -> return (SV (Loc i))
              Nothing -> case lookupCtxt Nothing n ctxt of
                              [LConstructor _ i ar] ->
                                  if ar == 0 then return (SCon i n [])
                                     else fail $ "Codegen error: Constructor " ++ show n ++
                                                 " has arity " ++ show ar
                              [_] -> return (SV (Glob n))
                              [] -> fail $ "Codegen error: No such variable " ++ show n
    sc env (SApp tc f args)
       = do case lookupCtxt Nothing f ctxt of
                [LConstructor n tag ar] ->
                    if (ar == length args)
                       then return $ SCon tag n args
                       else fail $ "Codegen error: Constructor " ++ show f ++ 
                                   " has arity " ++ show ar
                [_] -> return $ SApp tc f args
                [] -> fail $ "Codegen error: No such variable " ++ show f
    sc env (SCase e alts)
       = do alts' <- mapM (scalt env) alts
            return (SCase e alts')
    sc env (SLet n v e)
       = do v' <- sc env v
            e' <- sc (env ++ [(n, length env)]) e
            return (SLet n v' e')
    sc env (SOp prim args)
       = do return (SOp prim args)
    sc env x = return x

    scalt env (SConCase i n args e)
       = do let env' = env ++ zip args [length env..]
            tag <- case lookupCtxt Nothing n ctxt of
                        [LConstructor _ i ar] -> 
                             if (length args == ar) then return i
                                else fail $ "Codegen error: Constructor " ++ show n ++
                                            " has arity " ++ show ar
                        _ -> fail $ "Codegen error: No constructor " ++ show n
            e' <- sc env' e
            return (SConCase tag n args e')
    scalt env (SConstCase c e) = do e' <- sc env e
                                    return (SConstCase c e')
    scalt env (SDefaultCase e) = do e' <- sc env e
                                    return (SDefaultCase e')


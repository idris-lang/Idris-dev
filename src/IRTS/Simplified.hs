module IRTS.Simplified where

import IRTS.Lang
import Core.TT
import Data.Maybe
import Control.Monad.State

-- Simplified expressions, where functions/constructors can only be applied 
-- to variables

data SExp = SV LVar
          | SApp Bool Name [LVar]
          | SLet LVar SExp SExp
          | SCon Int Name [LVar]
          | SCase LVar [SAlt]
          | SConst Const
          | SForeign FLang FType String [(FType, LVar)]
          | SOp PrimFn [LVar]
          | SError String
  deriving Show

data SAlt = SConCase Int Int Name [Name] SExp
          | SConstCase Const SExp
          | SDefaultCase SExp
  deriving Show

data SDecl = SFun Name [Name] Int SExp
  deriving Show

hvar :: State (LDefs, Int) Int
hvar = do (l, h) <- get
          put (l, h + 1)
          return h

ldefs :: State (LDefs, Int) LDefs
ldefs = do (l, h) <- get
           return l

simplify :: Bool -> LExp -> State (LDefs, Int) SExp
simplify tl (LV (Loc i)) = return (SV (Loc i))
simplify tl (LV (Glob x)) 
    = do ctxt <- ldefs
         case lookupCtxt Nothing x ctxt of
              [LConstructor _ t 0] -> return $ SCon t x []
              _ -> return $ SV (Glob x)
simplify tl (LApp tc (LV (Glob n)) args) 
                             = do args' <- mapM sVar args
                                  mkapp (SApp (tl || tc) n) args'
simplify tl (LForeign lang ty fn args) 
                            = do args' <- mapM sVar (map snd args)
                                 let fargs = zip (map fst args) args'
                                 mkfapp (SForeign lang ty fn) fargs
simplify tl (LLet n v e) = do v' <- simplify False v
                              e' <- simplify tl e
                              return (SLet (Glob n) v' e')
simplify tl (LCon i n args) = do args' <- mapM sVar args
                                 mkapp (SCon i n) args'
simplify tl (LCase e alts) = do v <- sVar e
                                alts' <- mapM (sAlt tl) alts
                                case v of 
                                    (x, Nothing) -> return (SCase x alts')
                                    (Glob x, Just e) -> 
                                        return (SLet (Glob x) e (SCase (Glob x) alts'))
simplify tl (LConst c) = return (SConst c)
simplify tl (LOp p args) = do args' <- mapM sVar args
                              mkapp (SOp p) args'
simplify tl (LError str) = return $ SError str

sVar (LV (Glob x))
    = do ctxt <- ldefs
         case lookupCtxt Nothing x ctxt of
              [LConstructor _ t 0] -> sVar (LCon t x [])
              _ -> return (Glob x, Nothing)
sVar (LV x) = return (x, Nothing)
sVar e = do e' <- simplify False e
            i <- hvar
            return (Glob (MN i "R"), Just e')

mkapp f args = mkapp' f args [] where
   mkapp' f [] args = return $ f (reverse args)
   mkapp' f ((x, Nothing) : xs) args = mkapp' f xs (x : args)
   mkapp' f ((x, Just e) : xs) args 
       = do sc <- mkapp' f xs (x : args)
            return (SLet x e sc)

mkfapp f args = mkapp' f args [] where
   mkapp' f [] args = return $ f (reverse args)
   mkapp' f ((ty, (x, Nothing)) : xs) args = mkapp' f xs ((ty, x) : args)
   mkapp' f ((ty, (x, Just e)) : xs) args 
       = do sc <- mkapp' f xs ((ty, x) : args)
            return (SLet x e sc)

sAlt tl (LConCase i n args e) = do e' <- simplify tl e
                                   return (SConCase (-1) i n args e')
sAlt tl (LConstCase c e) = do e' <- simplify tl e
                              return (SConstCase c e')
sAlt tl (LDefaultCase e) = do e' <- simplify tl e
                              return (SDefaultCase e')

checkDefs :: LDefs -> [(Name, LDecl)] -> TC [(Name, SDecl)]
checkDefs ctxt [] = return []
checkDefs ctxt (con@(n, LConstructor _ _ _) : xs) 
    = do xs' <- checkDefs ctxt xs
         return xs'
checkDefs ctxt ((n, LFun n' args exp) : xs) 
    = do let sexp = evalState (simplify True exp) (ctxt, 0)
         (exp', locs) <- runStateT (scopecheck ctxt (zip args [0..]) sexp) (length args)
         xs' <- checkDefs ctxt xs
         return ((n, SFun n' args ((locs + 1) - length args) exp') : xs')

lvar v = do i <- get
            put (max i v)

scopecheck :: LDefs -> [(Name, Int)] -> SExp -> StateT Int TC SExp 
scopecheck ctxt env tm = sc env tm where
    sc env (SV (Glob n)) =
       case lookup n (reverse env) of -- most recent first
              Just i -> do lvar i; return (SV (Loc i))
              Nothing -> case lookupCtxt Nothing n ctxt of
                              [LConstructor _ i ar] ->
                                  if True -- ar == 0 
                                     then return (SCon i n [])
                                     else fail $ "Codegen error: Constructor " ++ show n ++
                                                 " has arity " ++ show ar
                              [_] -> return (SV (Glob n))
                              [] -> fail $ "Codegen error: No such variable " ++ show n
    sc env (SApp tc f args)
       = do args' <- mapM (scVar env) args
            case lookupCtxt Nothing f ctxt of
                [LConstructor n tag ar] ->
                    if True -- (ar == length args)
                       then return $ SCon tag n args'
                       else fail $ "Codegen error: Constructor " ++ show f ++ 
                                   " has arity " ++ show ar
                [_] -> return $ SApp tc f args'
                [] -> fail $ "Codegen error: No such variable " ++ show f
    sc env (SForeign l ty f args)
       = do args' <- mapM (\ (t, a) -> do a' <- scVar env a
                                          return (t, a')) args
            return $ SForeign l ty f args'
    sc env (SCon tag f args)
       = do args' <- mapM (scVar env) args
            case lookupCtxt Nothing f ctxt of
                [LConstructor n tag ar] ->
                    if True -- (ar == length args)
                       then return $ SCon tag n args'
                       else fail $ "Codegen error: Constructor " ++ show f ++ 
                                   " has arity " ++ show ar
                _ -> fail $ "Codegen error: No such constructor " ++ show f
    sc env (SCase e alts)
       = do e' <- scVar env e
            alts' <- mapM (scalt env) alts
            return (SCase e' alts')
    sc env (SLet (Glob n) v e)
       = do let env' = env ++ [(n, length env)]
            v' <- sc env v
            n' <- scVar env' (Glob n)
            e' <- sc env' e
            return (SLet n' v' e')
    sc env (SOp prim args)
       = do args' <- mapM (scVar env) args
            return (SOp prim args')
    sc env x = return x

    scVar env (Glob n) =
       case lookup n (reverse env) of -- most recent first
              Just i -> do lvar i; return (Loc i)
              Nothing -> case lookupCtxt Nothing n ctxt of
                              [LConstructor _ i ar] ->
                                  fail $ "Codegen error : can't pass constructor here"
                              [_] -> return (Glob n)
                              [] -> fail $ "Codegen error: No such variable " ++ show n
    scVar _ x = return x

    scalt env (SConCase _ i n args e)
       = do let env' = env ++ zip args [length env..]
            tag <- case lookupCtxt Nothing n ctxt of
                        [LConstructor _ i ar] -> 
                             if True -- (length args == ar) 
                                then return i
                                else fail $ "Codegen error: Constructor " ++ show n ++
                                            " has arity " ++ show ar
                        _ -> fail $ "Codegen error: No constructor " ++ show n
            e' <- sc env' e
            return (SConCase (length env) tag n args e')
    scalt env (SConstCase c e) = do e' <- sc env e
                                    return (SConstCase c e')
    scalt env (SDefaultCase e) = do e' <- sc env e
                                    return (SDefaultCase e')


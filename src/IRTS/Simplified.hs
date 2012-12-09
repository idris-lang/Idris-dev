module IRTS.Simplified where

import IRTS.Defunctionalise
import Core.TT
import Data.Maybe
import Control.Monad.State

import Debug.Trace

-- Simplified expressions, where functions/constructors can only be applied 
-- to variables

data SExp = SV LVar
          | SApp Bool Name [LVar]
          | SLet LVar SExp SExp
          | SUpdate LVar SExp
          | SCon Int Name [LVar]
          | SCase LVar [SAlt]
          | SChkCase LVar [SAlt]
          | SProj LVar Int
          | SConst Const
          | SForeign FLang FType String [(FType, LVar)]
          | SOp PrimFn [LVar]
          | SNothing -- erased value, will never be inspected
          | SError String
  deriving Show

data SAlt = SConCase Int Int Name [Name] SExp
          | SConstCase Const SExp
          | SDefaultCase SExp
  deriving Show

data SDecl = SFun Name [Name] Int SExp
  deriving Show

hvar :: State (DDefs, Int) Int
hvar = do (l, h) <- get
          put (l, h + 1)
          return h

ldefs :: State (DDefs, Int) DDefs
ldefs = do (l, h) <- get
           return l

simplify :: Bool -> DExp -> State (DDefs, Int) SExp
simplify tl (DV (Loc i)) = return (SV (Loc i))
simplify tl (DV (Glob x)) 
    = do ctxt <- ldefs
         case lookupCtxt Nothing x ctxt of
              [DConstructor _ t 0] -> return $ SCon t x []
              _ -> return $ SV (Glob x)
simplify tl (DApp tc n args) = do args' <- mapM sVar args
                                  mkapp (SApp (tl || tc) n) args'
simplify tl (DForeign lang ty fn args) 
                            = do args' <- mapM sVar (map snd args)
                                 let fargs = zip (map fst args) args'
                                 mkfapp (SForeign lang ty fn) fargs
simplify tl (DLet n v e) = do v' <- simplify False v
                              e' <- simplify tl e
                              return (SLet (Glob n) v' e')
simplify tl (DUpdate n e) = do e' <- simplify False e
                               return (SUpdate (Glob n) e')
simplify tl (DC i n args) = do args' <- mapM sVar args
                               mkapp (SCon i n) args'
simplify tl (DProj t i) = do v <- sVar t
                             case v of
                                (x, Nothing) -> return (SProj x i)
                                (Glob x, Just e) ->
                                    return (SLet (Glob x) e (SProj (Glob x) i))
simplify tl (DCase e alts) = do v <- sVar e
                                alts' <- mapM (sAlt tl) alts
                                case v of 
                                    (x, Nothing) -> return (SCase x alts')
                                    (Glob x, Just e) -> 
                                        return (SLet (Glob x) e (SCase (Glob x) alts'))
simplify tl (DChkCase e alts) 
                           = do v <- sVar e
                                alts' <- mapM (sAlt tl) alts
                                case v of 
                                    (x, Nothing) -> return (SChkCase x alts')
                                    (Glob x, Just e) -> 
                                        return (SLet (Glob x) e (SChkCase (Glob x) alts'))
simplify tl (DConst c) = return (SConst c)
simplify tl (DOp p args) = do args' <- mapM sVar args
                              mkapp (SOp p) args'
simplify tl DNothing = return SNothing 
simplify tl (DError str) = return $ SError str

sVar (DV (Glob x))
    = do ctxt <- ldefs
         case lookupCtxt Nothing x ctxt of
              [DConstructor _ t 0] -> sVar (DC t x [])
              _ -> return (Glob x, Nothing)
sVar (DV x) = return (x, Nothing)
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

sAlt tl (DConCase i n args e) = do e' <- simplify tl e
                                   return (SConCase (-1) i n args e')
sAlt tl (DConstCase c e) = do e' <- simplify tl e
                              return (SConstCase c e')
sAlt tl (DDefaultCase e) = do e' <- simplify tl e
                              return (SDefaultCase e')

checkDefs :: DDefs -> [(Name, DDecl)] -> TC [(Name, SDecl)]
checkDefs ctxt [] = return []
checkDefs ctxt (con@(n, DConstructor _ _ _) : xs) 
    = do xs' <- checkDefs ctxt xs
         return xs'
checkDefs ctxt ((n, DFun n' args exp) : xs) 
    = do let sexp = evalState (simplify True exp) (ctxt, 0)
         (exp', locs) <- runStateT (scopecheck ctxt (zip args [0..]) sexp) (length args)
         xs' <- checkDefs ctxt xs
         return ((n, SFun n' args ((locs + 1) - length args) exp') : xs')

lvar v = do i <- get
            put (max i v)

scopecheck :: DDefs -> [(Name, Int)] -> SExp -> StateT Int TC SExp 
scopecheck ctxt envTop tm = sc envTop tm where
    sc env (SV (Glob n)) =
       case lookup n (reverse env) of -- most recent first
              Just i -> do lvar i; return (SV (Loc i))
              Nothing -> case lookupCtxt Nothing n ctxt of
                              [DConstructor _ i ar] ->
                                  if True -- ar == 0 
                                     then return (SCon i n [])
                                     else fail $ "Codegen error: Constructor " ++ show n ++
                                                 " has arity " ++ show ar
                              [_] -> return (SV (Glob n))
                              [] -> fail $ "Codegen error: No such variable " ++ show n
    sc env (SApp tc f args)
       = do args' <- mapM (scVar env) args
            case lookupCtxt Nothing f ctxt of
                [DConstructor n tag ar] ->
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
                [DConstructor n tag ar] ->
                    if True -- (ar == length args)
                       then return $ SCon tag n args'
                       else fail $ "Codegen error: Constructor " ++ show f ++ 
                                   " has arity " ++ show ar
                _ -> fail $ "Codegen error: No such constructor " ++ show f
    sc env (SProj e i)
       = do e' <- scVar env e
            return (SProj e' i)
    sc env (SCase e alts)
       = do e' <- scVar env e
            alts' <- mapM (scalt env) alts
            return (SCase e' alts')
    sc env (SChkCase e alts)
       = do e' <- scVar env e
            alts' <- mapM (scalt env) alts
            return (SChkCase e' alts')
    sc env (SLet (Glob n) v e)
       = do let env' = env ++ [(n, length env)]
            v' <- sc env v
            n' <- scVar env' (Glob n)
            e' <- sc env' e
            return (SLet n' v' e')
    sc env (SUpdate (Glob n) e)
       = do -- n already in env
            e' <- sc env e
            n' <- scVar env (Glob n)
            return (SUpdate n' e')
    sc env (SOp prim args)
       = do args' <- mapM (scVar env) args
            return (SOp prim args')
    sc env x = return x

    scVar env (Glob n) =
       case lookup n (reverse env) of -- most recent first
              Just i -> do lvar i; return (Loc i)
              Nothing -> case lookupCtxt Nothing n ctxt of
                              [DConstructor _ i ar] ->
                                  fail $ "Codegen error : can't pass constructor here"
                              [_] -> return (Glob n)
                              [] -> fail $ "Codegen error: No such variable " ++ show n ++ 
                                           " in " ++ show tm ++ " " ++ show envTop
    scVar _ x = return x

    scalt env (SConCase _ i n args e)
       = do let env' = env ++ zip args [length env..]
            tag <- case lookupCtxt Nothing n ctxt of
                        [DConstructor _ i ar] -> 
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


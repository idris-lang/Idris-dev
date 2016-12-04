{-|
Module      : IRTS.Simplified
Description : Simplified expressions, where functions/constructors can only be applied to variables.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module IRTS.Simplified(simplifyDefs, SDecl(..), SExp(..), SAlt(..)) where

import Idris.Core.CaseTree
import Idris.Core.TT
import Idris.Core.Typecheck
import IRTS.Defunctionalise

import Control.Monad.State
import Data.Maybe
import Debug.Trace

data SExp = SV LVar
          | SApp Bool Name [LVar]
          | SLet LVar SExp SExp
          | SUpdate LVar SExp
          | SCon (Maybe LVar) -- location to reallocate, if available
                 Int Name [LVar]
          | SCase CaseType LVar [SAlt]
          | SChkCase LVar [SAlt]
          | SProj LVar Int
          | SConst Const
          -- Keep DExps for describing foreign things, because they get
          -- translated differently
          | SForeign FDesc FDesc [(FDesc, LVar)]
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
         case lookupCtxtExact x ctxt of
              Just (DConstructor _ t 0) -> return $ SCon Nothing t x []
              _ -> return $ SV (Glob x)
simplify tl (DApp tc n args) = do args' <- mapM sVar args
                                  mkapp (SApp (tl || tc) n) args'
simplify tl (DForeign ty fn args)
                            = do args' <- mapM sVar (map snd args)
                                 let fargs = zip (map fst args) args'
                                 mkfapp (SForeign ty fn) fargs
simplify tl (DLet n v e) = do v' <- simplify False v
                              e' <- simplify tl e
                              return (SLet (Glob n) v' e')
simplify tl (DUpdate n e) = do e' <- simplify False e
                               return (SUpdate (Glob n) e')
simplify tl (DC loc i n args) = do args' <- mapM sVar args
                                   mkapp (SCon loc i n) args'
simplify tl (DProj t i) = do v <- sVar t
                             case v of
                                (x, Nothing) -> return (SProj x i)
                                (Glob x, Just e) ->
                                    return (SLet (Glob x) e (SProj (Glob x) i))
simplify tl (DCase up e alts) = do v <- sVar e
                                   alts' <- mapM (sAlt tl) alts
                                   case v of
                                      (x, Nothing) -> return (SCase up x alts')
                                      (Glob x, Just e) ->
                                          return (SLet (Glob x) e (SCase up (Glob x) alts'))
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
         case lookupCtxtExact x ctxt of
              Just (DConstructor _ t 0) -> sVar (DC Nothing t x [])
              _ -> return (Glob x, Nothing)
sVar (DV x) = return (x, Nothing)
sVar e = do e' <- simplify False e
            i <- hvar
            return (Glob (sMN i "R"), Just e')

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

simplifyDefs :: DDefs -> [(Name, DDecl)] -> TC [(Name, SDecl)]
simplifyDefs ctxt [] = return []
simplifyDefs ctxt (con@(n, DConstructor _ _ _) : xs)
    = do xs' <- simplifyDefs ctxt xs
         return xs'
simplifyDefs ctxt ((n, DFun n' args exp) : xs)
    = do let sexp = evalState (simplify True exp) (ctxt, 0)
         (exp', locs) <- runStateT (scopecheck n ctxt (zip args [0..]) sexp) (length args)
         xs' <- simplifyDefs ctxt xs
         return ((n, SFun n' args ((locs + 1) - length args) exp') : xs')

lvar v = do i <- get
            put (max i v)

scopecheck :: Name -> DDefs -> [(Name, Int)] -> SExp -> StateT Int TC SExp
scopecheck fn ctxt envTop tm = sc envTop tm where
    failsc err = fail $ "Codegen error in " ++ show fn ++ ":" ++ err

    sc env (SV (Glob n)) =
       case lookup n (reverse env) of -- most recent first
              Just i -> do lvar i; return (SV (Loc i))
              Nothing -> case lookupCtxtExact n ctxt of
                              Just (DConstructor _ i ar) ->
                                  if True -- ar == 0
                                     then return (SCon Nothing i n [])
                                     else failsc $ "Constructor " ++ show n ++
                                                 " has arity " ++ show ar
                              Just _ -> return (SV (Glob n))
                              Nothing -> failsc $ "No such variable " ++ show n
    sc env (SApp tc f args)
       = do args' <- mapM (scVar env) args
            case lookupCtxtExact f ctxt of
                Just (DConstructor n tag ar) ->
                    if True -- (ar == length args)
                       then return $ SCon Nothing tag n args'
                       else failsc $ "Constructor " ++ show f ++
                                   " has arity " ++ show ar
                Just _ -> return $ SApp tc f args'
                Nothing -> failsc $ "No such variable " ++ show f
    sc env (SForeign ty f args)
       = do args' <- mapM (\ (t, a) -> do a' <- scVar env a
                                          return (t, a')) args
            return $ SForeign ty f args'
    sc env (SCon loc tag f args)
       = do loc' <- case loc of
                         Nothing -> return Nothing
                         Just l -> do l' <- scVar env l
                                      return (Just l')
            args' <- mapM (scVar env) args
            case lookupCtxtExact f ctxt of
                Just (DConstructor n tag ar) ->
                    if True -- (ar == length args)
                       then return $ SCon loc' tag n args'
                       else failsc $ "Constructor " ++ show f ++
                                     " has arity " ++ show ar
                _ -> failsc $ "No such constructor " ++ show f
    sc env (SProj e i)
       = do e' <- scVar env e
            return (SProj e' i)
    sc env (SCase up e alts)
       = do e' <- scVar env e
            alts' <- mapM (scalt env) alts
            return (SCase up e' alts')
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
              Nothing -> case lookupCtxtExact n ctxt of
                              Just (DConstructor _ i ar) ->
                                  failsc "can't pass constructor here"
                              Just _ -> return (Glob n)
                              Nothing -> failsc $ "No such variable " ++ show n ++
                                               " in " ++ show tm ++ " " ++ show envTop
    scVar _ x = return x

    scalt env (SConCase _ i n args e)
       = do let env' = env ++ zip args [length env..]
            tag <- case lookupCtxtExact n ctxt of
                        Just (DConstructor _ i ar) ->
                             if True -- (length args == ar)
                                then return i
                                else failsc $ "Constructor " ++ show n ++
                                            " has arity " ++ show ar
                        _ -> failsc $ "No constructor " ++ show n
            e' <- sc env' e
            return (SConCase (length env) tag n args e')
    scalt env (SConstCase c e) = do e' <- sc env e
                                    return (SConstCase c e')
    scalt env (SDefaultCase e) = do e' <- sc env e
                                    return (SDefaultCase e')

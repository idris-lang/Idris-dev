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


ldefs :: State (DDefs, Int) DDefs
ldefs = do (l, h) <- get
           return l

-- | Simplify an expression by let-binding argument expressions that
-- are not variables
-- The boolean parameter indicates whether the expression is at tail
-- call position.
simplify :: Bool -> DExp -> State (DDefs, Int) SExp
simplify tl (DV (Loc i)) = return (SV (Loc i))
simplify tl (DV (Glob x))
    = do ctxt <- ldefs
         case lookupCtxtExact x ctxt of
              Just (DConstructor _ t 0) -> return $ SCon Nothing t x []
              _ -> return $ SV (Glob x)
simplify tl (DApp tc n args) = bindExprs args (SApp (tl || tc) n)
simplify tl (DForeign ty fn args)
    = let (fdescs, exprs) = unzip args
      in bindExprs exprs (\vars -> SForeign ty fn (zip fdescs vars))
simplify tl (DLet n v e) = do v' <- simplify False v
                              e' <- simplify tl e
                              return (SLet (Glob n) v' e')
simplify tl (DUpdate n e) = do e' <- simplify False e
                               return (SUpdate (Glob n) e')
simplify tl (DC loc i n args) = bindExprs args (SCon loc i n)
simplify tl (DProj t i) = bindExpr t (\var -> SProj var i)
simplify tl (DCase up e alts)
    = do alts' <- mapM (sAlt tl) alts
         bindExpr e (\var -> SCase up var alts')
simplify tl (DChkCase e alts)
    = do alts' <- mapM (sAlt tl) alts
         bindExpr e (\var -> SChkCase var alts')
simplify tl (DConst c) = return (SConst c)
simplify tl (DOp p args) = bindExprs args (SOp p)
simplify tl DNothing = return SNothing
simplify tl (DError str) = return $ SError str


-- | Let-bind a list of expressions to variables and construct the
-- inner expression with the bound variables.
-- If an expression in the list is already a variable we don’t bind it
-- again.
bindExprs :: [DExp] -> ([LVar] -> SExp) -> State (DDefs, Int) SExp
bindExprs es f = bindExprs' es f [] where
    bindExprs' [] f vars = return $ f (reverse vars)
    bindExprs' (e:es) f vars =
        bindExprM e (\var -> bindExprs' es f (var:vars))

-- | Special case of 'bindExprs' for just one expression
bindExpr :: DExp -> (LVar -> SExp) -> State (DDefs, Int) SExp
bindExpr e f = bindExprM e (return . f)

bindExprM :: DExp -> (LVar -> State (DDefs, Int) SExp) -> State (DDefs, Int) SExp
bindExprM (DV (Glob x)) f
    = do ctxt <- ldefs
         case lookupCtxtExact x ctxt of
              Just (DConstructor _ t 0) -> bindExprM (DC Nothing t x []) f
              _ -> f (Glob x)
bindExprM (DV var) f = f var
bindExprM e f =
    do e' <- simplify False e
       var <- freshVar
       f' <- f var
       return $ SLet var e' f'
    where
        freshVar = do (defs, i) <- get
                      put (defs, i + 1)
                      return (Glob (sMN i "R"))


sAlt :: Bool -> DAlt -> State (DDefs, Int) SAlt
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

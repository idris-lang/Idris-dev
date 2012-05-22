module RTS.Bytecode where

import Core.TT
import Core.CaseTree
import Core.Evaluate

import Idris.AbsSyntax
import RTS.SC

import Control.Monad.State

type Local = Int

data BAtom = BP Name | BL Local | BC Const
    deriving Show

-- Like SC, but with explicit evaluation, de Bruijn levels for locals, and all
-- intermediate values put into variables (which can be stored on the stack or
-- in registers when generating code)

data Bytecode = BAtom BAtom
              | BApp BAtom [BAtom]
              | BLazy BAtom [BAtom]
              | BLet Local Bytecode Bytecode
              | BEval Local Bytecode
              | BFCall String CType [(BAtom, CType)]
              | BCon Tag [BAtom]
              | BCase Local [BAlt]
              | BPrimOp SPrim [BAtom]
              | BError String
              | GetArgs [Name] Bytecode -- get function arguments
              | Reserve Int Bytecode -- reserve stack space, clear on exit
    deriving Show

data BAlt = BConCase Tag [Name] Bytecode
          | BConstCase Const Bytecode
          | BDefaultCase Bytecode
    deriving Show

bcdefs :: [(Name, SCDef)] -> [(Name, Bytecode)]
bcdefs = map (\ (n, s) -> (n, bc s))

bc (SCDef args max c) = GetArgs (map fst args) (bcExp max (length args) c)

bcExp v arity x 
   = let (code, max) = runState (bc' x) v
         space = max - arity in
         if (space > 0) then Reserve space code else code
  where
    ref i = do s <- get
               when (i > s) $ put i 
    next = do s <- get
              put (s + 1)
              return s

    bc' :: SCExp -> State Int Bytecode
    bc' (SRef n) = return $ BAtom (BP n)
    bc' (SLoc i) = do ref i; return $ BAtom (BL i)
    bc' (SApp f args) = do f' <- bc' f
                           args' <- mapM bc' args
                           case f' of
                              BAtom r -> mkApp (\x -> BApp r x) args' []
                              bc -> do v <- next
                                       mkApp (\x -> BLet v bc (BApp (BL v) x)) args' []
    bc' (SLazyApp f args) = do args' <- mapM bc' args
                               mkApp (\x -> BApp (BP f) x) args' []
    bc' (SCon t args) = do args' <- mapM bc' args
                           mkApp (\x -> BCon t x) args' []
    bc' (SFCall c t args) = do args' <- mapM bc' (map fst args)
                               mkFApp c t (zip args' (map snd args)) []
    bc' (SConst c) = return $ BAtom (BC c)
    bc' (SError s) = return $ BError s
    bc' (SCase e alts) = do e' <- bc' e
                            alts' <- mapM bcAlt alts
                            case e' of
                               BAtom (BL i) -> return $ BCase i alts'
                               bc -> do v <- next
                                        return $ BLet v bc (BCase v alts')
    bc' (SPrimOp p args) = do args' <- mapM bc' args
                              mkApp (\x -> BPrimOp p x) args' []

    mkApp ap [] locs = return $ ap locs
    mkApp ap (BAtom (BL i) : as) locs = mkApp ap as (locs ++ [BL i]) 
    mkApp ap (a : as) locs = do v <- next
                                app <- mkApp ap as (locs ++ [BL v])
                                return $ BLet v a app

    bcAlt (SConCase t args e) = do e' <- bc' e
                                   return $ BConCase t args e' 
    bcAlt (SConstCase i e) = do e' <- bc' e
                                return $ BConstCase i e' 
    bcAlt (SDefaultCase e) = do e' <- bc' e
                                return $ BDefaultCase e' 

    mkFApp c ty [] locs = return $ BFCall c ty locs
    mkFApp c ty ((BAtom (BL i), t) : as) locs = mkFApp c ty as (locs ++ [(BL i, t)]) 
    mkFApp c ty ((a, t) : as) locs = do v <- next
                                        app <- mkFApp c ty as (locs ++ [(BL v, t)])
                                        return $ BLet v a app


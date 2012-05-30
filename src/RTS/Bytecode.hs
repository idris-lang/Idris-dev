module RTS.Bytecode where

import Core.TT
import Core.CaseTree
import Core.Evaluate

import Idris.AbsSyntax
import RTS.SC

import Control.Monad.State

type Local = Int

data BAtom = BP Name Int | BL Local | BC Const
    deriving Show

-- Like SC, but with explicit evaluation, de Bruijn levels for locals, and all
-- intermediate values put into variables (which can be stored on the stack or
-- in registers when generating code)

data Bytecode = BAtom BAtom
              | BApp BAtom [BAtom]
              | BTailApp BAtom [BAtom]
              | BLazy BAtom [BAtom]
              | BLet Local Bytecode Bytecode
              | BFCall String CType [(BAtom, CType)]
              | BCon Tag [BAtom]
              | BCase Local [BAlt]
              | BPrimOp SPrim [BAtom]
              | BError String
              | BGetArgs [Name] Bytecode -- get function arguments
              | BReserve Int Bytecode -- reserve stack space, clear on exit
    deriving Show

data BAlt = BConCase Tag [Name] Int Bytecode
          | BConstCase Const Bytecode
          | BDefaultCase Bytecode
    deriving Show

bcdefs :: [(Name, SCDef)] -> [(Name, (Int, Bytecode))]
bcdefs xs = map (\ (n, s) -> (n, bc xs s)) xs

bc all (SCDef args max c) = (length args,
                            BGetArgs (map fst args) (bcExp all max (length args) c))

bcExp all v arity x 
   = let (code, max) = runState (bc' True arity x) v
         space = max - arity in
         if (space > 0) then BReserve space code else code
  where
    ref i = do s <- get
               when (i > s) $ put i 
    next = do s <- get
              put (s + 1)
              return s
    scarity n = case lookup n all of
                     Just (SCDef args _ _) -> length args
                     
    bc' :: Bool -> Int -> SCExp -> State Int Bytecode
    bc' tl d (SRef n) = if tl then return $ BTailApp (BP n (scarity n)) []
                              else return $ BApp (BP n (scarity n)) []
    bc' tl d (SLoc i) = do ref i; return $ BAtom (BL i)
    bc' tl d (SApp f args) 
       = do f' <- case f of
                       SRef n -> return $ BAtom (BP n (scarity n))
                       _ -> bc' False d f
            args' <- mapM (bc' False d) args
            let bapp = if tl then BTailApp else BApp
            case f' of
                BAtom r -> mkApp (\x -> bapp r x) args' []
                bc -> do v <- next
                         mkApp (\x -> BLet v bc (bapp (BL v) x)) args' []
    bc' tl d (SLazyApp f args) = do args' <- mapM (bc' False d) args
                                    -- let bapp = if tl then BTailApp else BApp
                                    mkApp (\x -> BLazy (BP f (scarity f)) x) args' []
    bc' tl d (SLet n val sc) = do v' <- bc' False d val
                                  sc' <- bc' False (d + 1) sc
                                  return $ BLet d v' sc'
    bc' tl d (SCon t args) = do args' <- mapM (bc' False d) args
                                mkApp (\x -> BCon t x) args' []
    bc' tl d (SFCall c t args) = do args' <- mapM (bc' False d) (map fst args)
                                    mkFApp c t (zip args' (map snd args)) []
    bc' tl d (SConst c) = return $ BAtom (BC c)
    bc' tl d (SError s) = return $ BError s
    bc' tl d (SCase e alts) = do e' <- bc' False d e
                                 alts' <- mapM (bcAlt tl d) alts
                                 case e' of
                                    BAtom (BL i) -> return $ BCase i alts'
                                    bc -> do v <- next
                                             return $ BLet v bc (BCase v alts')
    bc' tl d (SPrimOp p args) = do args' <- mapM (bc' tl d) args
                                   mkApp (\x -> BPrimOp p x) args' []

    mkApp ap [] locs = return $ ap locs
    mkApp ap (BAtom (BL i) : as) locs = mkApp ap as (locs ++ [BL i]) 
    mkApp ap (a : as) locs = do v <- next
                                app <- mkApp ap as (locs ++ [BL v])
                                return $ BLet v a app

    bcAlt tl d (SConCase t args e) = do e' <- bc' tl (d + length args) e
                                        return $ BConCase t args d e' 
    bcAlt tl d (SConstCase i e) = do e' <- bc' tl d e
                                     return $ BConstCase i e' 
    bcAlt tl d (SDefaultCase e) = do e' <- bc' tl d e 
                                     return $ BDefaultCase e' 

    mkFApp c ty [] locs = return $ BFCall c ty locs
    mkFApp c ty ((BAtom (BL i), t) : as) locs 
       = mkFApp c ty as (locs ++ [(BL i, t)]) 
    mkFApp c ty ((a, t) : as) locs 
       = do v <- next
            app <- mkFApp c ty as (locs ++ [(BL v, t)])
            return $ BLet v a app


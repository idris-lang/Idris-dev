module IRTS.Lang where

import Core.TT
import Control.Monad.State hiding(lift)

data LVar = Loc Int | Glob Name
  deriving Show

data LExp = LV LVar
          | LApp Bool Name [LExp] -- True = tail call
          | LLazyApp Name [LExp] -- True = tail call
          | LLazyExp LExp
          | LLet Name LExp LExp -- name just for pretty printing
          | LLam [Name] LExp -- lambda, lifted out before compiling
          | LCon Int Name [LExp]
          | LCase LExp [LAlt]
          | LConst Const
          | LForeign FLang FType String [(FType, LExp)]
          | LOp PrimFn [LExp]
  deriving Show

data PrimFn = LPlus | LMinus | LTimes | LDiv | LEq | LLt | LLe | LGt | LGe
            | LFPlus | LFMinus | LFTimes | LFDiv | LFEq | LFLt | LFLe | LFGt | LFGe
            | LStrConcat | LStrLt | LStrEq | LStrLen
            | LIntFloat | LFloatInt | LIntStr | LStrInt | LFloatStr | LStrFloat
            | LPrintNum | LPrintStr | LReadStr
  deriving Show

-- Supported target languages for foreign calls

data FLang = LANG_C
  deriving Show

data FType = FInt | FString | FUnit | FPtr | FDouble | FAny
  deriving Show

data LAlt = LConCase Int Name [Name] LExp
          | LConstCase Const LExp
          | LDefaultCase LExp
  deriving Show

data LDecl = LFun Name [Name] LExp -- name, arg names, definition
           | LConstructor Name Int Int -- constructor name, tag, arity
  deriving Show

type LDefs = Ctxt LDecl

addTags :: Int -> [(Name, LDecl)] -> (Int, [(Name, LDecl)])
addTags i ds = tag i ds []
  where tag i ((n, LConstructor n' t a) : as) acc
            = tag (i + 1) as ((n, LConstructor n' i a) : acc) 
        tag i (x : as) acc = tag i as (x : acc)
        tag i [] acc  = (i, reverse acc)

data LiftState = LS Name Int [(Name, LDecl)]

lname (NS n x) i = NS (lname n i) x
lname (UN n) i = MN i n
lname x i = MN i (show x)

liftAll :: [(Name, LDecl)] -> [(Name, LDecl)]
liftAll xs = concatMap (\ (x, d) -> lambdaLift x d) xs

lambdaLift :: Name -> LDecl -> [(Name, LDecl)]
lambdaLift n (LFun _ args e) 
      = let (e', (LS _ _ decls)) = runState (lift args e) (LS n 0 []) in
            (n, LFun n args e') : decls
lambdaLift n x = [(n, x)]

getNextName :: State LiftState Name
getNextName = do LS n i ds <- get
                 put (LS n (i + 1) ds)
                 return (lname n i)

addFn :: Name -> LDecl -> State LiftState ()
addFn fn d = do LS n i ds <- get
                put (LS n i ((fn, d) : ds))

lift :: [Name] -> LExp -> State LiftState LExp
lift env (LV v) = return (LV v)
lift env (LApp tc n args) = do args' <- mapM (lift env) args
                               return (LApp tc n args')
lift env (LLazyApp n args) = do args' <- mapM (lift env) args
                                return (LLazyApp n args')
lift env (LLazyExp (LConst c)) = return (LConst c)
lift env (LLazyExp e) = do e' <- lift env e
                           fn <- getNextName
                           addFn fn (LFun fn env e')
                           return (LLazyApp fn (map (LV . Glob) env))
lift env (LLet n v e) = do v' <- lift env v
                           e' <- lift (env ++ [n]) e
                           return (LLet n v' e')
lift env (LLam args e) = do e' <- lift (env ++ args) e
                            fn <- getNextName
                            addFn fn (LFun fn (env ++ args) e')
                            return (LApp False fn (map (LV . Glob) env))
lift env (LCon i n args) = do args' <- mapM (lift env) args
                              return (LCon i n args')
lift env (LCase e alts) = do alts' <- mapM liftA alts
                             e' <- lift env e
                             return (LCase e' alts')
  where
    liftA (LConCase i n args e) = do e' <- lift (env ++ args) e
                                     return (LConCase i n args e')
    liftA (LConstCase c e) = do e' <- lift env e
                                return (LConstCase c e')
    liftA (LDefaultCase e) = do e' <- lift env e
                                return (LDefaultCase e')
lift env (LConst c) = return (LConst c)
lift env (LForeign l t s args) = do args' <- mapM (liftF env) args
                                    return (LForeign l t s args')
  where
    liftF env (t, e) = do e' <- lift env e
                          return (t, e')
lift env (LOp f args) = do args' <- mapM (lift env) args
                           return (LOp f args')









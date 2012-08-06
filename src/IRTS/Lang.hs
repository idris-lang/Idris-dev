module IRTS.Lang where

import Core.TT

data LVar = Loc Int | Glob Name
  deriving Show

data LExp = LV LVar
          | LApp Name [LExp]
          | LLet Name LExp LExp -- name just for pretty printing
          | LCon Int Name [LExp]
          | LCase LExp [LAlt]
          | LConst Const
          | LOp PrimFn [LExp]
  deriving Show

data PrimFn = LPlus | LMinus | LTimes | LDiv | LEq 
            | LPrintNum | LPrintStr
  deriving Show

data LAlt = LConCase Int Name [Name] LExp
          | LConstCase Const LExp
          | LDefaultCase LExp
  deriving Show

data LDecl = LFun Name [Name] LExp -- name, arg names, definition
           | LConstructor Name Int Int -- constructor name, tag, arity
  deriving Show

type LDefs = Ctxt LDecl

-- TODO: scope and arity checker.

addTags :: [(Name, LDecl)] -> [(Name, LDecl)]
addTags ds = tag 0 ds
  where tag i ((n, LConstructor n' t a) : as) 
            = (n, LConstructor n' i a) : tag (i + 1) as
        tag i (x : as) = x : tag i as
        tag i [] = []

checkDefs :: LDefs -> [(Name, LDecl)] -> TC [(Name, LDecl)] 
checkDefs ctxt [] = return []
checkDefs ctxt (con@(n, LConstructor _ _ _) : xs) = do xs' <- checkDefs ctxt xs
                                                       return (con : xs')
checkDefs ctxt ((n, LFun n' args exp) : xs) 
   = do exp' <- scopecheck ctxt (zip args [0..]) exp
        xs' <- checkDefs ctxt xs
        return ((n, LFun n' args exp') : xs')

scopecheck :: LDefs -> [(Name, Int)] -> LExp -> TC LExp 
scopecheck ctxt env tm = sc env tm where
    sc env (LV (Glob n)) 
       = case lookup n (reverse env) of -- most recent first
              Just i -> return (LV (Loc i))
              Nothing -> case lookupCtxt Nothing n ctxt of
                              [LConstructor _ i ar] ->
                                  if ar == 0 then return (LCon i n [])
                                     else fail $ "Codegen error: Constructor " ++ show n ++
                                                 " has arity " ++ show ar
                              [_] -> return (LV (Glob n))
                              [] -> fail $ "Codegen error: No such variable " ++ show n
    sc env (LApp f args)
       = do args' <- mapM (sc env) args
            case lookupCtxt Nothing f ctxt of
                [LConstructor n tag ar] ->
                    if (ar == length args)
                       then return $ LCon tag n args' 
                       else fail $ "Codegen error: Constructor " ++ show f ++ 
                                   " has arity " ++ show ar
                [_] -> return $ LApp f args'
                [] -> fail $ "Codegen error: No such variable " ++ show f
    sc env (LCase e alts)
       = do e' <- sc env e
            alts' <- mapM (scalt env) alts
            return (LCase e' alts')
    sc env (LLet n v e)
       = do v' <- sc env v
            e' <- sc (env ++ [(n, length env)]) e
            return (LLet n v' e')
    sc env (LOp prim args)
       = do args' <- mapM (sc env) args
            return (LOp prim args')
    sc env x = return x

    scalt env (LConCase i n args e)
       = do let env' = env ++ zip args [length env..]
            tag <- case lookupCtxt Nothing n ctxt of
                        [LConstructor _ i ar] -> 
                             if (length args == ar) then return i
                                else fail $ "Codegen error: Constructor " ++ show n ++
                                            " has arity " ++ show ar
                        _ -> fail $ "Codegen error: No constructor " ++ show n
            e' <- sc env' e
            return (LConCase tag n args e')
    scalt env (LConstCase c e) = do e' <- sc env e
                                    return (LConstCase c e')
    scalt env (LDefaultCase e) = do e' <- sc env e
                                    return (LDefaultCase e')


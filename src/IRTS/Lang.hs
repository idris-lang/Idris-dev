{-# LANGUAGE PatternGuards, DeriveFunctor #-}

module IRTS.Lang where

import Control.Monad.State hiding (lift)
import Control.Applicative hiding (Const)
import Idris.Core.TT
import Idris.Core.CaseTree
import Data.List
import Debug.Trace

data Endianness = Native | BE | LE deriving (Show, Eq)

data LVar = Loc Int | Glob Name
  deriving (Show, Eq)

-- ASSUMPTION: All variable bindings have unique names here
data LExp = LV LVar
          | LApp Bool LExp [LExp] -- True = tail call
          | LLazyApp Name [LExp] -- True = tail call
          | LLazyExp LExp
          | LForce LExp -- make sure Exp is evaluted
          | LLet Name LExp LExp -- name just for pretty printing
          | LLam [Name] LExp -- lambda, lifted out before compiling
          | LProj LExp Int -- projection
          | LCon (Maybe LVar) -- Location to reallocate, if available
                 Int Name [LExp]
          | LCase CaseType LExp [LAlt]
          | LConst Const
          | LForeign FLang FType String [(FType, LExp)]
          | LOp PrimFn [LExp]
          | LNothing
          | LError String
  deriving Eq

-- Primitive operators. Backends are not *required* to implement all
-- of these, but should report an error if they are unable

data PrimFn = LPlus ArithTy | LMinus ArithTy | LTimes ArithTy
            | LUDiv IntTy | LSDiv ArithTy | LURem IntTy | LSRem ArithTy
            | LAnd IntTy | LOr IntTy | LXOr IntTy | LCompl IntTy
            | LSHL IntTy | LLSHR IntTy | LASHR IntTy
            | LEq ArithTy | LLt IntTy | LLe IntTy | LGt IntTy | LGe IntTy
            | LSLt ArithTy | LSLe ArithTy | LSGt ArithTy | LSGe ArithTy
            | LSExt IntTy IntTy | LZExt IntTy IntTy | LTrunc IntTy IntTy
            | LStrConcat | LStrLt | LStrEq | LStrLen
            | LIntFloat IntTy | LFloatInt IntTy | LIntStr IntTy | LStrInt IntTy
            | LFloatStr | LStrFloat | LChInt IntTy | LIntCh IntTy
            | LPrintNum | LPrintStr | LReadStr
            | LBitCast ArithTy ArithTy -- Only for values of equal width

            | LFExp | LFLog | LFSin | LFCos | LFTan | LFASin | LFACos | LFATan
            | LFSqrt | LFFloor | LFCeil

           -- construction          element extraction     element insertion
            | LMkVec NativeTy Int | LIdxVec NativeTy Int | LUpdateVec NativeTy Int

            | LStrHead | LStrTail | LStrCons | LStrIndex | LStrRev
            | LStdIn | LStdOut | LStdErr

            -- Buffers
            | LAllocate
            | LAppendBuffer
            -- system info
            | LSystemInfo
            -- Note that for Bits8 only Native endianness is actually used
            -- and the user-exposed interface for Bits8 doesn't mention
            -- endianness
            | LAppend IntTy Endianness
            | LPeek IntTy Endianness

            | LFork
            | LPar -- evaluate argument anywhere, possibly on another
                   -- core or another machine. 'id' is a valid implementation
            | LVMPtr
            | LNullPtr
            | LRegisterPtr
            | LNoOp
  deriving (Show, Eq)

-- Supported target languages for foreign calls

data FCallType = FStatic | FObject | FConstructor
  deriving (Show, Eq)

data FLang = LANG_C | LANG_JAVA FCallType
  deriving (Show, Eq)

data FType = FArith ArithTy
           | FFunction
           | FFunctionIO
           | FString
           | FUnit
           | FPtr
           | FManagedPtr
           | FAny
  deriving (Show, Eq)

-- FIXME: Why not use this for all the IRs now?
data LAlt' e = LConCase Int Name [Name] e
             | LConstCase Const e
             | LDefaultCase e
  deriving (Show, Eq, Functor)

type LAlt = LAlt' LExp

data LDecl = LFun [LOpt] Name [Name] LExp -- options, name, arg names, def
           | LConstructor Name Int Int -- constructor name, tag, arity
  deriving (Show, Eq)

type LDefs = Ctxt LDecl

data LOpt = Inline | NoInline
  deriving (Show, Eq)

addTags :: Int -> [(Name, LDecl)] -> (Int, [(Name, LDecl)])
addTags i ds = tag i ds []
  where tag i ((n, LConstructor n' (-1) a) : as) acc
            = tag (i + 1) as ((n, LConstructor n' i a) : acc)
        tag i ((n, LConstructor n' t a) : as) acc
            = tag i as ((n, LConstructor n' t a) : acc)
        tag i (x : as) acc = tag i as (x : acc)
        tag i [] acc  = (i, reverse acc)

data LiftState = LS Name Int [(Name, LDecl)]

lname (NS n x) i = NS (lname n i) x
lname (UN n) i = MN i n
lname x i = sMN i (show x)

liftAll :: [(Name, LDecl)] -> [(Name, LDecl)]
liftAll xs = concatMap (\ (x, d) -> lambdaLift x d) xs

lambdaLift :: Name -> LDecl -> [(Name, LDecl)]
lambdaLift n (LFun opts _ args e)
      = let (e', (LS _ _ decls)) = runState (lift args e) (LS n 0 []) in
            (n, LFun opts n args e') : decls
lambdaLift n x = [(n, x)]

getNextName :: State LiftState Name
getNextName = do LS n i ds <- get
                 put (LS n (i + 1) ds)
                 return (lname n i)

addFn :: Name -> LDecl -> State LiftState ()
addFn fn d = do LS n i ds <- get
                put (LS n i ((fn, d) : ds))

lift :: [Name] -> LExp -> State LiftState LExp
lift env (LV v) = return (LV v) -- Lifting happens before these can exist...
lift env (LApp tc (LV (Glob n)) args) = do args' <- mapM (lift env) args
                                           return (LApp tc (LV (Glob n)) args')
lift env (LApp tc f args) = do f' <- lift env f
                               fn <- getNextName
                               addFn fn (LFun [Inline] fn env f')
                               args' <- mapM (lift env) args
                               return (LApp tc (LV (Glob fn)) (map (LV . Glob) env ++ args'))
lift env (LLazyApp n args) = do args' <- mapM (lift env) args
                                return (LLazyApp n args')
lift env (LLazyExp (LConst c)) = return (LConst c)
-- lift env (LLazyExp (LApp tc (LV (Glob f)) args))
--                       = lift env (LLazyApp f args)
lift env (LLazyExp e) = do e' <- lift env e
                           let usedArgs = nub $ usedIn env e'
                           fn <- getNextName
                           addFn fn (LFun [NoInline] fn usedArgs e')
                           return (LLazyApp fn (map (LV . Glob) usedArgs))
lift env (LForce e) = do e' <- lift env e
                         return (LForce e')
lift env (LLet n v e) = do v' <- lift env v
                           e' <- lift (env ++ [n]) e
                           return (LLet n v' e')
lift env (LLam args e) = do e' <- lift (env ++ args) e
                            let usedArgs = nub $ usedIn env e'
                            fn <- getNextName
                            addFn fn (LFun [Inline] fn (usedArgs ++ args) e')
                            return (LApp False (LV (Glob fn)) (map (LV . Glob) usedArgs))
lift env (LProj t i) = do t' <- lift env t
                          return (LProj t' i)
lift env (LCon loc i n args) = do args' <- mapM (lift env) args
                                  return (LCon loc i n args')
lift env (LCase up e alts) = do alts' <- mapM liftA alts
                                e' <- lift env e
                                return (LCase up e' alts')
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
lift env (LError str) = return $ LError str
lift env LNothing = return $ LNothing

allocUnique :: LDecl -> LDecl
allocUnique x = x

inlineAll :: [(Name, LDecl)] -> [(Name, LDecl)]
inlineAll lds = let defs = addAlist lds emptyContext in
                    map (\ (n, def) -> (n, doInline defs def)) lds

nextN :: State Int Name
nextN = do i <- get
           put (i + 1)
           return $ sMN i "in"

-- Inline inside a declaration. Variables are still Name at this stage.
-- Need to preserve uniqueness of variable names in the resulting definition,
-- so invent a new name for every variable we encounter
doInline :: LDefs -> LDecl -> LDecl
doInline defs d@(LConstructor _ _ _) = d
doInline defs (LFun opts topn args exp) 
      = let res = evalState (inlineWith [topn] (map (\n -> (n, LV (Glob n))) args) exp) 0 in
            LFun opts topn args res
  where
    inlineWith :: [Name] -> [(Name, LExp)] -> LExp -> State Int LExp
    inlineWith done env var@(LV (Glob n)) 
                                     = case lookup n env of
                                            Just t -> return t
                                            Nothing -> return var
    inlineWith done env (LLazyApp n es) = LLazyApp n <$> (mapM (inlineWith done env) es)
    inlineWith done env (LForce e) = LForce <$> inlineWith done env e
    inlineWith done env (LLazyExp e) = LLazyExp <$> inlineWith done env e
    -- Extend the environment for Let and Lam so that bound names aren't
    -- expanded with any top level argument definitions they shadow
    inlineWith done env (LLet n val sc) 
       = do n' <- nextN
            LLet n' <$> inlineWith done env val <*>
                        inlineWith done ((n, LV (Glob n')) : env) sc
    inlineWith done env (LLam args sc)
       = do ns' <- mapM (\n -> do n' <- nextN
                                  return (n, n')) args
            LLam (map snd ns') <$>
                 inlineWith done (map (\ (n,n') -> (n, LV (Glob n'))) ns' ++ env) sc
    inlineWith done env (LProj exp i) = LProj <$> inlineWith done env exp <*> return i
    inlineWith done env (LCon loc i n es)
       = LCon loc i n <$> mapM (inlineWith done env) es
    inlineWith done env (LCase ty e alts) 
       = LCase ty <$> inlineWith done env e <*> mapM (inlineWithAlt done env) alts
    inlineWith done env (LOp f es) = LOp f <$> mapM (inlineWith done env) es
    -- the interesting case!
    inlineWith done env (LApp t (LV (Glob n)) es)
       | n `notElem` done,
         [LFun opts _ args body] <- lookupCtxt n defs,
         Inline `elem` opts,
         length es == length args
           = do es' <- mapM (inlineWith done env) es
                inlineWith (n : done) (zip args es' ++ env) body
    inlineWith done env (LApp t f es)
       = LApp t <$> inlineWith done env f <*> mapM (inlineWith done env) es
    inlineWith done env (LForeign l t s args)
       = LForeign l t s <$> mapM (\(t, e) -> do e' <- inlineWith done env e
                                                return (t, e')) args
    inlineWith done env t = return t

    inlineWithAlt done env (LConCase i n es rhs)
       = do ns' <- mapM (\n -> do n' <- nextN
                                  return (n, n')) es
            LConCase i n (map snd ns') <$> 
              inlineWith done (map (\ (n,n') -> (n, LV (Glob n'))) ns' ++ env) rhs
    inlineWithAlt done env (LConstCase c e) = LConstCase c <$> inlineWith done env e
    inlineWithAlt done env (LDefaultCase e) = LDefaultCase <$> inlineWith done env e

-- substLExp :: [(Name, LExp)] -> LExp -> LExp
-- substLExp env (LV (Glob n)) | Just t <- lookup n env = t
-- substLExp env (LApp t f as) = LApp t (substLExp env f) (map (substLExp env) as)
-- substLExp env (LLazyApp n as) = LLazyApp n (map (substLExp env) as)
-- substLExp env (LLazyExp e) = LLazyExp (substLExp env e)
-- substLExp env (LForce e) = LForce (substLExp env e)
-- substLExp env (LLet n v sc) = LLet n (substLExp env v)
--                                      (substLExp ((n, LV (Glob n)) : env) sc)
-- substLExp env (LLam args sc) 
--     = LLam args (substLExp (map (\n -> (n, LV (Glob n))) args ++ env) sc)
-- substLExp env (LProj e i) = LProj (substLExp env e) i
-- substLExp env (LCon up i n es) = LCon up i n (map (substLExp env) es)
-- substLExp env (LCase ty e alts) = LCase ty (substLExp env e) (map substC alts)
--   where
--     substC (LConCase i n args e) 
--        = LConCase i n args 
--              (substLExp (map (\n -> (n, LV (Glob n))) args ++ env) e)
--     substC (LConstCase i e) = LConstCase i (substLExp env e)
--     substC (LDefaultCase e) = LDefaultCase (substLExp env e)
-- substLExp env (LForeign l t s args)
--     = LForeign l t s (map (\ (ty, e) -> (ty, substLExp env e)) args)
-- substLExp env (LOp fn es) = LOp fn (map (substLExp env) es)
-- substLExp env t = t


-- Return variables in list which are used in the expression

usedArg env n | n `elem` env = [n]
              | otherwise = []

usedIn :: [Name] -> LExp -> [Name]
usedIn env (LV (Glob n)) = usedArg env n
usedIn env (LApp _ e args) = usedIn env e ++ concatMap (usedIn env) args
usedIn env (LLazyApp n args) = concatMap (usedIn env) args ++ usedArg env n
usedIn env (LLazyExp e) = usedIn env e
usedIn env (LForce e) = usedIn env e
usedIn env (LLet n v e) = usedIn env v ++ usedIn (env \\ [n]) e
usedIn env (LLam ns e) = usedIn (env \\ ns) e
usedIn env (LCon loc i n args) = concatMap (usedIn env) args
usedIn env (LProj t i) = usedIn env t
usedIn env (LCase up e alts) = usedIn env e ++ concatMap (usedInA env) alts
  where usedInA env (LConCase i n ns e) = usedIn env e
        usedInA env (LConstCase c e) = usedIn env e
        usedInA env (LDefaultCase e) = usedIn env e
usedIn env (LForeign _ _ _ args) = concatMap (usedIn env) (map snd args)
usedIn env (LOp f args) = concatMap (usedIn env) args
usedIn env _ = []

instance Show LExp where
   show e = show' [] "" e where
     show' env ind (LV (Loc i)) = env!!i
     show' env ind (LV (Glob n)) = show n

     show' env ind (LLazyApp e args)
        = show e ++ "|(" ++ showSep ", " (map (show' env ind) args) ++")"

     show' env ind (LApp _ e args)
        = show' env ind e ++ "(" ++ showSep ", " (map (show' env ind) args) ++")"

     show' env ind (LLazyExp e) = "lazy{ "  ++ show' env ind e ++ " }"
     show' env ind (LForce   e) = "force{ " ++ show' env ind e ++ " }"
     show' env ind (LLet n v e)
        = "let " ++ show n ++ " = " ++ show' env ind v
            ++ " in " ++ show' (env ++ [show n]) ind e

     show' env ind (LLam args e)
        = "\\ " ++ showSep "," (map show args)
            ++ " => " ++ show' (env ++ (map show args)) ind e

     show' env ind (LProj t i) = show t ++ "!" ++ show i

     show' env ind (LCon loc i n args)
        = atloc loc ++ show n ++ "(" ++ showSep ", " (map (show' env ind) args) ++ ")"
       where atloc Nothing = ""
             atloc (Just l) = "@" ++ show (LV l) ++ ":"

     show' env ind (LCase up e alts)
        = "case" ++ update ++ show' env ind e ++ " of \n" ++ fmt alts
       where
         update = case up of
                       Shared -> " "
                       Updatable -> "! "
         fmt [] = ""
         fmt [alt]
            = "\t" ++ ind ++ "| " ++ showAlt env (ind ++ "    ") alt 
         fmt (alt:as)
            = "\t" ++ ind ++ "| " ++ showAlt env (ind ++ ".   ") alt
                ++ "\n" ++ fmt as

     show' env ind (LConst c) = show c

     show' env ind (LForeign lang ty n args) = concat
            [ "foreign{ "
            ,       n ++ "("
            ,           showSep ", " (map (\(ty,x) -> show' env ind x ++ " : " ++ show ty) args)
            ,       ") : "
            ,       show ty
            , " }"
            ]

     show' env ind (LOp f args)
        = show f ++ "(" ++ showSep ", " (map (show' env ind) args) ++ ")"

     show' env ind (LError str) = "error " ++ show str
     show' env ind LNothing = "____"

     showAlt env ind (LConCase _ n args e)
          = show n ++ "(" ++ showSep ", " (map show args) ++ ") => "
             ++ show' env ind e

     showAlt env ind (LConstCase c e) = show c ++ " => " ++ show' env ind e
     showAlt env ind (LDefaultCase e) = "_ => " ++ show' env ind e

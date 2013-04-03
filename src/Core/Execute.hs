{-# LANGUAGE PatternGuards #-}
module Core.Execute (execute) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree

import Core.TT
import Core.Evaluate
import Core.CaseTree

import Debug.Trace

import Util.DynamicLinker

import Control.Applicative hiding (Const)
import Control.Monad.Trans
import Control.Monad
import Data.Maybe
import qualified Data.Map as M

import Foreign.LibFFI
import Foreign.C.String
import Foreign.Marshal.Alloc (free)

import System.IO

-- | Attempt to perform a side effect. Return either Just the next step in
-- evaluation (after performing the side effect through IO), or Nothing if no
-- IO was performed.
--
-- This function is exceedingly generous about what it will accept in order to
-- enable convenient testing at the REPL.
-- step :: TT Name -> Idris (Maybe (TT Name))
-- step tm = step' (unApply tm)
--     where step' (P _ (UN "unsafePerformIO") _, [_, arg] ) = step arg -- Only step if arg can be stepped
--           step' (P _ (UN "mkForeign") _, args) = stepForeign args
--           step' (P _ (UN "prim__IO") _, [_, arg]) = return (Just arg)
--           step' (P _ (UN "prim__readString") _, [(P _ (UN "prim__stdin") _)]) =
--               do line <- lift $ getLine
--                  return . Just . Constant . Str $ line
--           step' _ = return Nothing

-- | Perform side effects until no more can be performed, then return the
-- resulting term (possibly the argument).
-- execute :: TT Name -> Idris (TT Name)
-- execute tm = case unApply tm of
--                (P _ (UN "unsafePerformIO") _, [_, arg] ) -> execute' arg
--                _ -> return tm
--     where execute' tm = do stepped <- step tm
--                            case stepped of
--                              Nothing -> return tm
--                              Just tm' -> execute' tm'


execute :: Term -> Idris Term
execute tm = do ctxt <- getContext
                doExec [] ctxt tm

doExec :: Env -> Context -> Term -> Idris Term
doExec env ctxt p@(P Ref n ty) =
    do let val = lookupDef Nothing n ctxt
       case val of
         [Function _ tm] ->
             do val <- doExec env ctxt tm
                return val
         [TyDecl nt ty] -> return p -- abstract def
         [Operator tp arity op] -> do ty' <- doExec env ctxt ty
                                      return (P Ref n ty')
         [CaseOp _ _ _ _ _ [] (STerm tm) _ _] -> -- nullary fun
             doExec env ctxt tm
         [CaseOp _ _ _ _ _ ns sc _ _] -> return p
         thing -> trace ("got to " ++ show thing) $ undefined
doExec env ctxt p@(P Bound n ty) = case (lookupDef Nothing n ctxt) of -- bound vars must be Function
                                     [Function ty tm] -> doExec env ctxt tm
                                     [] -> return p
                                     x -> fail ("Internal error lookup up bound var " ++ show n ++ " - found " ++ show x)
doExec env ctxt p@(P (DCon a b) n ty) = do { ty' <- doExec env ctxt ty; return (P (DCon a b) n ty') }
doExec env ctxt p@(P (TCon a b) n ty) = do { ty' <- doExec env ctxt ty; return (P (TCon a b) n ty') }
doExec env ctxt v@(V i) | i < length env = do let binder = env !! i
                                              case binder of
                                                (_, (Let t v)) -> return v
                                                (_, (NLet t v)) -> return v
                                                (n, b) -> doExec env ctxt (P Bound n (binderTy b))
                        | otherwise      = return $ V i
doExec env ctxt (Bind n (Let t v) body) = do v' <- doExec env ctxt v
                                             let ctxt' = addToCtxt n v' t ctxt
                                             doExec ((n, Let t v'):env) ctxt' body
doExec env ctxt (Bind n (NLet t v) body) = trace "NLet" $ undefined
doExec env ctxt tm@(Bind n b body) = return tm -- don't eval under lambda!
doExec env ctxt a@(App _ _) = execApp env ctxt (unApply a)
doExec env ctxt (Constant c) = return (Constant c)
doExec env ctxt (Proj tm i) = let (x, xs) = unApply tm in
                              return ((x:xs) !! i)
doExec env ctxt Erased = return Erased
doExec env ctxt Impossible = fail "Tried to execute an impossible case"
doExec env ctxt (TType u) = return (TType u)

execApp :: Env -> Context -> (Term, [Term]) -> Idris Term
execApp env ctxt (f, args) = do newF <- doExec env ctxt f
                                newArgs <- mapM (doExec env ctxt) args
                                execApp' env ctxt newF newArgs

execApp' :: Env -> Context -> Term -> [Term] -> Idris Term
execApp' env ctxt v [] = return v -- no args is just a constant! can result from function calls
execApp' env ctxt (P _ (UN "mkForeign") _) args =
    do res <- stepForeign args
       case res of
         Nothing -> fail "Could not call foreign function"
         Just r -> return r
execApp' env ctxt (P _ (UN "prim__readString") _) [P _ (UN "prim__stdin") _] =
    do line <- lift getLine
       return (Constant (Str line))

execApp' env ctxt (P _ (UN "prim__concat") _)  [(Constant (Str s1)), (Constant (Str s2))] =
    return $ Constant (Str (s1 ++ s2))

execApp' env ctxt f@(P _ n _) args =
    do let val = lookupDef Nothing n ctxt
       case val of
         [Function _ tm] -> fail "should already have been eval'd"
         [TyDecl nt ty] -> return $ mkApp f args
         [Operator tp arity op] -> fail $ "Can't apply operator " ++ show n ++ " which needs special-casing"
         [CaseOp _ _ _ _ _ [] (STerm tm) _ _] -> -- nullary fun
             do rhs <- doExec env ctxt tm
                doExec env ctxt (mkApp tm args)
         [CaseOp _ _ _ _ _  ns sc _ _] ->
             do res <- execCase env ctxt ns sc args
                return $ fromMaybe (mkApp f args) res
         thing -> return $ mkApp f args

execApp' env ctxt bnd@(Bind n b body) (arg:args) = let ctxt' = addToCtxt n arg Erased ctxt in
                                                   doExec ((n, b):env) ctxt' body

execApp' env ctxt f args = return (mkApp f args)

execCase :: Env -> Context -> [Name] -> SC -> [Term] -> Idris (Maybe Term)
execCase env ctxt ns sc args =
    let arity = length ns in
    if arity <= length args
    then do let amap = (zip ns (take arity args))
            caseRes <- execCase' env ctxt amap sc
            case caseRes of
              Just res-> Just <$> doExec env ctxt (mkApp res (drop arity args))
              Nothing -> return Nothing
    else return Nothing

execCase' :: Env -> Context -> [(Name, Term)] -> SC -> Idris (Maybe Term)
execCase' env ctxt amap (STerm tm) =
    Just <$> doExec env (foldl (\c (n, t) -> addToCtxt n t Erased c) ctxt amap) tm
execCase' env ctxt amap (Case n alts) | Just tm <- lookup n amap =
    let (newCase, newBindings) = chooseAlt tm alts in
    execCase' env ctxt (amap ++ newBindings) newCase

chooseAlt :: Term -> [CaseAlt] -> (SC, [(Name, Term)])
chooseAlt _ (DefaultCase sc : alts) = (sc, [])
chooseAlt (Constant c) (ConstCase c' sc : alts) | c == c' = (sc, [])
chooseAlt tm (ConCase n i ns sc : alts) | ((P _ cn _), args) <- unApply tm, cn == n = (sc, zip ns args)
                                        | otherwise = chooseAlt tm alts
chooseAlt tm (_:alts) = chooseAlt tm alts
chooseAlt _ [] = trace "bad pattern match" undefined

data FTy = FInt | FFloat | FChar | FString | FPtr | FUnit deriving (Show, Read)

data Foreign = FFun String [FTy] FTy deriving Show

call :: Foreign -> [Term] -> Idris (Maybe Term)
call (FFun name argTypes retType) args = do fn <- findForeign name
                                            case fn of
                                              Nothing -> return Nothing
                                              Just f -> do res <- call' f args retType
                                                           return . Just $ App (P Ref (UN "prim__IO") Erased) res
    where call' :: ForeignFun -> [Term] -> FTy -> Idris Term
          call' (Fun _ h) args FInt = do res <- lift $ callFFI h retCInt (prepArgs args)
                                         return (Constant (I (fromIntegral res)))
          call' (Fun _ h) args FFloat = do res <- lift $ callFFI h retCDouble (prepArgs args)
                                           return (Constant (Fl (realToFrac res)))
          call' (Fun _ h) args FChar = do res <- lift $ callFFI h retCChar (prepArgs args)
                                          return (Constant (Ch (castCCharToChar res)))
          call' (Fun _ h) args FString = do res <- lift $ callFFI h retCString (prepArgs args)
                                            hStr <- lift $ peekCString res
--                                            lift $ free res
                                            return (Constant (Str hStr))
-- awaiting Const constructor for pointers
--          call' (Fun _ h) args FPtr = do res <- lift $ callFFI h retPtr (prepArgs args)
--                                          return (Constant (Ch (castCCharToChar res)))
          call' (Fun _ h) args FUnit = do res <- lift $ callFFI h retVoid (prepArgs args)
                                          return (P Ref unitCon (P Ref unitTy (TType (UVal 0)))) -- FIXME check universe level

          prepArgs = map prepArg
          prepArg (Constant (I i)) = argCInt (fromIntegral i)
          prepArg (Constant (Fl f)) = argCDouble (realToFrac f)
          prepArg (Constant (Ch c)) = argCChar (castCharToCChar c) -- FIXME - castCharToCChar only safe for first 256 chars
          prepArg (Constant (Str s)) = argString s
          prepArg other = trace ("Could not use " ++ show other ++ " as FFI arg.") undefined



foreignFromTT :: Term -> Maybe Foreign
foreignFromTT t = case (unApply t) of
                    (_, [(Constant (Str name)), args, ret]) ->
                        do argTy <- unList args
                           argFTy <- sequence $ map getFTy argTy
                           retFTy <- getFTy ret
                           return $ FFun name argFTy retFTy
                    _ -> trace "failed to construct ffun" Nothing

getFTy :: Term -> Maybe FTy
getFTy (P _ (UN t) _) = case t of
                          "FInt"    -> Just FInt
                          "FFloat"  -> Just FFloat
                          "FChar"   -> Just FChar
                          "FString" -> Just FString
                          "FPtr"    -> Just FPtr
                          "FUnit"   -> Just FUnit
                          _         -> Nothing
getFTy _ = Nothing

unList :: Term -> Maybe [Term]
unList tm = case unApply tm of
              (nil, [_]) -> Just []
              (cons, ([_, x, xs])) ->
                  do rest <- unList xs
                     return $ x:rest
              (f, args) -> Nothing

toConst :: Term -> Maybe Const
toConst (Constant c) = Just c
toConst _ = Nothing

stepForeign :: [Term] -> Idris (Maybe Term)
stepForeign (ty:fn:args) = do let ffun = foreignFromTT fn
                              f' <- case (call <$> ffun) of
                                      Just f -> f args
                                      Nothing -> return Nothing
                              return f'
stepForeign _ = fail "Tried to call foreign function that wasn't mkForeign"

mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f [] = return []
mapMaybeM f (x:xs) = do rest <- mapMaybeM f xs
                        x' <- f x
                        case x' of
                          Just x'' -> return (x'':rest)
                          Nothing -> return rest

findForeign :: String -> Idris (Maybe ForeignFun)
findForeign fn = do i <- getIState
                    let libs = idris_dynamic_libs i
                    fns <- mapMaybeM (lift . tryLoadFn fn) libs
                    case fns of
                      [f] -> return (Just f)
                      [] -> do iputStrLn $ "Symbol \"" ++ fn ++ "\" not found"
                               return Nothing
                      fs -> do iputStrLn $ "Symbol \"" ++ fn ++ "\" is ambiguous. Found " ++
                                           show (length fs) ++ " occurrences."
                               return Nothing


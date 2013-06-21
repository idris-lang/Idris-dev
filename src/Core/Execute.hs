{-# LANGUAGE PatternGuards, ExistentialQuantification #-}
module Core.Execute (execute) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import IRTS.Lang( IntTy(..)
                , intTyToConst
                , FType(..))

import Core.TT
import Core.Evaluate
import Core.CaseTree

import Debug.Trace

import Util.DynamicLinker
import Util.System

import Control.Applicative hiding (Const)
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Error
import Control.Monad
import Data.Maybe
import Data.Bits
import qualified Data.Map as M

import Foreign.LibFFI
import Foreign.C.String
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr

import System.IO


data Lazy = Delayed ExecEnv Context Term | Forced ExecVal deriving Show

data ExecState = ExecState { exec_thunks :: M.Map Int Lazy -- ^ Thunks - the result of evaluating "lazy" or calling lazy funcs
                           , exec_next_thunk :: Int -- ^ Ensure thunk key uniqueness
                           , exec_implicits :: Ctxt [PArg] -- ^ Necessary info on laziness from idris monad
                           , exec_dynamic_libs :: [DynamicLib] -- ^ Dynamic libs from idris monad
                           }

data ExecVal = EP NameType Name ExecVal
             | EV Int
             | EBind Name (Binder ExecVal) (ExecVal -> Exec ExecVal)
             | EApp ExecVal ExecVal
             | EType UExp
             | EErased
             | EConstant Const
             | forall a. EPtr (Ptr a)
             | EThunk Int
             | EHandle Handle

instance Show ExecVal where
  show (EP _ n _)       = show n
  show (EV i)           = "!!V" ++ show i ++ "!!"
  show (EBind n b body) = "EBind " ++ show b ++ " <<fn>>"
  show (EApp e1 e2)     = show e1 ++ " (" ++ show e2 ++ ")"
  show (EType _)        = "Type"
  show EErased          = "[__]"
  show (EConstant c)    = show c
  show (EPtr p)         = "<<ptr " ++ show p ++ ">>"
  show (EThunk i)       = "<<thunk " ++ show i ++ ">>"
  show (EHandle h)      = "<<handle " ++ show h ++ ">>"

toTT :: ExecVal -> Exec Term
toTT (EP nt n ty) = (P nt n) <$> (toTT ty)
toTT (EV i) = return $ V i
toTT (EBind n b body) = do body' <- body $ EP Bound n EErased
                           b' <- fixBinder b
                           Bind n b' <$> toTT body'
    where fixBinder (Lam t)       = Lam   <$> toTT t
          fixBinder (Pi t)        = Pi    <$> toTT t
          fixBinder (Let t1 t2)   = Let   <$> toTT t1 <*> toTT t2
          fixBinder (NLet t1 t2)  = NLet  <$> toTT t1 <*> toTT t2
          fixBinder (Hole t)      = Hole  <$> toTT t
          fixBinder (GHole t)     = GHole <$> toTT t
          fixBinder (Guess t1 t2) = Guess <$> toTT t1 <*> toTT t2
          fixBinder (PVar t)      = PVar  <$> toTT t
          fixBinder (PVTy t)      = PVTy  <$> toTT t
toTT (EApp e1 e2) = do e1' <- toTT e1
                       e2' <- toTT e2
                       return $ App e1' e2'
toTT (EType u) = return $ TType u
toTT EErased = return Erased
toTT (EConstant c) = return (Constant c)
toTT (EThunk i) = return (P (DCon 0 0) (MN i "THUNK") Erased) --(force i) >>= toTT
toTT (EHandle _) = return Erased

unApplyV :: ExecVal -> (ExecVal, [ExecVal])
unApplyV tm = ua [] tm
    where ua args (EApp f a) = ua (a:args) f
          ua args t = (t, args)

mkEApp :: ExecVal -> [ExecVal] -> ExecVal
mkEApp f [] = f
mkEApp f (a:args) = mkEApp (EApp f a) args

initState :: Idris ExecState
initState = do ist <- getIState
               return $ ExecState M.empty 0 (idris_implicits ist) (idris_dynamic_libs ist)

type Exec = ErrorT String (StateT ExecState IO)

runExec :: Exec a -> ExecState -> IO (Either String a)
runExec ex st = fst <$> runStateT (runErrorT ex) st

getExecState :: Exec ExecState
getExecState = lift get

putExecState :: ExecState -> Exec ()
putExecState = lift . put

execFail :: String -> Exec a
execFail = throwError

execIO :: IO a -> Exec a
execIO = lift . lift

delay :: ExecEnv -> Context -> Term -> Exec ExecVal
delay env ctxt tm =
    do st <- getExecState
       let i = exec_next_thunk st
       putExecState $ st { exec_thunks = M.insert i (Delayed env ctxt tm) (exec_thunks st)
                         , exec_next_thunk = exec_next_thunk st + 1
                         }
       return $ EThunk i

force :: Int -> Exec ExecVal
force i = do st <- getExecState
             case M.lookup i (exec_thunks st) of
               Just (Delayed env ctxt tm) -> do tm' <- doExec env ctxt tm
                                                case tm' of
                                                  EThunk i ->
                                                      do res <- force i
                                                         update res i
                                                         return res
                                                  _ -> do update tm' i
                                                          return tm'
               Just (Forced tm) -> return tm
               Nothing -> execFail "Tried to exec non-existing thunk. This is a bug!"
    where update :: ExecVal -> Int -> Exec ()
          update tm i = do est <- getExecState
                           putExecState $ est { exec_thunks = M.insert i (Forced tm) (exec_thunks est) }

tryForce :: ExecVal -> Exec ExecVal
tryForce (EThunk i) = force i
tryForce tm = return tm

debugThunks :: Exec ()
debugThunks = do st <- getExecState
                 execIO $ putStrLn (take 4000 (show (exec_thunks st)))

execute :: Term -> Idris Term
execute tm = do est <- initState
                ctxt <- getContext
                res <- lift $ flip runExec est $ do res <- doExec [] ctxt tm
                                                    toTT res
                case res of
                  Left err -> fail err
                  Right tm' -> return tm'

ioWrap :: ExecVal -> ExecVal
ioWrap tm = mkEApp (EP (DCon 0 2) (UN "prim__IO") EErased) [EErased, tm]

ioUnit :: ExecVal
ioUnit = ioWrap (EP Ref unitCon EErased)

type ExecEnv = [(Name, ExecVal)]

doExec :: ExecEnv -> Context -> Term -> Exec ExecVal
doExec env ctxt p@(P Ref n ty) | Just v <- lookup n env = return v
doExec env ctxt p@(P Ref n ty) =
    do let val = lookupDef n ctxt
       case val of
         [Function _ tm] -> doExec env ctxt tm
         [TyDecl _ _] -> return (EP Ref n EErased) -- abstract def
         [Operator tp arity op] -> return (EP Ref n EErased) -- will be special-cased later
         [CaseOp _ _ _ _ _ [] (STerm tm) _ _] -> -- nullary fun
             doExec env ctxt tm
         [CaseOp _ _ _ _ _ ns sc _ _] -> return (EP Ref n EErased)
         [] -> execFail $ "Could not find " ++ show n ++ " in definitions."
         thing -> trace (take 200 $ "got to " ++ show thing ++ " lookup up " ++ show n) $ undefined
doExec env ctxt p@(P Bound n ty) =
  case lookup n env of
    Nothing -> execFail "not found"
    Just tm -> return tm
doExec env ctxt (P (DCon a b) n _) = return (EP (DCon a b) n EErased)
doExec env ctxt (P (TCon a b) n _) = return (EP (TCon a b) n EErased)
doExec env ctxt v@(V i) | i < length env = return (snd (env !! i))
                        | otherwise      = execFail "env too small"
doExec env ctxt (Bind n (Let t v) body) = do v' <- doExec env ctxt v
                                             doExec ((n, v'):env) ctxt body
doExec env ctxt (Bind n (NLet t v) body) = trace "NLet" $ undefined
doExec env ctxt tm@(Bind n b body) = return $
                                     EBind n (fmap (\_->EErased) b)
                                           (\arg -> doExec ((n, arg):env) ctxt body)
doExec env ctxt a@(App _ _) = execApp env ctxt (unApply a)
doExec env ctxt (Constant c) = return (EConstant c)
doExec env ctxt (Proj tm i) = let (x, xs) = unApply tm in
                              doExec env ctxt ((x:xs) !! i)
doExec env ctxt Erased = return EErased
doExec env ctxt Impossible = fail "Tried to execute an impossible case"
doExec env ctxt (TType u) = return (EType u)

execApp :: ExecEnv -> Context -> (Term, [Term]) -> Exec ExecVal
execApp env ctxt (f, args) = do newF <- doExec env ctxt f
                                laziness <- (++ repeat False) <$> (getLaziness newF)
                                newArgs <- mapM argExec (zip args laziness)
                                execApp' env ctxt newF newArgs
    where getLaziness (EP _ (UN "lazy") _) = return [False, True]
          getLaziness (EP _ n _) = do est <- getExecState
                                      let argInfo = exec_implicits est
                                      case lookupCtxtName n argInfo of
                                        [] -> return (repeat False)
                                        [ps] -> return $ map lazyarg (snd ps)
                                        many -> execFail $ "Ambiguous " ++ show n ++ ", found " ++ (take 200 $ show many)
          getLaziness _ = return (repeat False) -- ok due to zip above
          argExec :: (Term, Bool) -> Exec ExecVal
          argExec (tm, False) = doExec env ctxt tm
          argExec (tm, True) = delay env ctxt tm


execApp' :: ExecEnv -> Context -> ExecVal -> [ExecVal] -> Exec ExecVal
execApp' env ctxt v [] = return v -- no args is just a constant! can result from function calls
execApp' env ctxt (EP _ (UN "unsafePerformIO") _) (ty:action:rest) | (prim__IO, [_, v]) <- unApplyV action =
    execApp' env ctxt v rest

execApp' env ctxt (EP _ (UN "io_bind") _) args@(_:_:v:k:rest) | (prim__IO, [_, v']) <- unApplyV v =
    do v'' <- tryForce v'
       res <- execApp' env ctxt k [v''] >>= tryForce
       execApp' env ctxt res rest
execApp' env ctxt con@(EP _ (UN "io_return") _) args@(tp:v:rest) =
    do v' <- tryForce v
       execApp' env ctxt (mkEApp con [tp, v']) rest

-- Special cases arising from not having access to the C RTS in the interpreter
execApp' env ctxt (EP _ (UN "mkForeign") _) (_:fn:EConstant (Str arg):rest)
    | Just (FFun "putStr" _ _) <- foreignFromTT fn = do execIO (putStr arg)
                                                        execApp' env ctxt ioUnit rest
execApp' env ctxt (EP _ (UN "mkForeign") _) (_:fn:EConstant (Str f):EConstant (Str mode):rest)
    | Just (FFun "fileOpen" _ _) <- foreignFromTT fn = do m <- case mode of
                                                                 "r" -> return ReadMode
                                                                 "w" -> return WriteMode
                                                                 "a" -> return AppendMode
                                                                 "rw" -> return ReadWriteMode
                                                                 "wr" -> return ReadWriteMode
                                                                 "r+" -> return ReadWriteMode
                                                                 _ -> execFail ("Invalid mode for " ++ f ++ ": " ++ mode)
                                                          h <- execIO $ openFile f m
                                                          execApp' env ctxt (ioWrap (EHandle h)) rest

execApp' env ctxt (EP _ (UN "mkForeign") _) (_:fn:(EHandle h):rest)
    | Just (FFun "fileEOF" _ _) <- foreignFromTT fn = do eofp <- execIO $ hIsEOF h
                                                         let res = ioWrap (EConstant (I $ if eofp then 1 else 0))
                                                         execApp' env ctxt res rest

execApp' env ctxt (EP _ (UN "mkForeign") _) (_:fn:(EHandle h):rest)
    | Just (FFun "fileClose" _ _) <- foreignFromTT fn = do execIO $ hClose h
                                                           execApp' env ctxt ioUnit rest

execApp' env ctxt (EP _ (UN "mkForeign") _) (_:fn:(EPtr p):rest)
    | Just (FFun "isNull" _ _) <- foreignFromTT fn = let res = ioWrap . EConstant . I $
                                                               if p == nullPtr then 1 else 0
                                                     in execApp' env ctxt res rest

execApp' env ctxt f@(EP _ (UN "mkForeign") _) args@(ty:fn:xs) | Just (FFun f argTs retT) <- foreignFromTT fn
                                                              , length xs >= length argTs =
    do res <- stepForeign (ty:fn:take (length argTs) xs)
       case res of
         Nothing -> fail $ "Could not call foreign function \"" ++ f ++
                           "\" with args " ++ show (take (length argTs) xs)
         Just r -> return (mkEApp r (drop (length argTs) xs))
                                                             | otherwise = return (mkEApp f args)

execApp' env ctxt c@(EP (DCon _ arity) n _) args =
    do args' <- mapM tryForce (take arity args)
       let restArgs = drop arity args
       execApp' env ctxt (mkEApp c args') restArgs

execApp' env ctxt c@(EP (TCon _ arity) n _) args =
    do args' <- mapM tryForce (take arity args)
       let restArgs = drop arity args
       execApp' env ctxt (mkEApp c args') restArgs

execApp' env ctxt f@(EP _ n _) args =
    do let val = lookupDef n ctxt
       case val of
         [Function _ tm] -> fail "should already have been eval'd"
         [TyDecl nt ty] -> return $ mkEApp f args
         [Operator tp arity op] ->
             if length args >= arity
               then do args' <- mapM tryForce $ take arity args
                       case getOp n args' of
                         Just res -> do r <- res
                                        execApp' env ctxt r (drop arity args)
                         Nothing -> return (mkEApp f args)
               else return (mkEApp f args)
         [CaseOp _ _ _ _ _ [] (STerm tm) _ _] -> -- nullary fun
             do rhs <- doExec env ctxt tm
                execApp' env ctxt rhs args
         [CaseOp _ _ _ _ _  ns sc _ _] ->
             do res <- execCase env ctxt ns sc args
                return $ fromMaybe (mkEApp f args) res
         thing -> return $ mkEApp f args
    where getOp :: Name -> [ExecVal] -> Maybe (Exec ExecVal)
          getOp (UN "prim__addB16") [EConstant (B16 i1), EConstant (B16 i2)] =
              primRes B16 (i1 + i2)
          getOp (UN "prim__addB32") [EConstant (B32 i1), EConstant (B32 i2)] =
              primRes B32 (i1 + i2)
          getOp (UN "prim__addB64") [EConstant (B64 i1), EConstant (B64 i2)] =
              primRes B64 (i1 + i2)
          getOp (UN "prim__addB8") [EConstant (B8 i1), EConstant (B8 i2)] =
              primRes B8 (i1 + i2)
          getOp (UN "prim__addBigInt") [EConstant (BI i1), EConstant (BI i2)] =
              primRes BI (i1 + i2)
          getOp (UN "prim__addFloat") [EConstant (Fl f1), EConstant (Fl f2)] =
              primRes Fl (f1 + f2)
          getOp (UN "prim__addInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (i1 + i2)
          getOp (UN "prim__andInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (i1 .&. i2)
          getOp (UN "prim__charToInt") [EConstant (Ch c)] =
              primRes I (fromEnum c)
          getOp (UN "prim__complInt") [EConstant (I i)] =
              primRes I (complement i)
          getOp (UN "prim__concat") [EConstant (Str s1), EConstant (Str s2)] =
              primRes Str (s1 ++ s2)
          getOp (UN "prim__divInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (i1 `div` i2)
          getOp (UN "prim__eqChar") [EConstant (Ch c1), EConstant (Ch c2)] =
              primResBool (c1 == c2)
          getOp (UN "prim__eqInt") [EConstant (I i1), EConstant (I i2)] =
              primResBool (i1 == i2)
          getOp (UN "prim__eqString") [EConstant (Str s1), EConstant (Str s2)] =
              primResBool (s1 == s2)
          getOp (UN "prim__gtChar") [EConstant (Ch i1), EConstant (Ch i2)] =
              primResBool (i1 > i2)
          getOp (UN "prim__gteChar") [EConstant (Ch i1), EConstant (Ch i2)] =
              primResBool (i1 >= i2)
          getOp (UN "prim__gtInt") [EConstant (I i1), EConstant (I i2)] =
              primResBool (i1 > i2)
          getOp (UN "prim__gteInt") [EConstant (I i1), EConstant (I i2)] =
              primResBool (i1 >= i2)
          getOp (UN "prim__intToFloat") [EConstant (I i)] =
              primRes Fl (fromRational (toRational i))
          getOp (UN "prim__intToStr") [EConstant (I i)] =
              primRes Str (show i)
          getOp (UN "prim_lenString") [EConstant (Str s)] =
              primRes I (length s)
          getOp (UN "prim__ltChar") [EConstant (Ch i1), EConstant (Ch i2)] =
              primResBool (i1 < i2)
          getOp (UN "prim__lteChar") [EConstant (Ch i1), EConstant (Ch i2)] =
              primResBool (i1 <= i2)
          getOp (UN "prim__lteInt") [EConstant (I i1), EConstant (I i2)] =
              primResBool (i1 <= i2)
          getOp (UN "prim__ltInt") [EConstant (I i1), EConstant (I i2)] =
              primResBool (i1 < i2)
          getOp (UN "prim__modInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (i1 `mod` i2)
          getOp (UN "prim__mulBigInt") [EConstant (BI i1), EConstant (BI i2)] =
              primRes BI (i1 * i2)
          getOp (UN "prim__mulFloat") [EConstant (Fl i1), EConstant (Fl i2)] =
              primRes Fl (i1 * i2)
          getOp (UN "prim__mulInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (i1 * i2)
          getOp (UN "prim__orInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (i1 .|. i2)
          getOp (UN "prim__readString") [EP _ (UN "prim__stdin") _] =
              Just $ do line <- execIO getLine
                        return (EConstant (Str line))
          getOp (UN "prim__readString") [EHandle h] =
              Just $ do contents <- execIO $ hGetLine h
                        return (EConstant (Str (contents ++ "\n")))
          getOp (UN "prim__shLInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (shiftL i1 i2)
          getOp (UN "prim__shRInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (shiftR i1 i2)
          getOp (UN "prim__strCons") [EConstant (Ch c), EConstant (Str s)] =
              primRes Str (c:s)
          getOp (UN "prim__strHead") [EConstant (Str (c:s))] =
              primRes Ch c
          getOp (UN "prim__strRev") [EConstant (Str s)] =
              primRes Str (reverse s)
          getOp (UN "prim__strTail") [EConstant (Str (c:s))] =
              primRes Str s
          getOp (UN "prim__subFloat") [EConstant (Fl i1), EConstant (Fl i2)] =
              primRes Fl (i1 - i2)
          getOp (UN "prim__subInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (i1 - i2)
          getOp (UN "prim__xorInt") [EConstant (I i1), EConstant (I i2)] =
              primRes I (i1 `xor` i2)
          getOp n args = trace ("No prim " ++ show n ++ " for " ++ take 1000 (show args)) Nothing

          primRes :: (a -> Const) -> a -> Maybe (Exec ExecVal)
          primRes constr = Just . return . EConstant . constr

          primResBool :: Bool -> Maybe (Exec ExecVal)
          primResBool b = primRes I (if b then 1 else 0)

execApp' env ctxt bnd@(EBind n b body) (arg:args) = do ret <- body arg
                                                       let (f', as) = unApplyV ret
                                                       execApp' env ctxt f' (as ++ args)
execApp' env ctxt (EThunk i) args = do f <- force i
                                       execApp' env ctxt f args
execApp' env ctxt app@(EApp _ _) args2 | (f, args1) <- unApplyV app = execApp' env ctxt f (args1 ++ args2)
execApp' env ctxt f args = return (mkEApp f args)





-- | Overall wrapper for case tree execution. If there are enough arguments, it takes them,
-- evaluates them, then begins the checks for matching cases.
execCase :: ExecEnv -> Context -> [Name] -> SC -> [ExecVal] -> Exec (Maybe ExecVal)
execCase env ctxt ns sc args =
    let arity = length ns in
    if arity <= length args
    then do let amap = zip ns args
--            trace ("Case " ++ show sc ++ "\n   in " ++ show amap ++"\n   in env " ++ show env ++ "\n\n" ) $ return ()
            caseRes <- execCase' env ctxt amap sc
            case caseRes of
              Just res -> Just <$> execApp' (map (\(n, tm) -> (n, tm)) amap ++ env) ctxt res (drop arity args)
              Nothing -> return Nothing
    else return Nothing

-- | Take bindings and a case tree and examines them, executing the matching case if possible.
execCase' :: ExecEnv -> Context -> [(Name, ExecVal)] -> SC -> Exec (Maybe ExecVal)
execCase' env ctxt amap (UnmatchedCase _) = return Nothing
execCase' env ctxt amap (STerm tm) =
    Just <$> doExec (map (\(n, v) -> (n, v)) amap ++ env) ctxt tm
execCase' env ctxt amap (Case n alts) | Just tm <- lookup n amap =
    do tm' <- tryForce tm
       case chooseAlt tm' alts of
         Just (newCase, newBindings) ->
             let amap' = newBindings ++ (filter (\(x,_) -> not (elem x (map fst newBindings))) amap) in
             execCase' env ctxt amap' newCase
         Nothing -> return Nothing

chooseAlt :: ExecVal -> [CaseAlt] -> Maybe (SC, [(Name, ExecVal)])
chooseAlt _ (DefaultCase sc : alts) = Just (sc, [])
chooseAlt (EConstant c) (ConstCase c' sc : alts) | c == c' = Just (sc, [])
chooseAlt tm (ConCase n i ns sc : alts) | ((EP _ cn _), args) <- unApplyV tm
                                        , cn == n = Just (sc, zip ns args)
                                        | otherwise = chooseAlt tm alts
chooseAlt tm (_:alts) = chooseAlt tm alts
chooseAlt _ [] = Nothing




idrisType :: FType -> ExecVal
idrisType FUnit = EP Ref unitTy EErased
idrisType ft = EConstant (idr ft)
    where idr (FInt ty) = intTyToConst ty
          idr FDouble = FlType
          idr FChar = ChType
          idr FString = StrType
          idr FPtr = PtrType

data Foreign = FFun String [FType] FType deriving Show


call :: Foreign -> [ExecVal] -> Exec (Maybe ExecVal)
call (FFun name argTypes retType) args =
    do fn <- findForeign name
       case fn of
         Nothing -> return Nothing
         Just f -> do res <- call' f args retType
                      return . Just . ioWrap $ res
    where call' :: ForeignFun -> [ExecVal] -> FType -> Exec ExecVal
          call' (Fun _ h) args (FInt ITNative) = do res <- execIO $ callFFI h retCInt (prepArgs args)
                                                    return (EConstant (I (fromIntegral res)))
          call' (Fun _ h) args (FInt IT8) = do res <- execIO $ callFFI h retCChar (prepArgs args)
                                               return (EConstant (B8 (fromIntegral res)))
          call' (Fun _ h) args (FInt IT16) = do res <- execIO $ callFFI h retCWchar (prepArgs args)
                                                return (EConstant (B16 (fromIntegral res)))
          call' (Fun _ h) args (FInt IT32) = do res <- execIO $ callFFI h retCInt (prepArgs args)
                                                return (EConstant (B32 (fromIntegral res)))
          call' (Fun _ h) args (FInt IT64) = do res <- execIO $ callFFI h retCLong (prepArgs args)
                                                return (EConstant (B64 (fromIntegral res)))
          call' (Fun _ h) args FDouble = do res <- execIO $ callFFI h retCDouble (prepArgs args)
                                            return (EConstant (Fl (realToFrac res)))
          call' (Fun _ h) args FChar = do res <- execIO $ callFFI h retCChar (prepArgs args)
                                          return (EConstant (Ch (castCCharToChar res)))
          call' (Fun _ h) args FString = do res <- execIO $ callFFI h retCString (prepArgs args)
                                            hStr <- execIO $ peekCString res
--                                            lift $ free res
                                            return (EConstant (Str hStr))

          call' (Fun _ h) args FPtr = do res <- execIO $ callFFI h (retPtr retVoid) (prepArgs args)
                                         return (EPtr res)
          call' (Fun _ h) args FUnit = do res <- execIO $ callFFI h retVoid (prepArgs args)
                                          return (EP Ref unitCon EErased)
--          call' (Fun _ h) args other = fail ("Unsupported foreign return type " ++ show other)


          prepArgs = map prepArg
          prepArg (EConstant (I i)) = argCInt (fromIntegral i)
          prepArg (EConstant (B8 i)) = argCChar (fromIntegral i)
          prepArg (EConstant (B16 i)) = argCWchar (fromIntegral i)
          prepArg (EConstant (B32 i)) = argCInt (fromIntegral i)
          prepArg (EConstant (B64 i)) = argCLong (fromIntegral i)
          prepArg (EConstant (Fl f)) = argCDouble (realToFrac f)
          prepArg (EConstant (Ch c)) = argCChar (castCharToCChar c) -- FIXME - castCharToCChar only safe for first 256 chars
          prepArg (EConstant (Str s)) = argString s
          prepArg (EPtr p) = argPtr p
          prepArg other = trace ("Could not use " ++ take 100 (show other) ++ " as FFI arg.") undefined



foreignFromTT :: ExecVal -> Maybe Foreign
foreignFromTT t = case (unApplyV t) of
                    (_, [(EConstant (Str name)), args, ret]) ->
                        do argTy <- unEList args
                           argFTy <- sequence $ map getFTy argTy
                           retFTy <- getFTy ret
                           return $ FFun name argFTy retFTy
                    _ -> trace "failed to construct ffun" Nothing

getFTy :: ExecVal -> Maybe FType
getFTy (EApp (EP _ (UN "FIntT") _) (EP _ (UN intTy) _)) =
    case intTy of
      "ITNative" -> Just $ FInt ITNative
      "IT8" -> Just $ FInt IT8
      "IT16" -> Just $ FInt IT16
      "IT32" -> Just $ FInt IT32
      "IT64" -> Just $ FInt IT64
      _ -> Nothing
getFTy (EP _ (UN t) _) =
    case t of
      "FFloat"  -> Just FDouble
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

unEList :: ExecVal -> Maybe [ExecVal]
unEList tm = case unApplyV tm of
               (nil, [_]) -> Just []
               (cons, ([_, x, xs])) ->
                   do rest <- unEList xs
                      return $ x:rest
               (f, args) -> Nothing


toConst :: Term -> Maybe Const
toConst (Constant c) = Just c
toConst _ = Nothing

stepForeign :: [ExecVal] -> Exec (Maybe ExecVal)
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

findForeign :: String -> Exec (Maybe ForeignFun)
findForeign fn = do est <- getExecState
                    let libs = exec_dynamic_libs est
                    fns <- mapMaybeM getFn libs
                    case fns of
                      [f] -> return (Just f)
                      [] -> do execIO . putStrLn $ "Symbol \"" ++ fn ++ "\" not found"
                               return Nothing
                      fs -> do execIO . putStrLn $ "Symbol \"" ++ fn ++ "\" is ambiguous. Found " ++
                                                   show (length fs) ++ " occurrences."
                               return Nothing
    where getFn lib = execIO $ catchIO (tryLoadFn fn lib) (\_ -> return Nothing)

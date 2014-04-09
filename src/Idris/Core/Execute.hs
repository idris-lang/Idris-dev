{-# LANGUAGE PatternGuards, ExistentialQuantification, CPP #-}
module Idris.Core.Execute (execute) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import IRTS.Lang(FType(..))

import Idris.Primitives(Prim(..), primitives)

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Core.CaseTree

import Debug.Trace

import Util.DynamicLinker
import Util.System

import Control.Applicative hiding (Const)
import Control.Exception
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Error
import Control.Monad
import Data.Maybe
import Data.Bits
import qualified Data.Map as M

#ifdef IDRIS_FFI
import Foreign.LibFFI
import Foreign.C.String
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr
#endif

import System.IO

#ifndef IDRIS_FFI
execute :: Term -> Idris Term
execute tm = fail "libffi not supported, rebuild Idris with -f FFI"
#else
-- else is rest of file
readMay :: (Read a) => String -> Maybe a
readMay s = case reads s of
              [(x, "")] -> Just x
              _         -> Nothing

data Lazy = Delayed ExecEnv Context Term | Forced ExecVal deriving Show

newtype ExecState = ExecState { exec_dynamic_libs :: [DynamicLib] -- ^ Dynamic libs from idris monad
                              }

data ExecVal = EP NameType Name ExecVal
             | EV Int
             | EBind Name (Binder ExecVal) (ExecVal -> Exec ExecVal)
             | EApp ExecVal ExecVal
             | EType UExp
             | EErased
             | EConstant Const
             | forall a. EPtr (Ptr a)
             | EThunk Context ExecEnv Term
             | EHandle Handle

instance Show ExecVal where
  show (EP _ n _)        = show n
  show (EV i)            = "!!V" ++ show i ++ "!!"
  show (EBind n b body)  = "EBind " ++ show b ++ " <<fn>>"
  show (EApp e1 e2)      = show e1 ++ " (" ++ show e2 ++ ")"
  show (EType _)         = "Type"
  show EErased           = "[__]"
  show (EConstant c)     = show c
  show (EPtr p)          = "<<ptr " ++ show p ++ ">>"
  show (EThunk _ env tm) = "<<thunk " ++ show env ++ "||||" ++ show tm ++ ">>"
  show (EHandle h)       = "<<handle " ++ show h ++ ">>"

toTT :: ExecVal -> Exec Term
toTT (EP nt n ty) = (P nt n) <$> (toTT ty)
toTT (EV i) = return $ V i
toTT (EBind n b body) = do body' <- body $ EP Bound n EErased
                           b' <- fixBinder b
                           Bind n b' <$> toTT body'
    where fixBinder (Lam t)       = Lam     <$> toTT t
          fixBinder (Pi t)        = Pi      <$> toTT t
          fixBinder (Let t1 t2)   = Let     <$> toTT t1 <*> toTT t2
          fixBinder (NLet t1 t2)  = NLet    <$> toTT t1 <*> toTT t2
          fixBinder (Hole t)      = Hole    <$> toTT t
          fixBinder (GHole i t)   = GHole i <$> toTT t
          fixBinder (Guess t1 t2) = Guess   <$> toTT t1 <*> toTT t2
          fixBinder (PVar t)      = PVar    <$> toTT t
          fixBinder (PVTy t)      = PVTy    <$> toTT t
toTT (EApp e1 e2) = do e1' <- toTT e1
                       e2' <- toTT e2
                       return $ App e1' e2'
toTT (EType u) = return $ TType u
toTT EErased = return Erased
toTT (EConstant c) = return (Constant c)
toTT (EThunk ctxt env tm) = do env' <- mapM toBinder env
                               return $ normalise ctxt env' tm
  where toBinder (n, v) = do v' <- toTT v
                             return (n, Let Erased v')
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
               return $ ExecState (idris_dynamic_libs ist)

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


execute :: Term -> Idris Term
execute tm = do est <- initState
                ctxt <- getContext
                res <- lift . lift . flip runExec est $
                         do res <- doExec [] ctxt tm
                            toTT res
                case res of
                  Left err -> fail err
                  Right tm' -> return tm'

ioWrap :: ExecVal -> ExecVal
ioWrap tm = mkEApp (EP (DCon 0 2) (sUN "prim__IO") EErased) [EErased, tm]

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
         [CaseOp _ _ _ _ _ (CaseDefs _ ([], STerm tm) _ _)] -> -- nullary fun
             doExec env ctxt tm
         [CaseOp _ _ _ _ _ (CaseDefs _ (ns, sc) _ _)] -> return (EP Ref n EErased)
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
doExec env ctxt a@(App _ _) =
  do let (f, args) = unApply a
     f' <- doExec env ctxt f
     args' <- case f' of
                (EP _ d _) | d == delay ->
                  case args of
                    [t,a,tm] -> do t' <- doExec env ctxt t
                                   a' <- doExec env ctxt a
                                   return [t', a', EThunk ctxt env tm]
                    _ -> mapM (doExec env ctxt) args -- partial applications are fine to evaluate
                fun' -> do mapM (doExec env ctxt) args
     execApp env ctxt f' args'
doExec env ctxt (Constant c) = return (EConstant c)
doExec env ctxt (Proj tm i) = let (x, xs) = unApply tm in
                              doExec env ctxt ((x:xs) !! i)
doExec env ctxt Erased = return EErased
doExec env ctxt Impossible = fail "Tried to execute an impossible case"
doExec env ctxt (TType u) = return (EType u)


execApp :: ExecEnv -> Context -> ExecVal -> [ExecVal] -> Exec ExecVal
execApp env ctxt v [] = return v -- no args is just a constant! can result from function calls
execApp env ctxt (EP _ f _) (t:a:delayed:rest)
  | f == force
  , (_, [_, _, EThunk tmCtxt tmEnv tm]) <- unApplyV delayed =
    do tm' <- doExec tmEnv tmCtxt tm
       execApp env ctxt tm' rest
execApp env ctxt (EP _ fp _) (ty:action:rest)
  | fp == upio,
    (prim__IO, [_, v]) <- unApplyV action
       = execApp env ctxt v rest

execApp env ctxt (EP _ fp _) args@(_:_:v:k:rest)
  | fp == piobind,
    (prim__IO, [_, v']) <- unApplyV v =
    do res <- execApp env ctxt k [v']
       execApp env ctxt res rest
execApp env ctxt con@(EP _ fp _) args@(tp:v:rest)
  | fp == pioret = execApp env ctxt (mkEApp con [tp, v]) rest

-- Special cases arising from not having access to the C RTS in the interpreter
execApp env ctxt (EP _ fp _) (_:fn:EConstant (Str arg):_:rest)
    | fp == mkfprim,
      Just (FFun "putStr" _ _) <- foreignFromTT fn 
           = do execIO (putStr arg)
                execApp env ctxt ioUnit rest
execApp env ctxt (EP _ fp _) (_:fn:_:EHandle h:_:rest)
    | fp == mkfprim,
      Just (FFun "idris_readStr" _ _) <- foreignFromTT fn
           = do contents <- execIO $ hGetLine h
                execApp env ctxt (EConstant (Str (contents ++ "\n"))) rest
execApp env ctxt (EP _ fp _) (_:fn:EConstant (Str f):EConstant (Str mode):rest)
    | fp == mkfprim,
      Just (FFun "fileOpen" _ _) <- foreignFromTT fn
           = do f <- execIO $
                     catch (do let m = case mode of
                                         "r"  -> Right ReadMode
                                         "w"  -> Right WriteMode
                                         "a"  -> Right AppendMode
                                         "rw" -> Right ReadWriteMode
                                         "wr" -> Right ReadWriteMode
                                         "r+" -> Right ReadWriteMode
                                         _    -> Left ("Invalid mode for " ++ f ++ ": " ++ mode)
                               case fmap (openFile f) m of
                                 Right h -> do h' <- h; return $ Right (ioWrap (EHandle h'), tail rest)
                                 Left err -> return $ Left err)
                           (\e -> let _ = ( e::SomeException)
                                  in return $ Right (ioWrap (EPtr nullPtr), tail rest))
                case f of
                  Left err -> execFail err
                  Right (res, rest) -> execApp env ctxt res rest

execApp env ctxt (EP _ fp _) (_:fn:(EHandle h):rest)
    | fp == mkfprim,
      Just (FFun "fileEOF" _ _) <- foreignFromTT fn
           = do eofp <- execIO $ hIsEOF h
                let res = ioWrap (EConstant (I $ if eofp then 1 else 0))
                execApp env ctxt res (tail rest)

execApp env ctxt (EP _ fp _) (_:fn:(EHandle h):rest)
    | fp == mkfprim,
      Just (FFun "fileClose" _ _) <- foreignFromTT fn
           = do execIO $ hClose h
                execApp env ctxt ioUnit (tail rest)

execApp env ctxt (EP _ fp _) (_:fn:(EPtr p):rest)
    | fp == mkfprim,
      Just (FFun "isNull" _ _) <- foreignFromTT fn
           = let res = ioWrap . EConstant . I $
                       if p == nullPtr then 1 else 0
             in execApp env ctxt res (tail rest)

-- Handles will be checked as null pointers sometimes - but if we got a
-- real Handle, then it's valid, so just return 1.
execApp env ctxt (EP _ fp _) (_:fn:(EHandle h):rest)
    | fp == mkfprim,
      Just (FFun "isNull" _ _) <- foreignFromTT fn
           = let res = ioWrap . EConstant . I $ 0
             in execApp env ctxt res (tail rest)

-- A foreign-returned char* has to be tested for NULL sometimes
execApp env ctxt (EP _ fp _) (_:fn:EConstant (Str s):rest)
    | fp == mkfprim,
      Just (FFun "isNull" _ _) <- foreignFromTT fn
           = let res = ioWrap . EConstant . I $ 0
                 in execApp env ctxt res (tail rest)

-- Right now, there's no way to send command-line arguments to the executor,
-- so just return 0.
execApp env ctxt (EP _ fp _) (_:fn:rest)
    | fp == mkfprim,
      Just (FFun "idris_numArgs" _ _) <- foreignFromTT fn
           = let res = ioWrap . EConstant . I $ 0
             in execApp env ctxt res (tail rest)
-- Throw away the 'World' argument to the foreign function

execApp env ctxt f@(EP _ fp _) args@(ty:fn:xs) | fp == mkfprim
   = case foreignFromTT fn of
        Just (FFun f argTs retT) | length xs >= length argTs ->
           do let (args', xs') = (take (length argTs) xs, -- foreign args
                                  drop (length argTs + 1) xs) -- rest
              res <- stepForeign (ty:fn:args')
              case res of
                   Nothing -> fail $ "Could not call foreign function \"" ++ f ++
                                     "\" with args " ++ show args
                   Just r -> return (mkEApp r xs')
        Nothing -> return (mkEApp f args)

execApp env ctxt c@(EP (DCon _ arity) n _) args =
    do let args' = take arity args
       let restArgs = drop arity args
       execApp env ctxt (mkEApp c args') restArgs

execApp env ctxt c@(EP (TCon _ arity) n _) args =
    do let args' = take arity args
       let restArgs = drop arity args
       execApp env ctxt (mkEApp c args') restArgs

execApp env ctxt f@(EP _ n _) args =
    do let val = lookupDef n ctxt
       case val of
         [Function _ tm] -> fail "should already have been eval'd"
         [TyDecl nt ty] -> return $ mkEApp f args
         [Operator tp arity op] ->
             if length args >= arity
               then let args' = take arity args in
                    case getOp n args' of
                      Just res -> do r <- res
                                     execApp env ctxt r (drop arity args)
                      Nothing -> return (mkEApp f args)
               else return (mkEApp f args)
         [CaseOp _ _ _ _ _ (CaseDefs _ ([], STerm tm) _ _)] -> -- nullary fun
             do rhs <- doExec env ctxt tm
                execApp env ctxt rhs args
         [CaseOp _ _ _ _ _ (CaseDefs _ (ns, sc) _ _)] ->
             do res <- execCase env ctxt ns sc args
                return $ fromMaybe (mkEApp f args) res
         thing -> return $ mkEApp f args
execApp env ctxt bnd@(EBind n b body) (arg:args) = do ret <- body arg
                                                      let (f', as) = unApplyV ret
                                                      execApp env ctxt f' (as ++ args)
execApp env ctxt app@(EApp _ _) args2 | (f, args1) <- unApplyV app = execApp env ctxt f (args1 ++ args2)
execApp env ctxt f args = return (mkEApp f args)

prs = sUN "prim__readString"
pbm = sUN "prim__believe_me"
pstd = sUN "prim__stdin"
mkfprim = sUN "mkForeignPrim"
pioret = sUN "prim_io_return"
piobind = sUN "prim_io_bind"
upio = sUN "unsafePerformPrimIO"
delay = sUN "Delay"
force = sUN "Force"

-- | Look up primitive operations in the global table and transform them into ExecVal functions
getOp :: Name -> [ExecVal] -> Maybe (Exec ExecVal)
getOp fn [_, _, x] | fn == pbm = Just (return x)
getOp fn [EP _ fn' _] 
    | fn == prs && fn' == pstd =
              Just $ do line <- execIO getLine
                        return (EConstant (Str line))
getOp fn [EHandle h]
    | fn == prs =
              Just $ do contents <- execIO $ hGetLine h
                        return (EConstant (Str (contents ++ "\n")))
getOp n args = getPrim n primitives >>= flip applyPrim args
    where getPrim :: Name -> [Prim] -> Maybe ([ExecVal] -> Maybe ExecVal)
          getPrim n [] = Nothing
          getPrim n ((Prim pn _ arity def _ _) : prims) | n == pn   = Just $ execPrim def
                                                        | otherwise = getPrim n prims

          execPrim :: ([Const] -> Maybe Const) -> [ExecVal] -> Maybe ExecVal
          execPrim f args = EConstant <$> (mapM getConst args >>= f)

          getConst (EConstant c) = Just c
          getConst _             = Nothing

          applyPrim :: ([ExecVal] -> Maybe ExecVal) -> [ExecVal] -> Maybe (Exec ExecVal)
          applyPrim fn args = return <$> fn args




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
              Just res -> Just <$> execApp (map (\(n, tm) -> (n, tm)) amap ++ env) ctxt res (drop arity args)
              Nothing -> return Nothing
    else return Nothing

-- | Take bindings and a case tree and examines them, executing the matching case if possible.
execCase' :: ExecEnv -> Context -> [(Name, ExecVal)] -> SC -> Exec (Maybe ExecVal)
execCase' env ctxt amap (UnmatchedCase _) = return Nothing
execCase' env ctxt amap (STerm tm) =
    Just <$> doExec (map (\(n, v) -> (n, v)) amap ++ env) ctxt tm
execCase' env ctxt amap (Case n alts) | Just tm <- lookup n amap =
       case chooseAlt tm alts of
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
    where idr (FArith ty) = AType ty
          idr FString = StrType
          idr FPtr = PtrType

data Foreign = FFun String [FType] FType deriving Show


call :: Foreign -> [ExecVal] -> Exec (Maybe ExecVal)
call (FFun name argTypes retType) args =
    do fn <- findForeign name
       maybe (return Nothing) (\f -> Just . ioWrap <$> call' f args retType) fn
    where call' :: ForeignFun -> [ExecVal] -> FType -> Exec ExecVal
          call' (Fun _ h) args (FArith (ATInt ITNative)) = do
            res <- execIO $ callFFI h retCInt (prepArgs args)
            return (EConstant (I (fromIntegral res)))
          call' (Fun _ h) args (FArith (ATInt (ITFixed IT8))) = do
            res <- execIO $ callFFI h retCChar (prepArgs args)
            return (EConstant (B8 (fromIntegral res)))
          call' (Fun _ h) args (FArith (ATInt (ITFixed IT16))) = do
            res <- execIO $ callFFI h retCWchar (prepArgs args)
            return (EConstant (B16 (fromIntegral res)))
          call' (Fun _ h) args (FArith (ATInt (ITFixed IT32))) = do
            res <- execIO $ callFFI h retCInt (prepArgs args)
            return (EConstant (B32 (fromIntegral res)))
          call' (Fun _ h) args (FArith (ATInt (ITFixed IT64))) = do
            res <- execIO $ callFFI h retCLong (prepArgs args)
            return (EConstant (B64 (fromIntegral res)))
          call' (Fun _ h) args (FArith ATFloat) = do
            res <- execIO $ callFFI h retCDouble (prepArgs args)
            return (EConstant (Fl (realToFrac res)))
          call' (Fun _ h) args (FArith (ATInt ITChar)) = do
            res <- execIO $ callFFI h retCChar (prepArgs args)
            return (EConstant (Ch (castCCharToChar res)))
          call' (Fun _ h) args FString = do res <- execIO $ callFFI h retCString (prepArgs args)
                                            if res == nullPtr
                                               then return (EPtr res)
                                               else do hStr <- execIO $ peekCString res
                                                       return (EConstant (Str hStr))

          call' (Fun _ h) args FPtr = EPtr <$> (execIO $ callFFI h (retPtr retVoid) (prepArgs args))
          call' (Fun _ h) args FUnit = do _ <- execIO $ callFFI h retVoid (prepArgs args)
                                          return $ EP Ref unitCon EErased
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
                    _ -> trace ("failed to construct ffun") Nothing

getFTy :: ExecVal -> Maybe FType
getFTy (EApp (EP _ (UN fi) _) (EP _ (UN intTy) _)) 
  | fi == txt "FIntT" =
    case str intTy of
      "ITNative" -> Just (FArith (ATInt ITNative))
      "ITChar" -> Just (FArith (ATInt ITChar))
      "IT8" -> Just (FArith (ATInt (ITFixed IT8)))
      "IT16" -> Just (FArith (ATInt (ITFixed IT16)))
      "IT32" -> Just (FArith (ATInt (ITFixed IT32)))
      "IT64" -> Just (FArith (ATInt (ITFixed IT64)))
      _ -> Nothing
getFTy (EP _ (UN t) _) =
    case str t of
      "FFloat"  -> Just (FArith ATFloat)
      "FString" -> Just FString
      "FPtr"    -> Just FPtr
      "FUnit"   -> Just FUnit
      _         -> Nothing
getFTy _ = Nothing

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
stepForeign (ty:fn:args) = let ffun = foreignFromTT fn
                           in case (call <$> ffun) of
                                Just f -> f args
                                Nothing -> return Nothing
stepForeign _ = fail "Tried to call foreign function that wasn't mkForeignPrim"

mapMaybeM :: (Functor m, Monad m) => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f [] = return []
mapMaybeM f (x:xs) = do rest <- mapMaybeM f xs
                        maybe rest (:rest) <$> f x
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

#endif

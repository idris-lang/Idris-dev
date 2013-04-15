{-# LANGUAGE PatternGuards #-}
module Core.Execute (execute) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree

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
import qualified Data.Map as M

import Foreign.LibFFI
import Foreign.C.String
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr

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

data Lazy = Delayed Env Context Term | Forced Term

data ExecState = ExecState { exec_thunks :: M.Map Int Lazy -- ^ Thunks - the result of evaluating "lazy" or calling lazy funcs
                           , exec_next_thunk :: Int -- ^ Ensure thunk key uniqueness
                           , exec_implicits :: Ctxt [PArg] -- ^ Necessary info on laziness from idris monad
                           , exec_dynamic_libs :: [DynamicLib] -- ^ Dynamic libs from idris monad
                           , exec_handles :: M.Map Int Handle -- ^ Opened files
                           , exec_next_handle :: Int -- ^ Ensure opened file key uniqueness
                           }

initState :: Idris ExecState
initState = do ist <- getIState
               return $ ExecState M.empty 0 (idris_implicits ist) (idris_dynamic_libs ist) M.empty 0

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

thunk :: Name
thunk = MN 0 "__execThunk"

delay :: Env -> Context -> Term -> Exec Term
delay env ctxt tm =
    do st <- getExecState
       let i = exec_next_thunk st
       putExecState $ st { exec_thunks = M.insert i (Delayed env ctxt tm) (exec_thunks st)
                         , exec_next_thunk = exec_next_thunk st + 1
                         }
       return $ App (P (DCon 1 0) thunk Erased) (Constant (I i))

force :: Int -> Exec Term
force i = do st <- getExecState
             case M.lookup i (exec_thunks st) of
               Just (Delayed env ctxt tm) -> do tm' <- doExec env ctxt tm
                                                case tm' of
                                                  App (P _ thnk _) (Constant (I i)) | thnk == thunk ->
                                                         do res <- force i
                                                            update res i
                                                            return res
                                                  _ -> do update tm' i
                                                          return tm'
               Just (Forced tm) -> return tm
               Nothing -> execFail "Tried to exec non-existing thunk. This is a bug!"
    where update :: Term -> Int -> Exec ()
          update tm i = do est <- getExecState
                           putExecState $ est { exec_thunks = M.insert i (Forced tm) (exec_thunks est) }

unLazy :: Env -> Context -> Term -> Exec Term
unLazy env ctxt tm = trace ("unLazy " ++ take 100 (show (unApply tm))) $
                     do res <- unLazy' (unApply tm)
                        trace ("unLazy res is " ++ take 100 (show res)) $ return res
    where unLazy' (P _ thnk _, (Constant (I i)):rest) | thnk == thunk = do tm <- force i
                                                                           doExec env ctxt (mkApp tm rest)
          unLazy' (tm, xs) = return $ mkApp tm xs


execute :: Term -> Idris Term
execute tm = do est <- initState
                ctxt <- getContext
                res <- lift $ runExec (doExec [] ctxt tm) est
                case res of
                  Left err -> fail err
                  Right tm' -> return tm'

ioWrap :: Term -> Term
ioWrap tm = mkApp (P Ref (UN "prim__IO") Erased) [Erased, tm]

ioUnit :: Term
ioUnit = ioWrap (P Ref unitCon Erased)

doExec :: Env -> Context -> Term -> Exec Term
doExec env ctxt p@(P Ref n ty) =
    do let val = lookupDef n ctxt
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
         thing -> trace (take 200 $ "got to " ++ show thing ++ " lookup up " ++ show n) $ undefined
doExec env ctxt p@(P Bound n ty) =
    case (lookupDef n ctxt) of -- bound vars must be Function
      [Function ty tm] -> doExec env ctxt tm
      [] -> return p
      x -> fail ("Internal error lookup up bound var " ++ show n ++ " - found " ++ show x)
doExec env ctxt p@(P (DCon _ _) n _) = return p
doExec env ctxt p@(P (TCon _ _) n _) = return p
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

execApp :: Env -> Context -> (Term, [Term]) -> Exec Term
execApp env ctxt ((P _ n _), (Constant (I i)):args) | n == thunk = do x <- force i
                                                                      doExec env ctxt (mkApp x args)
execApp env ctxt (f, args) = do newF <- doExec env ctxt f
                                laziness <- (getLaziness newF) >>= return . (++ repeat False)
                                newArgs <- mapM argExec (zip args laziness)
                                trace ((take 40 (show newF)) ++ " " ++  show (map (take 100 . show) (zip args laziness))) $ return ()
                                execApp' env ctxt newF newArgs
    where getLaziness (P _ (UN "io_bind") _) = return [False, False, False, True]
          getLaziness (P _ (UN "lazy") _) = return [True]
          getLaziness (P _ n _) = do est <- getExecState
                                     let argInfo = exec_implicits est
                                     trace ("Looking for laziness of " ++ show n ++ ", found " ++ (take 1000 . show $ lookupCtxtName n argInfo)) $ return ()
                                     case lookupCtxtName n argInfo of
                                       [] -> return (repeat False)
                                       [ps] -> return $ map lazyarg (snd ps)
                                       many -> execFail $ "Ambiguous " ++ show n ++ ", found " ++ (take 200 $ show many)
          getLaziness x = return (repeat False) -- ok due to zip above
          argExec :: (Term, Bool) -> Exec Term
          argExec (tm, False) = doExec env ctxt tm
          argExec (tm, True) = delay env ctxt tm


execApp' :: Env -> Context -> Term -> [Term] -> Exec Term
execApp' env ctxt v [] = return v -- no args is just a constant! can result from function calls
execApp' env ctxt (P _ (UN "io_bind") _) (_:_:x:k:rest) =
    trace ("x="++(take 150 (show x)) ++ " and\nk=" ++ (take 150 (show k))) $
    do x' <- doExec env ctxt x
       trace ("Arg x in io_bind from " ++ (take 150 (show x)) ++ "\n   to ==> " ++ take 150 (show x')) $ return ()
       case unApply x' of
         (P _ (UN "prim__IO") _, [_, x'']) ->
             trace ("Calling " ++ take 100 (show k)) $
             doExec env ctxt (mkApp k (x'':rest))
         _ -> execFail $ "Did not get an IO object out of " ++ take 100 (show x)
execApp' env ctxt (P _ (UN "unsafePerformIO") _) (ty:action:rest) | (prim__IO, [ty', v]) <- unApply action =
    doExec env ctxt (mkApp v rest)

-- Special cases arising from not having access to the C RTS in the interpreter

execApp' env ctxt (P _ (UN "mkForeign") _) (_:fn:Constant (Str arg):rest)
    | Just (FFun "putStr" _ _) <- foreignFromTT fn = do execIO (putStr arg)
                                                        doExec env ctxt (mkApp ioUnit rest)
execApp' env ctxt (P _ (UN "mkForeign") _) (_:fn:Constant (Str f):Constant (Str mode):rest)
    | Just (FFun "fileOpen" _ _) <- foreignFromTT fn = do trace ("Opening " ++ f ++ " with " ++ mode) $ return ()
                                                          m <- case mode of
                                                                 "r" -> return ReadMode
                                                                 "w" -> return WriteMode
                                                                 "a" -> return AppendMode
                                                                 "rw" -> return ReadWriteMode
                                                                 "wr" -> return ReadWriteMode
                                                                 "r+" -> return ReadWriteMode
                                                                 _ -> execFail ("Invalid mode for " ++ f ++ ": " ++ mode)
                                                          h <- execIO $ openFile f m
                                                          h' <- handle h
                                                          trace ("Got " ++ (take 100 (show h') ++ " and " ++ (take 100 (show rest)))) (return ())
                                                          doExec env ctxt (mkApp (ioWrap h') rest)

execApp' env ctxt (P _ (UN "mkForeign") _) (_:fn:fh:rest)
    | Just (FFun "fileEOF" _ _) <- foreignFromTT fn = trace ("feof") $
                                                      do h <- unHandle fh
                                                         eofp <- execIO $ hIsEOF h
                                                         let res = ioWrap (Constant (I $ if eofp then 1 else 0))
                                                         doExec env ctxt (mkApp res rest)


execApp' env ctxt f@(P _ (UN "mkForeign") _) args@(ty:fn:xs) | Just (FFun _ argTs retT) <- foreignFromTT fn
                                                             , length xs >= length argTs =
    do res <- stepForeign (ty:fn:take (length argTs) xs)
       case res of
         Nothing -> fail "Could not call foreign function"
         Just r -> return (mkApp r (drop (length argTs) xs))
                                                             | otherwise = return (mkApp f args)

execApp' env ctxt (P _ (UN "prim__concat") _)  [Constant (Str s1), Constant (Str s2)] =
    return $ Constant (Str (s1 ++ s2))

execApp' env ctxt (P _ (UN "prim__eqInt") _)  [Constant (I i1), Constant (I i2)] =
    return $ if i1 == i2 then Constant (I 1) else Constant (I 0)

execApp' env ctxt (P _ (UN "prim__ltInt") _) [Constant (I i1), Constant (I i2)] =
    return $ if i1 < i2 then Constant (I 1) else Constant (I 0)

execApp' env ctxt (P _ (UN "prim__subInt") _) [Constant (I i1), Constant (I i2)] =
    return . Constant . I $ i1 - i2

execApp' env ctxt (P _ (UN "prim__readString") _) [P _ (UN "prim__stdin") _] =
    do line <- execIO getLine
       return (Constant (Str line))

execApp' env ctxt (P _ (UN "prim__readString") _) [ptr] =
    trace ("prim__readStr of file") $
    do h <- unHandle ptr
       
       contents <- execIO $ hGetLine h
       return $ ioWrap (Constant (Str contents))

execApp' env ctxt f@(P _ n _) args =
    do let val = lookupDef n ctxt
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

execCase :: Env -> Context -> [Name] -> SC -> [Term] -> Exec (Maybe Term)
execCase env ctxt ns sc args = trace ("Case execution, args are " ++ take 100 (show (zip ns args))) $
    let arity = length ns in
    if arity <= length args
    then do args' <- mapM (unLazy env ctxt) (take arity args)
            trace ("Unlazied args are " ++ take 100 (show args')) $ return ()
            let amap = zip ns args'
            caseRes <- execCase' env ctxt amap sc
            case caseRes of
              Just res-> Just <$> doExec env ctxt (mkApp res (drop arity args))
              Nothing -> return Nothing
    else return Nothing

execCase' :: Env -> Context -> [(Name, Term)] -> SC -> Exec (Maybe Term)
execCase' env ctxt amap (STerm tm) =
    Just <$> doExec env (foldl (\c (n, t) -> addToCtxt n t Erased c) ctxt amap) tm
execCase' env ctxt amap (Case n alts) | Just tm <- lookup n amap
                                      , Just (newCase, newBindings) <- chooseAlt tm alts =
    execCase' env ctxt (amap ++ newBindings) newCase
                                      | otherwise = return Nothing

chooseAlt :: Term -> [CaseAlt] -> Maybe (SC, [(Name, Term)])
chooseAlt _ (DefaultCase sc : alts) = Just (sc, [])
chooseAlt (Constant c) (ConstCase c' sc : alts) | c == c' = Just (sc, [])
chooseAlt tm (ConCase n i ns sc : alts) | ((P _ cn _), args) <- unApply tm, cn == n = Just (sc, zip ns args)
                                        | otherwise = chooseAlt tm alts
chooseAlt tm (_:alts) = chooseAlt tm alts
chooseAlt _ [] = Nothing

data FTy = FInt | FFloat | FChar | FString | FPtr | FUnit deriving (Show, Read)

idrisType :: FTy -> Type
idrisType FUnit = P Ref unitTy (TType (UVal 0))
idrisType ft = Constant (idr ft)
    where idr FInt = IType
          idr FFloat = FlType
          idr FChar = ChType
          idr FString = StrType
          idr FPtr = PtrType

data Foreign = FFun String [FTy] FTy deriving Show

-- | A representation of Ptr values, which otherwise don't work in TT
ptrCon :: Name
ptrCon = MN 0 "__Ptr"

-- | Convert a Haskell pointer to a Ptr term in TT
ptr :: Ptr a -> Term
ptr p = App (P (DCon 1 0) ptrCon Erased) (Constant (I (addr p)))
    where addr p = p `minusPtr` nullPtr

-- | Convert a Ptr term in TT to a Haskell pointer
unPtr :: Term -> Maybe (Ptr a)
unPtr (App (P _ con _) (Constant (I addr))) | con == ptrCon = Just (unAddr addr)
    where unAddr a = nullPtr `plusPtr` a
unPtr _ = Nothing

handleCon :: Name
handleCon = MN 0 "__Handle"

-- | Convert a Haskell file handle to a handle term in TT (an int)
handle :: Handle -> Exec Term
handle h = do est <- getExecState
              let i = exec_next_handle est
              putExecState $ est { exec_next_handle = exec_next_handle est + 1
                                 , exec_handles = M.insert i h (exec_handles est)
                                 }
              return $ App (P (DCon 1 0) handleCon Erased) (Constant (I i))

unHandle :: Term -> Exec Handle
unHandle (App (P _ hc _) (Constant (I i))) | hc == handleCon =
    do est <- getExecState
       case M.lookup i (exec_handles est) of
         Just h -> return h
         Nothing -> execFail "Bad handle ID"
unHandle _ = execFail "Not a handle"

call :: Foreign -> [Term] -> Exec (Maybe Term)
call (FFun name argTypes retType) args =
    do fn <- findForeign name
       case fn of
         Nothing -> return Nothing
         Just f -> do res <- call' f args retType
                      return . Just $ mkApp (P Ref (UN "prim__IO") Erased) [idrisType retType, res]
    where call' :: ForeignFun -> [Term] -> FTy -> Exec Term
          call' (Fun _ h) args FInt = do res <- execIO $ callFFI h retCInt (prepArgs args)
                                         return (Constant (I (fromIntegral res)))
          call' (Fun _ h) args FFloat = do res <- execIO $ callFFI h retCDouble (prepArgs args)
                                           return (Constant (Fl (realToFrac res)))
          call' (Fun _ h) args FChar = do res <- execIO $ callFFI h retCChar (prepArgs args)
                                          return (Constant (Ch (castCCharToChar res)))
          call' (Fun _ h) args FString = do res <- execIO $ callFFI h retCString (prepArgs args)
                                            hStr <- execIO $ peekCString res
--                                            lift $ free res
                                            return (Constant (Str hStr))

          call' (Fun _ h) args FPtr = do res <- execIO $ callFFI h (retPtr retVoid) (prepArgs args)
                                         return (ptr res)
          call' (Fun _ h) args FUnit = do res <- execIO $ callFFI h retVoid (prepArgs args)
                                          return (P Ref unitCon (P Ref unitTy (TType (UVal 0)))) -- FIXME check universe level
--          call' (Fun _ h) args other = fail ("Unsupported foreign return type " ++ show other)


          prepArgs = map prepArg
          prepArg (Constant (I i)) = argCInt (fromIntegral i)
          prepArg (Constant (Fl f)) = argCDouble (realToFrac f)
          prepArg (Constant (Ch c)) = argCChar (castCharToCChar c) -- FIXME - castCharToCChar only safe for first 256 chars
          prepArg (Constant (Str s)) = argString s
          prepArg ptr | Just p <- unPtr ptr = argPtr p
          prepArg other = trace ("Could not use " ++ take 100 (show other) ++ " as FFI arg.") undefined



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

stepForeign :: [Term] -> Exec (Maybe Term)
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

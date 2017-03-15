{-|
Module      : Idris.Core.Execute
Description : Execute Idris code and deal with FFI.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE CPP, ExistentialQuantification, PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Core.Execute (execute) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Error
import Idris.Primitives (Prim(..), primitives)
import IRTS.Lang (FDesc(..), FType(..))

import Util.DynamicLinker
import Util.System

import Control.Applicative hiding (Const)
import Control.Exception
import Control.Monad hiding (forM)
import Control.Monad.Trans
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Control.Monad.Trans.State.Strict
import Data.Bits
import Data.IORef
import qualified Data.Map as M
import Data.Maybe
import Data.Time.Clock.POSIX (getPOSIXTime)
import Data.Traversable (forM)
import Debug.Trace
import System.IO

#ifdef IDRIS_FFI
import Foreign.C.String
import Foreign.LibFFI
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr
#endif

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

data ExecState = ExecState { exec_dynamic_libs :: [DynamicLib] -- ^ Dynamic libs from idris monad
                           , binderNames :: [Name] -- ^ Used to uniquify binders when converting to TT
                           }

data ExecVal = EP NameType Name ExecVal
             | EV Int
             | EBind Name (Binder ExecVal) (ExecVal -> Exec ExecVal)
             | EApp ExecVal ExecVal
             | EType UExp
             | EUType Universe
             | EErased
             | EConstant Const
             | forall a. EPtr (Ptr a)
             | EThunk Context ExecEnv Term
             | EHandle Handle
             | EStringBuf (IORef String)

mkRaw :: ExecVal -> ExecVal
mkRaw arg = EApp (EApp (EP (DCon 0 1 False) (sNS (sUN "MkRaw") ["FFI_C"]) EErased)
                       EErased) arg

instance Show ExecVal where
  show (EP _ n _)        = show n
  show (EV i)            = "!!V" ++ show i ++ "!!"
  show (EBind n b body)  = "EBind " ++ show b ++ " <<fn>>"
  show (EApp e1 e2)      = show e1 ++ " (" ++ show e2 ++ ")"
  show (EType _)         = "Type"
  show (EUType _)        = "UType"
  show EErased           = "[__]"
  show (EConstant c)     = show c
  show (EPtr p)          = "<<ptr " ++ show p ++ ">>"
  show (EThunk _ env tm) = "<<thunk " ++ show env ++ "||||" ++ show tm ++ ">>"
  show (EHandle h)       = "<<handle " ++ show h ++ ">>"
  show (EStringBuf h)    = "<<string buffer>>"

toTT :: ExecVal -> Exec Term
toTT (EP nt n ty) = (P nt n) <$> (toTT ty)
toTT (EV i) = return $ V i
toTT (EBind n b body) = do n' <- newN n
                           body' <- body $ EP Bound n' EErased
                           b' <- fixBinder b
                           Bind n' b' <$> toTT body'
    where fixBinder (Lam rig t)    = Lam rig  <$> toTT t
          fixBinder (Pi rig i t k) = Pi rig i <$> toTT t <*> toTT k
          fixBinder (Let t1 t2)   = Let     <$> toTT t1 <*> toTT t2
          fixBinder (NLet t1 t2)  = NLet    <$> toTT t1 <*> toTT t2
          fixBinder (Hole t)      = Hole    <$> toTT t
          fixBinder (GHole i ns t) = GHole i ns <$> toTT t
          fixBinder (Guess t1 t2) = Guess   <$> toTT t1 <*> toTT t2
          fixBinder (PVar rig t)  = PVar rig <$> toTT t
          fixBinder (PVTy t)      = PVTy    <$> toTT t
          newN n = do (ExecState hs ns) <- lift get
                      let n' = uniqueName n ns
                      lift (put (ExecState hs (n':ns)))
                      return n'
toTT (EApp e1 e2) = do e1' <- toTT e1
                       e2' <- toTT e2
                       return $ App Complete e1' e2'
toTT (EType u) = return $ TType u
toTT (EUType u) = return $ UType u
toTT EErased = return Erased
toTT (EConstant c) = return (Constant c)
toTT (EThunk ctxt env tm) = do env' <- mapM toBinder env
                               return $ normalise ctxt env' tm
  where toBinder (n, v) = do v' <- toTT v
                             return (n, RigW, Let Erased v')
toTT (EHandle _) = execFail $ Msg "Can't convert handles back to TT after execution."
toTT (EPtr ptr) = execFail $ Msg "Can't convert pointers back to TT after execution."
toTT (EStringBuf ptr) = execFail $ Msg "Can't convert string buffers back to TT after execution."

unApplyV :: ExecVal -> (ExecVal, [ExecVal])
unApplyV tm = ua [] tm
    where ua args (EApp f a) = ua (a:args) f
          ua args t = (t, args)

mkEApp :: ExecVal -> [ExecVal] -> ExecVal
mkEApp f [] = f
mkEApp f (a:args) = mkEApp (EApp f a) args

initState :: Idris ExecState
initState = do ist <- getIState
               return $ ExecState (idris_dynamic_libs ist) []

type Exec = ExceptT Err (StateT ExecState IO)

runExec :: Exec a -> ExecState -> IO (Either Err a)
runExec ex st = fst <$> runStateT (runExceptT ex) st

getExecState :: Exec ExecState
getExecState = lift get

putExecState :: ExecState -> Exec ()
putExecState = lift . put

execFail :: Err -> Exec a
execFail = throwE

execIO :: IO a -> Exec a
execIO = lift . lift


execute :: Term -> Idris Term
execute tm = do est <- initState
                ctxt <- getContext
                res <- lift . lift . flip runExec est $
                         do res <- doExec [] ctxt tm
                            toTT res
                case res of
                  Left err -> ierror err
                  Right tm' -> return tm'

ioWrap :: ExecVal -> ExecVal
ioWrap tm = mkEApp (EP (DCon 0 2 False) (sUN "prim__IO") EErased) [EErased, tm]

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
         [CaseOp _ _ _ _ _ (CaseDefs ([], STerm tm) _)] -> -- nullary fun
             doExec env ctxt tm
         [CaseOp _ _ _ _ _ (CaseDefs (ns, sc) _)] -> return (EP Ref n EErased)
         [] -> execFail . Msg $ "Could not find " ++ show n ++ " in definitions."
         other | length other > 1 -> execFail . Msg $ "Multiple definitions found for " ++ show n
               | otherwise        -> execFail . Msg . take 500 $ "got to " ++ show other ++ " lookup up " ++ show n
doExec env ctxt p@(P Bound n ty) =
  case lookup n env of
    Nothing -> execFail . Msg $ "not found"
    Just tm -> return tm
doExec env ctxt (P (DCon a b u) n _) = return (EP (DCon a b u) n EErased)
doExec env ctxt (P (TCon a b) n _) = return (EP (TCon a b) n EErased)
doExec env ctxt v@(V i) | i < length env = return (snd (env !! i))
                        | otherwise      = execFail . Msg $ "env too small"
doExec env ctxt (Bind n (Let t v) body) = do v' <- doExec env ctxt v
                                             doExec ((n, v'):env) ctxt body
doExec env ctxt (Bind n (NLet t v) body) = undefined
doExec env ctxt tm@(Bind n b body) = do b' <- forM b (doExec env ctxt)
                                        return $
                                          EBind n b' (\arg -> doExec ((n, arg):env) ctxt body)
doExec env ctxt a@(App _ _ _) =
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
doExec env ctxt (Inferred t) = doExec env ctxt t
doExec env ctxt (TType u) = return (EType u)
doExec env ctxt (UType u) = return (EUType u)

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
execApp env ctxt f@(EP _ fp _) args@(xs:_:_:_:args')
    | fp == mkfprim,
      (ty : fn : w : rest) <- reverse args' =
          execForeign env ctxt getArity ty fn rest (mkEApp f args)
  where getArity = case unEList xs of
                        Just as -> length as
                        _ -> 0

execApp env ctxt c@(EP (DCon _ arity _) n _) args =
    do let args' = take arity args
       let restArgs = drop arity args
       execApp env ctxt (mkEApp c args') restArgs

execApp env ctxt c@(EP (TCon _ arity) n _) args =
    do let args' = take arity args
       let restArgs = drop arity args
       execApp env ctxt (mkEApp c args') restArgs

execApp env ctxt f@(EP _ n _) args
    | Just (res, rest) <- getOp n args = do r <- res
                                            execApp env ctxt r rest
execApp env ctxt f@(EP _ n _) args =
    do let val = lookupDef n ctxt
       case val of
         [Function _ tm] -> fail "should already have been eval'd"
         [TyDecl nt ty] -> return $ mkEApp f args
         [Operator tp arity op] ->
             if length args >= arity
               then let args' = take arity args in
                    case getOp n args' of
                      Just (res, []) -> do r <- res
                                           execApp env ctxt r (drop arity args)
                      _ -> return (mkEApp f args)
               else return (mkEApp f args)
         [CaseOp _ _ _ _ _ (CaseDefs ([], STerm tm) _)] -> -- nullary fun
             do rhs <- doExec env ctxt tm
                execApp env ctxt rhs args
         [CaseOp _ _ _ _ _ (CaseDefs (ns, sc) _)] ->
             do res <- execCase env ctxt ns sc args
                return $ fromMaybe (mkEApp f args) res
         thing -> return $ mkEApp f args
execApp env ctxt bnd@(EBind n b body) (arg:args) = do ret <- body arg
                                                      let (f', as) = unApplyV ret
                                                      execApp env ctxt f' (as ++ args)
execApp env ctxt app@(EApp _ _) args2 | (f, args1) <- unApplyV app = execApp env ctxt f (args1 ++ args2)
execApp env ctxt f args = return (mkEApp f args)

execForeign env ctxt arity ty fn xs onfail
    | Just (FFun "putStr" [(_, str)] _) <- foreignFromTT arity ty fn xs
       = case str of
           EConstant (Str arg) -> do execIO (putStr arg)
                                     execApp env ctxt ioUnit (drop arity xs)
           _ -> execFail . Msg $
                  "The argument to putStr should be a constant string, but it was " ++
                  show str ++
                  ". Are all cases covered?"
    | Just (FFun "putchar" [(_, ch)] _) <- foreignFromTT arity ty fn xs
           = case ch of
               EConstant (Ch c) -> do execIO (putChar c)
                                      execApp env ctxt ioUnit (drop arity xs)
               EConstant (I i)  -> do execIO (putChar (toEnum i))
                                      execApp env ctxt ioUnit (drop arity xs)
               _ -> execFail . Msg $
                      "The argument to putchar should be a constant character, but it was " ++
                      show str ++
                      ". Are all cases covered?"
    | Just (FFun "idris_readStr" [_, (_, handle)] _) <- foreignFromTT arity ty fn xs
           = case handle of
               EHandle h -> do contents <- execIO $ hGetLine h
                               execApp env ctxt (EConstant (Str (contents ++ "\n"))) (drop arity xs)
               _ -> execFail . Msg $
                      "The argument to idris_readStr should be a handle, but it was " ++
                      show handle ++
                      ". Are all cases covered?"
    | Just (FFun "getchar" _ _) <- foreignFromTT arity ty fn xs
           = do -- The C API returns an Int which Idris library code
                -- converts; thus, we must make an int here.
                ch <- execIO $ fmap (ioWrap . EConstant . I . fromEnum) getChar
                execApp env ctxt ch xs
    | Just (FFun "idris_time" _ _) <- foreignFromTT arity ty fn xs
           = do execIO $ fmap (ioWrap . EConstant . I . round) getPOSIXTime
    | Just (FFun "fileOpen" [(_,fileStr), (_,modeStr)] _) <- foreignFromTT arity ty fn xs
           = case (fileStr, modeStr) of
               (EConstant (Str f), EConstant (Str mode)) ->
                 do f <- execIO $
                         catch (do let m = case mode of
                                             "r"  -> Right ReadMode
                                             "w"  -> Right WriteMode
                                             "a"  -> Right AppendMode
                                             "rw" -> Right ReadWriteMode
                                             "wr" -> Right ReadWriteMode
                                             "r+" -> Right ReadWriteMode
                                             _    -> Left ("Invalid mode for " ++ f ++ ": " ++ mode)
                                   case fmap (openFile f) m of
                                     Right h -> do h' <- h
                                                   hSetBinaryMode h' True
                                                   return $ Right (ioWrap (EHandle h'), drop arity xs)
                                     Left err -> return $ Left err)
                               (\e -> let _ = ( e::SomeException)
                                      in return $ Right (ioWrap (EPtr nullPtr), drop arity xs))
                    case f of
                      Left err -> execFail . Msg $ err
                      Right (res, rest) -> execApp env ctxt res rest
               _ -> execFail . Msg $
                      "The arguments to fileOpen should be constant strings, but they were " ++
                      show fileStr ++ " and " ++ show modeStr ++
                      ". Are all cases covered?"
    | Just (FFun "fileEOF" [(_,handle)] _) <- foreignFromTT arity ty fn xs
           = case handle of
               EHandle h -> do eofp <- execIO $ hIsEOF h
                               let res = ioWrap (EConstant (I $ if eofp then 1 else 0))
                               execApp env ctxt res (drop arity xs)
               _ -> execFail . Msg $
                      "The argument to fileEOF should be a file handle, but it was " ++
                      show handle ++
                      ". Are all cases covered?"
    | Just (FFun "fileError" [(_,handle)] _) <- foreignFromTT arity ty fn xs
           = case handle of
             -- errors handled differently in Haskell than in C, so if
             -- there's been an error we'll have had an exception already.
             -- Therefore, assume we're okay.
               EHandle h -> do let res = ioWrap (EConstant (I 0))
                               execApp env ctxt res (drop arity xs)
               _ -> execFail . Msg $
                      "The argument to fileError should be a file handle, but it was " ++
                      show handle ++
                      ". Are all cases covered?"
    | Just (FFun "fileClose" [(_,handle)] _) <- foreignFromTT arity ty fn xs
           = case handle of
               EHandle h -> do execIO $ hClose h
                               execApp env ctxt ioUnit (drop arity xs)
               _ -> execFail . Msg $
                      "The argument to fileClose should be a file handle, but it was " ++
                      show handle ++
                      ". Are all cases covered?"
    | Just (FFun "fileSize" [(_,handle)] _) <- foreignFromTT arity ty fn xs
           = case handle of
               EHandle h -> do size <- execIO $ hFileSize h
                               let res = ioWrap (EConstant (I (fromInteger size)))
                               execApp env ctxt res (drop arity xs)
               _ -> execFail . Msg $
                      "The argument to fileSize should be a file handle, but it was " ++
                      show handle ++
                      ". Are all cases covered?"

    | Just (FFun "isNull" [(_, ptr)] _) <- foreignFromTT arity ty fn xs
           = case ptr of
               EPtr p -> let res = ioWrap . EConstant . I $
                                   if p == nullPtr then 1 else 0
                         in execApp env ctxt res (drop arity xs)
               -- Handles will be checked as null pointers sometimes - but if we got a
               -- real Handle, then it's valid, so just return 1.
               EHandle h -> let res = ioWrap . EConstant . I $ 0
                            in execApp env ctxt res (drop arity xs)
               -- A foreign-returned char* has to be tested for NULL sometimes
               EConstant (Str s) -> let res = ioWrap . EConstant . I $ 0
                                    in execApp env ctxt res (drop arity xs)
               _ -> execFail . Msg $
                      "The argument to isNull should be a pointer or file handle or string, but it was " ++
                      show ptr ++
                      ". Are all cases covered?"

    | Just (FFun "idris_disableBuffering" _ _) <- foreignFromTT arity ty fn xs
       = do execIO $ hSetBuffering stdin NoBuffering
            execIO $ hSetBuffering stdout NoBuffering
            execApp env ctxt ioUnit (drop arity xs)

    -- Just use a Haskell String in an IORef for a string buffer
    | Just (FFun "idris_makeStringBuffer" [(_, len)] _) <- foreignFromTT arity ty fn xs
       = case len of
              EConstant (I _) -> do buf <- execIO $ newIORef ""
                                    let res = ioWrap (EStringBuf buf)
                                    execApp env ctxt res (drop arity xs)

              _ -> execFail . Msg $
                      "The argument to idris_makeStringBuffer should be an Int, but it was " ++
                      show len ++
                      ". Are all cases covered?"
    | Just (FFun "idris_addToString" [(_, strBuf), (_, str)] _) <- foreignFromTT arity ty fn xs
       = case (strBuf, str) of
              (EStringBuf ref, EConstant (Str add)) ->
                  do execIO $ modifyIORef ref (++add)
                     execApp env ctxt ioUnit (drop arity xs)
              _ -> execFail . Msg $
                      "The arguments to idris_addToString should be a StringBuffer and a String, but were " ++
                      show strBuf ++ " and " ++ show str ++
                      ". Are all cases covered?"
    | Just (FFun "idris_getString" [_, (_, str)] _) <- foreignFromTT arity ty fn xs
       = case str of
              EStringBuf ref -> do str <- execIO $ readIORef ref
                                   let res = ioWrap (mkRaw (EConstant (Str str)))
                                   execApp env ctxt res (drop arity xs)
              _ -> execFail . Msg $
                      "The argument to idris_getString should be a StringBuffer, but it was " ++
                      show str ++
                      ". Are all cases covered?"



-- Right now, there's no way to send command-line arguments to the executor,
-- so just return 0.
execForeign env ctxt arity ty fn xs onfail
    | Just (FFun "idris_numArgs" _ _) <- foreignFromTT arity ty fn xs
           = let res = ioWrap . EConstant . I $ 0
             in execApp env ctxt res (drop arity xs)

execForeign env ctxt arity ty fn xs onfail
   = case foreignFromTT arity ty fn xs of
        Just ffun@(FFun f argTs retT) | length xs >= arity ->
           do let (args', xs') = (take arity xs, -- foreign args
                                  drop arity xs) -- rest
              res <- call ffun (map snd argTs)
              case res of
                   Nothing -> fail $ "Could not call foreign function \"" ++ f ++
                                     "\" with args " ++ show (map snd argTs)
                   Just r -> return (mkEApp r xs')
        _ -> return onfail


splitArg tm | (_, [_,_,l,r]) <- unApplyV tm -- pair, two implicits
    = Just (toFDesc l, r)
splitArg _ = Nothing

toFDesc tm
   | (EP _ n _, []) <- unApplyV tm = FCon (deNS n)
   | (EP _ n _, as) <- unApplyV tm = FApp (deNS n) (map toFDesc as)
toFDesc _ = FUnknown

deNS (NS n _) = n
deNS n = n

prf = sUN "prim__readFile"
prc = sUN "prim__readChars"
pwf = sUN "prim__writeFile"
prs = sUN "prim__readString"
pws = sUN "prim__writeString"
pbm = sUN "prim__believe_me"
pstdin = sUN "prim__stdin"
pstdout = sUN "prim__stdout"
mkfprim = sUN "mkForeignPrim"
pioret = sUN "prim_io_pure"
piobind = sUN "prim_io_bind"
upio = sUN "unsafePerformPrimIO"
delay = sUN "Delay"
force = sUN "Force"

-- | Look up primitive operations in the global table and transform
-- them into ExecVal functions
getOp :: Name -> [ExecVal] -> Maybe (Exec ExecVal, [ExecVal])
getOp fn (_ : _ : x : xs) | fn == pbm = Just (return x, xs)
getOp fn (_ : EConstant (Str n) : xs)
    | fn == pws =
              Just (do execIO $ putStr n
                       return (EConstant (I 0)), xs)
getOp fn (_:xs)
    | fn == prs =
              Just (do line <- execIO getLine
                       return (EConstant (Str line)), xs)
getOp fn (_ : EP _ fn' _ : EConstant (Str n) : xs)
    | fn == pwf && fn' == pstdout =
              Just (do execIO $ putStr n
                       return (EConstant (I 0)), xs)
getOp fn (_ : EP _ fn' _ : xs)
    | fn == prf && fn' == pstdin =
              Just (do line <- execIO getLine
                       return (EConstant (Str line)), xs)
getOp fn (_ : EHandle h : EConstant (Str n) : xs)
    | fn == pwf =
              Just (do execIO $ hPutStr h n
                       return (EConstant (I 0)), xs)
getOp fn (_ : EHandle h : xs)
    | fn == prf =
              Just (do contents <- execIO $ hGetLine h
                       return (EConstant (Str (contents ++ "\n"))), xs)
getOp fn (_ : EConstant (I len) : EHandle h : xs)
    | fn == prc =
              Just (do contents <- execIO $ hGetChars h len
                       return (EConstant (Str contents)), xs)
  where hGetChars h 0 = return ""
        hGetChars h i = do eof <- hIsEOF h
                           if eof then return "" else do
                             c <- hGetChar h
                             rest <- hGetChars h (i - 1)
                             return (c : rest)
getOp fn (_ : arg : xs)
    | fn == prf =
              Just $ (execFail (Msg "Can't use prim__readFile on a raw pointer in the executor."), xs)
getOp n args = do (arity, prim) <- getPrim n primitives
                  if (length args >= arity)
                     then do res <- applyPrim prim (take arity args)
                             Just (res, drop arity args)
                     else Nothing
    where getPrim :: Name -> [Prim] -> Maybe (Int, [ExecVal] -> Maybe ExecVal)
          getPrim n [] = Nothing
          getPrim n ((Prim pn _ arity def _ _) : prims)
             | n == pn   = Just (arity, execPrim def)
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
execCase' env ctxt amap (Case sh n alts) | Just tm <- lookup n amap =
       case chooseAlt tm alts of
         Just (newCase, newBindings) ->
             let amap' = newBindings ++ (filter (\(x,_) -> not (elem x (map fst newBindings))) amap) in
             execCase' env ctxt amap' newCase
         Nothing -> return Nothing
execCase' _ _ _ cse = fail $ "The impossible happened: tried to exec  " ++ show cse

chooseAlt :: ExecVal -> [CaseAlt] -> Maybe (SC, [(Name, ExecVal)])
chooseAlt tm (DefaultCase sc : alts) | ok tm = Just (sc, [])
                                     | otherwise = Nothing
  where -- Default cases should only work on applications of constructors or on constants
        ok (EApp f x) = ok f
        ok (EP Bound _ _) = False
        ok (EP Ref _ _) = False
        ok _ = True


chooseAlt (EConstant c) (ConstCase c' sc : alts) | c == c' = Just (sc, [])
chooseAlt tm (ConCase n i ns sc : alts) | ((EP _ cn _), args) <- unApplyV tm
                                        , cn == n = Just (sc, zip ns args)
                                        | otherwise = chooseAlt tm alts
chooseAlt tm (_:alts) = chooseAlt tm alts
chooseAlt _ [] = Nothing


data Foreign = FFun String [(FDesc, ExecVal)] FDesc deriving Show

toFType :: FDesc -> FType
toFType (FCon c)
    | c == sUN "C_Str" = FString
    | c == sUN "C_Float" = FArith ATFloat
    | c == sUN "C_Ptr" = FPtr
    | c == sUN "C_MPtr" = FManagedPtr
    | c == sUN "C_Unit" = FUnit
toFType (FApp c [_,ity])
    | c == sUN "C_IntT" = FArith (toAType ity)
  where toAType (FCon i)
          | i == sUN "C_IntChar" = ATInt ITChar
          | i == sUN "C_IntNative" = ATInt ITNative
          | i == sUN "C_IntBits8" = ATInt (ITFixed IT8)
          | i == sUN "C_IntBits16" = ATInt (ITFixed IT16)
          | i == sUN "C_IntBits32" = ATInt (ITFixed IT32)
          | i == sUN "C_IntBits64" = ATInt (ITFixed IT64)
        toAType t = error (show t ++ " not defined in toAType")

toFType (FApp c [_])
    | c == sUN "C_Any" = FAny
toFType t = error (show t ++ " not defined in toFType")

call :: Foreign -> [ExecVal] -> Exec (Maybe ExecVal)
call (FFun name argTypes retType) args =
    do fn <- findForeign name
       maybe (return Nothing)
             (\f -> Just . ioWrap <$> call' f args (toFType retType)) fn
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
          call' _ _ _ = fail "the impossible happened in call' in Execute.hs"

          prepArgs = map prepArg
          prepArg (EConstant (I i)) = argCInt (fromIntegral i)
          prepArg (EConstant (B8 i)) = argCChar (fromIntegral i)
          prepArg (EConstant (B16 i)) = argCWchar (fromIntegral i)
          prepArg (EConstant (B32 i)) = argCInt (fromIntegral i)
          prepArg (EConstant (B64 i)) = argCLong (fromIntegral i)
          prepArg (EConstant (Fl f)) = argCDouble (realToFrac f)
          prepArg (EConstant (Ch c)) = argCChar (castCharToCChar c) -- FIXME - castCharToCChar only safe for first 256 chars
                                                                    -- Issue #1720 on the issue tracker.
                                                                    -- https://github.com/idris-lang/Idris-dev/issues/1720
          prepArg (EConstant (Str s)) = argString s
          prepArg (EPtr p) = argPtr p
          prepArg other = trace ("Could not use " ++ take 100 (show other) ++ " as FFI arg.") undefined


foreignFromTT :: Int -> ExecVal -> ExecVal -> [ExecVal] -> Maybe Foreign
foreignFromTT arity ty (EConstant (Str name)) args
    = do argFTyVals <- mapM splitArg (take arity args)
         return $ FFun name argFTyVals (toFDesc ty)
foreignFromTT arity ty fn args = trace ("failed to construct ffun from " ++ show (ty,fn,args)) Nothing

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

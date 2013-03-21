module Core.Execute (execute) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree

import Core.TT
import Core.Evaluate

import Debug.Trace

import Util.DynamicLinker

import Control.Applicative hiding (Const)
import Control.Monad.Trans
import Control.Monad
import Data.Maybe

import Foreign.LibFFI
import Foreign.C.String
import Foreign.Marshal.Alloc (free)

-- | Attempt to perform a side effect. Return either Just the next step in
-- evaluation (after performing the side effect through IO), or Nothing if no
-- IO was performed.
--
-- This function is exceedingly generous about what it will accept in order to
-- enable convenient testing at the REPL.
step :: TT Name -> Idris (Maybe (TT Name))
step tm = step' (unApply tm)
    where step' (P _ (UN "unsafePerformIO") _, [_, arg] ) = step arg -- Only step if arg can be stepped
          step' (P _ (UN "mkForeign") _, args) = stepForeign args
          step' (P _ (UN "prim__IO") _, [_, arg]) = step arg
          step' (P _ (UN "prim__readString") _, [(P _ (UN "prim__stdin") _)]) =
              do line <- lift $ getLine
                 return . Just . Constant . Str $ line
          step' _ = return Nothing

-- | Perform side effects until no more can be performed, then return the
-- resulting term (possibly the argument).
execute :: TT Name -> Idris (TT Name)
execute tm = case unApply tm of
               (P _ (UN "unsafePerformIO") _, [_, arg] ) -> execute' arg
               _ -> return tm
    where execute' tm = do stepped <- step tm
                           case stepped of
                             Nothing -> return tm
                             Just tm' -> execute' tm'



data FTy = FInt | FFloat | FChar | FString | FPtr | FUnit deriving (Show, Read)

data Foreign = FFun String [FTy] FTy deriving Show

call :: Foreign -> [TT Name] -> Idris (Maybe (TT Name))
call (FFun name argTypes retType) args = do fn <- findForeign name
                                            case fn of
                                              Nothing -> return Nothing
                                              Just f -> return . Just =<< call' f args retType
    where call' :: ForeignFun -> [TT Name] -> FTy -> Idris (TT Name)
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



foreignFromTT :: TT Name -> Maybe Foreign
foreignFromTT t = case (unApply t) of
                    (_, [(Constant (Str name)), args, ret]) ->
                        do argTy <- unList args
                           argFTy <- sequence $ map getFTy argTy
                           retFTy <- getFTy ret
                           return $ FFun name argFTy retFTy
                    _ -> Nothing

getFTy :: TT Name -> Maybe FTy
getFTy (P _ (UN t) _) = case t of
                          "FInt" -> Just FInt
                          "FFloat" -> Just FFloat
                          "FChar" -> Just FChar
                          "FString" -> Just FString
                          "FPtr" -> Just FPtr
                          "FUnit" -> Just FUnit
                          _ -> Nothing
getFTy _ = Nothing

unList :: TT Name -> Maybe [TT Name]
unList tm = case unApply tm of
              (nil, [_]) -> Just []
              (cons, ([_, x, xs])) ->
                  do rest <- unList xs
                     return $ x:rest
              (f, args) -> Nothing

toConst :: TT Name -> Maybe Const
toConst (Constant c) = Just c
toConst _ = Nothing

stepForeign :: [TT Name] -> Idris (Maybe (TT Name))
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


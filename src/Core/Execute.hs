module Core.Execute (execute) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree

import Core.TT
import Core.Evaluate

import Debug.Trace

import Util.DynamicLinker


-- | Attempt to perform a side effect. Return either Just the next step in
-- evaluation (after performing the side effect through IO), or Nothing if no
-- IO was performed.
step :: TT Name -> Idris (Maybe (TT Name))
step tm = step' (unApply tm)
    where step' (P _ (UN "unsafePerformIO") _, [_, arg] ) = return $ Just arg
          step' (P _ (UN "mkForeign") _, args) = do newTerm <- stepForeign args
                                                    return Nothing
          step' _ = return Nothing

-- | Perform side effects until no more can be performed, then return the
-- resulting term (possibly the argument).
execute :: TT Name -> Idris (TT Name)
execute tm = do stepped <- step tm
                case stepped of
                  Nothing -> return tm
                  Just tm' -> execute tm'



data FTy = FInt | FFloat | FChar | FString | FPtr | FUnit deriving (Show, Read)

data Foreign = FFun String [FTy] FTy deriving Show

call :: Foreign -> [TT Name] -> Idris (TT Name)
call (FFun name argTypes retType) args = undefined

foreignFromTT :: TT Name -> Maybe Foreign
foreignFromTT t = case (unApply t) of
                    (_, [(Constant (Str name)), args, ret]) ->
                        do trace (show $ unList args) $ return ()
                           argTy <- unList args
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

stepForeign :: [TT Name] -> Idris (TT Name)
stepForeign (ty:fn:args) = do iputStrLn $ "FOREIGN CALL " ++ show (ty:fn:args)
                              iputStrLn $ show $ foreignFromTT fn
                              iputStrLn ""
                              return $ mkApp (P Bound (UN "mkForeign") Erased) args
stepForeign _ = fail "Tried to call foreign function that wasn't mkForeign"
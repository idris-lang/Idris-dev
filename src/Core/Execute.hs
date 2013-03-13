module Core.Execute (execute) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree

import Core.TT
import Core.Evaluate

import Debug.Trace

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


stepForeign :: [TT Name] -> Idris (TT Name)
stepForeign args = do iputStrLn $ "FOREIGN CALL" ++ show args
                      return $ mkApp (P Bound (UN "mkForeign") Erased) args
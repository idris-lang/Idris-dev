{-# LANGUAGE PatternGuards #-}

module Idris.CaseSplit(split) where

-- splitting a variable in a pattern clause

import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Delaborate
import Idris.Error

import Core.TT
import Core.Evaluate

import Data.Maybe
import Control.Monad
import Control.Monad.State

{- 

Given a pattern clause and a variable 'n', elaborate the cluse and find the 
type of 'n'.

Make new pattern clauses by replacing 'n' with all the possibly constructors
applied to '_', and replacing all other variables with '_' in order to
resolve other dependencies.

Finally, merge the generated patterns with the original, by matching.
Always take the "more specific" argument when there is a discrepancy, i.e.
names over '_', patterns over names, etc.
-}

split :: Name -> PTerm -> Idris [PTerm]
split n t' 
   = do (tm, ty, pats) <- elabValBind toplevel True t'
        ist <- getIState
--         iputStrLn (show (delab ist tm) ++ " : " ++ show (delab ist ty))
--         iputStrLn (show pats)
        let t = mergeUserImpl (addImpl ist t') (delab ist tm) -- addImplPat ist t'
        let ctxt = tt_ctxt ist
        case lookup n pats of
             Nothing -> fail $ show n ++ " is not a pattern variable"
             Just ty -> 
                do let splits = findPats ist ty
                   let newPats_in = zipWith (replaceVar ctxt n) splits (repeat t)
                   newPats <- mapM elabNewPat newPats_in
                   logLvl 5 (showSep "\n" (map show (t : mapMaybe id newPats)))
                   logLvl 5 "----"
                   let newPats' = evalState (mapM (mergePat ctxt t)
                                                  (mapMaybe id newPats))
                                                  []
                   return newPats'

mergePat :: Context -> PTerm -> PTerm -> State [(Name, Name)] PTerm
-- If any names are unified, make sure they stay unified. Always prefer
-- user provided name (first pattern)
mergePat ctxt orig@(PRef fc n) new@(PRef _ n') 
  | isConName n' ctxt = return new
  | otherwise
    = do nmap <- get
         case lookup n' nmap of
              Just x -> return (PRef fc x)
              Nothing -> do put ((n', n) : nmap)
                            return (PRef fc n)
mergePat ctxt (PApp _ _ args) (PApp fc f args') 
      = do newArgs <- zipWithM mergeArg args args'
           return (PApp fc f newArgs)
   where mergeArg x y = do tm' <- mergePat ctxt (getTm x) (getTm y)
                           case x of
                                (PImp _ _ _ _ _ _) ->
                                   return (y { machine_inf = machine_inf x,
                                               getTm = tm' })
                                _ -> return (y { getTm = tm' })
mergePat ctxt (PRef fc n) t = tidy t
mergePat ctxt x y = return y

mergeUserImpl :: PTerm -> PTerm -> PTerm
mergeUserImpl x y = x

tidy orig@(PRef fc n) 
     = do nmap <- get
          case lookup n nmap of
               Just x -> return (PRef fc x)
               Nothing -> case n of
                               (UN _) -> return orig
                               _ -> return Placeholder
tidy (PApp fc f args)
     = do args' <- mapM tidyArg args
          return (PApp fc f args')
    where tidyArg x = do tm' <- tidy (getTm x)
                         return (x { getTm = tm' })
tidy tm = return tm


-- mapPT tidyVar tm
--   where tidyVar (PRef _ _) = Placeholder
--         tidyVar t = t

elabNewPat :: PTerm -> Idris (Maybe PTerm)
elabNewPat t = idrisCatch (do (tm, ty) <- elabVal toplevel True t
                              i <- getIState
                              return (Just (delab i tm)))
                          (\e -> return Nothing)

findPats :: IState -> Type -> [PTerm]
findPats ist t | (P _ n _, _) <- unApply t
    = case lookupCtxt n (idris_datatypes ist) of
           [ti] -> map genPat (con_names ti)
           _ -> [Placeholder]
    where genPat n = case lookupCtxt n (idris_implicits ist) of
                        [args] -> PApp emptyFC (PRef emptyFC n)
                                         (map toPlaceholder args)
                        _ -> error $ "Can't happen (genPat) " ++ show n
          toPlaceholder tm = tm { getTm = Placeholder }
findPats ist t = [Placeholder]

replaceVar :: Context -> Name -> PTerm -> PTerm -> PTerm
replaceVar ctxt n t (PApp fc f pats) = PApp fc f (map substArg pats)
  where subst :: PTerm -> PTerm
        subst orig@(PRef _ v) | v == n = t
                              | isConName v ctxt = orig
        subst (PRef _ _) = Placeholder
        subst (PApp fc f pats) = PApp fc f (map substArg pats)
        subst x = x

        substArg arg = arg { getTm = subst (getTm arg) }

replaceVar ctxt n t pat = pat




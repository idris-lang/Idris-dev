{-# LANGUAGE PatternGuards #-}

module Idris.CaseSplit(split, splitOnLine, replaceSplits,
                       getClause, getProofClause,
                       mkWith,
                       getUniq, nameRoot) where

-- splitting a variable in a pattern clause

import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Delaborate
import Idris.Parser
import Idris.Error

import Core.TT
import Core.Typecheck
import Core.Evaluate

import Data.Maybe
import Data.Char
import Control.Monad
import Control.Monad.State.Strict

import Text.Parser.Combinators
import Text.Parser.Char(anyChar)
import Text.Trifecta(Result(..), parseString)
import Text.Trifecta.Delta
import qualified Data.ByteString.UTF8 as UTF8

import Debug.Trace

{-

Given a pattern clause and a variable 'n', elaborate the clause and find the
type of 'n'.

Make new pattern clauses by replacing 'n' with all the possibly constructors
applied to '_', and replacing all other variables with '_' in order to
resolve other dependencies.

Finally, merge the generated patterns with the original, by matching.
Always take the "more specific" argument when there is a discrepancy, i.e.
names over '_', patterns over names, etc.
-}

-- Given a variable to split, and a term application, return a list of
-- variable updates
split :: Name -> PTerm -> Idris [[(Name, PTerm)]]
split n t'
   = do ist <- getIState
        (tm, ty, pats) <- elabValBind toplevel True (addImplPat ist t')
        logLvl 4 ("Elaborated:\n" ++ show tm ++ " : " ++ show ty ++ "\n" ++ show pats)
--         iputStrLn (show (delab ist tm) ++ " : " ++ show (delab ist ty))
--         iputStrLn (show pats)
        let t = mergeUserImpl (addImplPat ist t') (delab ist tm) 
        let ctxt = tt_ctxt ist
        case lookup n pats of
             Nothing -> fail $ show n ++ " is not a pattern variable"
             Just ty ->
                do let splits = findPats ist ty
                   iLOG ("New patterns " ++ show splits)
                   let newPats_in = zipWith (replaceVar ctxt n) splits (repeat t)
                   logLvl 4 ("Working from " ++ show t)
                   logLvl 4 ("Trying " ++ showSep "\n" (map show newPats_in))
                   newPats <- mapM elabNewPat newPats_in
                   logLvl 3 ("Original:\n" ++ show t)
                   logLvl 3 ("Split:\n" ++
                              (showSep "\n" (map show (mapMaybe id newPats))))
                   logLvl 3 "----"
                   let newPats' = mergeAllPats ctxt t (mapMaybe id newPats)
                   iLOG ("Name updates " ++ showSep "\n"
                         (map (\ (p, u) -> show u ++ " " ++ show p) newPats'))
                   return (map snd newPats')

data MergeState = MS { namemap :: [(Name, Name)],
                       updates :: [(Name, PTerm)] }

addUpdate n tm = do ms <- get
                    put (ms { updates = ((n, stripNS tm) : updates ms) } )

stripNS tm = mapPT dens tm where
    dens (PRef fc n) = PRef fc (nsroot n)
    dens t = t

mergeAllPats :: Context -> PTerm -> [PTerm] -> [(PTerm, [(Name, PTerm)])]
mergeAllPats ctxt t [] = []
mergeAllPats ctxt t (p : ps)
    = let (p', MS _ u) = runState (mergePat ctxt t p) (MS [] [])
          ps' = mergeAllPats ctxt t ps in
          ((p, u) : ps')

mergePat :: Context -> PTerm -> PTerm -> State MergeState PTerm
-- If any names are unified, make sure they stay unified. Always prefer
-- user provided name (first pattern)
mergePat ctxt (PPatvar fc n) new
  = mergePat ctxt (PRef fc n) new
mergePat ctxt old (PPatvar fc n)
  = mergePat ctxt old (PRef fc n)
mergePat ctxt orig@(PRef fc n) new@(PRef _ n')
  | isDConName n' ctxt = do addUpdate n new;
                            return new
  | otherwise
    = do ms <- get
         case lookup n' (namemap ms) of
              Just x -> do addUpdate n (PRef fc x)
                           return (PRef fc x)
              Nothing -> do put (ms { namemap = ((n', n) : namemap ms) })
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
mergePat ctxt (PRef fc n) t = do tm <- tidy t
                                 addUpdate n tm
                                 return tm
mergePat ctxt x y = return y

mergeUserImpl :: PTerm -> PTerm -> PTerm
mergeUserImpl x y = x

tidy orig@(PRef fc n)
     = do ms <- get
          case lookup n (namemap ms) of
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
        subst orig@(PPatvar _ v) | v == n = t
                                 | otherwise = Placeholder
        subst orig@(PRef _ v) | v == n = t
                              | isDConName v ctxt = orig
        subst (PRef _ _) = Placeholder
        subst (PApp fc f pats) = PApp fc f (map substArg pats)
        subst (PEq fc l r) = PEq fc (subst l) (subst r)
        subst x = x

        substArg arg = arg { getTm = subst (getTm arg) }

replaceVar ctxt n t pat = pat

splitOnLine :: Int -- ^ line number
               -> Name -- ^ variable
               -> FilePath -- ^ name of file
               -> Idris [[(Name, PTerm)]]
splitOnLine l n fn = do
--     let (before, later) = splitAt (l-1) (lines inp)
--     i <- getIState
    cl <- getInternalApp fn l
    logLvl 3 ("Working with " ++ showImp Nothing True False cl)
    tms <- split n cl
--     iputStrLn (showSep "\n" (map show tms))
    return tms -- "" -- not yet done...

replaceSplits :: String -> [[(Name, PTerm)]] -> Idris [String]
replaceSplits l ups = updateRHSs 1 (map (rep (expandBraces l)) ups)
  where
    rep str [] = str ++ "\n"
    rep str ((n, tm) : ups) = rep (updatePat False (show n) (nshow False tm) str) ups

    updateRHSs i [] = return []
    updateRHSs i (x : xs) = do (x', i') <- updateRHS i x
                               xs' <- updateRHSs i' xs
                               return (x' : xs')

    updateRHS i ('?':'=':xs) = do (xs', i') <- updateRHS i xs
                                  return ("?=" ++ xs', i')
    updateRHS i ('?':xs) = do let (nm, rest) = span (not . isSpace) xs
                              (nm', i') <- getUniq nm i
                              return ('?':nm' ++ rest, i')
    updateRHS i (x : xs) = do (xs', i') <- updateRHS i xs
                              return (x : xs', i')
    updateRHS i [] = return ("", i)


    -- TMP HACK: If there are Nats, we don't want to show as numerals since
    -- this isn't supported in a pattern, so special case here
    nshow brack (PRef _ (UN "Z")) = "Z"
    nshow brack (PApp _ (PRef _ (UN "S")) [x]) =
       if brack then "(S " else "S " ++ nshow True (getTm x) ++
       if brack then ")" else ""
    nshow _ t = show t

    -- if there's any {n} replace with {n=n}
    expandBraces ('{' : xs)
        = let (brace, (_:rest)) = span (/= '}') xs in
              if (not ('=' `elem` brace))
                 then ('{' : brace ++ " = " ++ brace ++ "}") ++
                         expandBraces rest
                 else ('{' : brace ++ "}") ++ expandBraces rest
    expandBraces (x : xs) = x : expandBraces xs
    expandBraces [] = []

    updatePat start n tm [] = []
    updatePat start n tm ('{':rest) =
        let (space, rest') = span isSpace rest in
            '{' : space ++ updatePat False n tm rest'
    updatePat True n tm xs@(c:rest) | length xs > length n
        = let (before, after@(next:_)) = splitAt (length n) xs in
              if (before == n && not (isAlpha next))
                 then addBrackets tm ++ updatePat False n tm after
                 else c : updatePat (not (isAlpha c)) n tm rest
    updatePat start n tm (c:rest) = c : updatePat (not (isAlpha c)) n tm rest

    addBrackets tm | ' ' `elem` tm = "(" ++ tm ++ ")"
                   | otherwise = tm

getUniq nm i
       = do ist <- getIState
            let n = nameRoot [] nm ++ "_" ++ show i
            case lookupTy (UN n) (tt_ctxt ist) of
                 [] -> return (n, i+1)
                 _ -> getUniq nm (i+1)

nameRoot acc nm | all isDigit nm = showSep "_" acc
nameRoot acc nm =
        case span (/='_') nm of
             (before, ('_' : after)) -> nameRoot (acc ++ [before]) after
             _ -> showSep "_" (acc ++ [nm])

getClause :: Int -> -- ^ Line type is declared on
             Name -> -- ^ Function name
             FilePath -> -- ^ Source file name
             Idris String
getClause l fn fp = do ty <- getInternalApp fp l
                       let ap = mkApp ty [1..]
                       return (show fn ++ " " ++ ap ++
                                   "= ?" ++ show fn ++ "_rhs")
   where mkApp (PPi (Exp _ _ _ False) (MN _ _) _ sc) (n : ns)
               = "x" ++ show n ++ " " ++ mkApp sc ns
         mkApp (PPi (Exp _ _ _ False) n _ sc) ns
               = show n ++ " " ++ mkApp sc ns
         mkApp (PPi _ _ _ sc) ns = mkApp sc ns
         mkApp _ _ = ""

getProofClause :: Int -> -- ^ Line type is declared on
                  Name -> -- ^ Function name
                  FilePath -> -- ^ Source file name
                  Idris String
getProofClause l fn fp
                  = do ty <- getInternalApp fp l
                       return (mkApp ty ++ " = ?" ++ show fn ++ "_rhs")
   where mkApp (PPi _ _ _ sc) = mkApp sc
         mkApp rt = "(" ++ show rt ++ ") <== " ++ show fn

-- Purely syntactic - turn a pattern match clause into a with and a new
-- match clause

mkWith :: String -> Name -> String
mkWith str n = let ind = getIndent str
                   str' = replicate ind ' ' ++
                          replaceRHS str "with (_)"
                   newpat = replicate (ind + 2) ' ' ++
                            replaceRHS str "| with_pat = ?" ++ show n ++ "_rhs" in
                   str' ++ "\n" ++ newpat

   where getIndent s = length (takeWhile isSpace s)

         replaceRHS [] str = str
         replaceRHS ('?':'=': rest) str = str
         replaceRHS ('=': rest) str = str
         replaceRHS (x : rest) str = x : replaceRHS rest str

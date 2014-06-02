{-# LANGUAGE PatternGuards #-}

module Idris.CaseSplit(splitOnLine, replaceSplits,
                       getClause, getProofClause,
                       mkWith,
                       nameMissing,
                       getUniq, nameRoot) where

-- splitting a variable in a pattern clause

import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Delaborate
import Idris.Parser
import Idris.Error
import Idris.Output

import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Core.Evaluate

import Data.Maybe
import Data.Char
import Data.List (isPrefixOf, isSuffixOf)
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
        -- Make sure all the names in the term are accessible
        mapM_ (\n -> setAccessibility n Public) (allNamesIn t')
        (tm, ty, pats) <- elabValBind toplevel True True (addImplPat ist t')
        -- ASSUMPTION: tm is in normal form after elabValBind, so we don't
        -- need to do anything special to find out what family each argument
        -- is in
        logLvl 4 ("Elaborated:\n" ++ show tm ++ " : " ++ show ty ++ "\n" ++ show pats)
--         iputStrLn (show (delab ist tm) ++ " : " ++ show (delab ist ty))
--         iputStrLn (show pats)
        let t = mergeUserImpl (addImplPat ist t') (delab ist tm) 
        let ctxt = tt_ctxt ist
        case lookup n pats of
             Nothing -> fail $ show n ++ " is not a pattern variable"
             Just ty ->
                do let splits = findPats ist ty
                   iLOG ("New patterns " ++ showSep ", "  
                         (map showTmImpls splits))
                   let newPats_in = zipWith (replaceVar ctxt n) splits (repeat t)
                   logLvl 4 ("Working from " ++ show t)
                   logLvl 4 ("Trying " ++ showSep "\n" 
                               (map (showTmImpls) newPats_in))
                   newPats <- mapM elabNewPat newPats_in
                   logLvl 3 ("Original:\n" ++ show t)
                   logLvl 3 ("Split:\n" ++
                              (showSep "\n" (map show (mapMaybe id newPats))))
                   logLvl 3 "----"
                   let newPats' = mergeAllPats ist n t (mapMaybe id newPats)
                   iLOG ("Name updates " ++ showSep "\n"
                         (map (\ (p, u) -> show u ++ " " ++ show p) newPats'))
                   return (map snd newPats')

data MergeState = MS { namemap :: [(Name, Name)],
                       invented :: [(Name, Name)],
                       explicit :: [Name],
                       updates :: [(Name, PTerm)] }

addUpdate n tm = do ms <- get
                    put (ms { updates = ((n, stripNS tm) : updates ms) } )

inventName ist ty n = 
    do ms <- get
       let supp = case ty of
                       Nothing -> []
                       Just t -> getNameHints ist t
       let nsupp = case n of
                        MN i n | not (tnull n) && thead n == '_'
                               -> mkSupply (supp ++ varlist)
                        MN i n -> mkSupply (UN n : supp ++ varlist)
                        UN n | thead n == '_'
                               -> mkSupply (supp ++ varlist)
                        x -> mkSupply (x : supp)
       let badnames = map snd (namemap ms) ++ map snd (invented ms) ++
                      explicit ms
       case lookup n (invented ms) of
          Just n' -> return n'
          Nothing ->
             do let n' = uniqueNameFrom nsupp badnames
                put (ms { invented = (n, n') : invented ms })
                return n'
                
mkSupply ns = mkSupply' ns (map nextName ns)
  where mkSupply' xs ns' = xs ++ mkSupply ns'
   
varlist = map (sUN . (:[])) "xyzwstuv" -- EB's personal preference :)

stripNS tm = mapPT dens tm where
    dens (PRef fc n) = PRef fc (nsroot n)
    dens t = t

mergeAllPats :: IState -> Name -> PTerm -> [PTerm] -> [(PTerm, [(Name, PTerm)])]
mergeAllPats ist cv t [] = []
mergeAllPats ist cv t (p : ps)
    = let (p', MS _ _ _ u) = runState (mergePat ist t p Nothing) 
                                      (MS [] [] (filter (/=cv) (patvars t)) [])
          ps' = mergeAllPats ist cv t ps in
          ((p', u) : ps')
  where patvars (PRef _ n) = [n]
        patvars (PApp _ _ as) = concatMap (patvars . getTm) as
        patvars (PPatvar _ n) = [n]
        patvars _ = []

mergePat :: IState -> PTerm -> PTerm -> Maybe Name -> State MergeState PTerm
-- If any names are unified, make sure they stay unified. Always prefer
-- user provided name (first pattern)
mergePat ist (PPatvar fc n) new t
  = mergePat ist (PRef fc n) new t
mergePat ist old (PPatvar fc n) t
  = mergePat ist old (PRef fc n) t
mergePat ist orig@(PRef fc n) new@(PRef _ n') t
  | isDConName n' (tt_ctxt ist) = do addUpdate n new
                                     return new
  | otherwise
    = do ms <- get
         case lookup n' (namemap ms) of
              Just x -> do addUpdate n (PRef fc x)
                           return (PRef fc x)
              Nothing -> do put (ms { namemap = ((n', n) : namemap ms) })
                            return (PRef fc n)
mergePat ist (PApp _ _ args) (PApp fc f args') t
      = do newArgs <- zipWithM mergeArg args (zip args' (argTys ist f))
           return (PApp fc f newArgs)
   where mergeArg x (y, t)
              = do tm' <- mergePat ist (getTm x) (getTm y) t
                   case x of
                        (PImp _ _ _ _ _) ->
                             return (y { machine_inf = machine_inf x,
                                         getTm = tm' })
                        _ -> return (y { getTm = tm' })
mergePat ist (PRef fc n) tm ty = do tm <- tidy ist tm ty
                                    addUpdate n tm
                                    return tm
mergePat ist x y t = return y

mergeUserImpl :: PTerm -> PTerm -> PTerm
mergeUserImpl x y = x

argTys :: IState -> PTerm -> [Maybe Name]
argTys ist (PRef fc n) 
    = case lookupTy n (tt_ctxt ist) of
           [ty] -> map (tyName . snd) (getArgTys ty) ++ repeat Nothing
           _ -> repeat Nothing
  where tyName (Bind _ (Pi _) _) = Just (sUN "->")
        tyName t | (P _ n _, _) <- unApply t = Just n
                 | otherwise = Nothing
argTys _ _ = repeat Nothing

tidy :: IState -> PTerm -> Maybe Name -> State MergeState PTerm
tidy ist orig@(PRef fc n) ty
     = do ms <- get
          case lookup n (namemap ms) of
               Just x -> return (PRef fc x)
               Nothing -> case n of
                               (UN _) -> return orig
                               _ -> do n' <- inventName ist ty n
                                       return (PRef fc n')
tidy ist (PApp fc f args) ty
     = do args' <- zipWithM tidyArg args (argTys ist f)
          return (PApp fc f args')
    where tidyArg x ty' = do tm' <- tidy ist (getTm x) ty'
                             return (x { getTm = tm' })
tidy ist tm ty = return tm


-- mapPT tidyVar tm
--   where tidyVar (PRef _ _) = Placeholder
--         tidyVar t = t

elabNewPat :: PTerm -> Idris (Maybe PTerm)
elabNewPat t = idrisCatch (do (tm, ty) <- elabVal toplevel True t
                              i <- getIState
                              return (Just (delab i tm)))
                          (\e -> do i <- getIState
                                    logLvl 5 $ "Not a valid split:\n" ++ pshow i e
                                    return Nothing)

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
        subst (PApp fc (PRef _ t) pats) 
            | isTConName t ctxt = Placeholder -- infer types
        subst (PApp fc f pats) = PApp fc f (map substArg pats)
        subst (PEq fc l r) = Placeholder -- PEq fc (subst l) (subst r)
        subst x = x

        substArg arg = arg { getTm = subst (getTm arg) }

replaceVar ctxt n t pat = pat

splitOnLine :: Int         -- ^ line number
            -> Name        -- ^ variable
            -> FilePath    -- ^ name of file
            -> Idris [[(Name, PTerm)]]
splitOnLine l n fn = do
--     let (before, later) = splitAt (l-1) (lines inp)
--     i <- getIState
    cl <- getInternalApp fn l
    logLvl 3 ("Working with " ++ showTmImpls cl)
    tms <- split n cl
--     iputStrLn (showSep "\n" (map show tms))
    return tms -- "" -- not yet done...

replaceSplits :: String -> [[(Name, PTerm)]] -> Idris [String]
replaceSplits l ups = updateRHSs 1 (map (rep (expandBraces l)) ups)
  where
    rep str [] = str ++ "\n"
    rep str ((n, tm) : ups) = rep (updatePat False (show n) (nshow tm) str) ups

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
    nshow (PRef _ (UN z)) | z == txt "Z" = "Z"
    nshow (PApp _ (PRef _ (UN s)) [x]) | s == txt "S" =
               "S " ++ addBrackets (nshow (getTm x))
    nshow t = show t

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
              if (before == n && not (isAlphaNum next))
                 then addBrackets tm ++ updatePat False n tm after
                 else c : updatePat (not (isAlphaNum c)) n tm rest
    updatePat start n tm (c:rest) = c : updatePat (not ((isAlphaNum c) || c == '_')) n tm rest

    addBrackets tm | ' ' `elem` tm
                   , not (isPrefixOf "(" tm)
                   , not (isSuffixOf ")" tm) = "(" ++ tm ++ ")"
                   | otherwise = tm

getUniq nm i
       = do ist <- getIState
            let n = nameRoot [] nm ++ "_" ++ show i
            case lookupTy (sUN n) (tt_ctxt ist) of
                 [] -> return (n, i+1)
                 _ -> getUniq nm (i+1)

nameRoot acc nm | all isDigit nm = showSep "_" acc
nameRoot acc nm =
        case span (/='_') nm of
             (before, ('_' : after)) -> nameRoot (acc ++ [before]) after
             _ -> showSep "_" (acc ++ [nm])

getClause :: Int      -- ^ line number that the type is declared on
          -> Name     -- ^ Function name
          -> FilePath -- ^ Source file name
          -> Idris String
getClause l fn fp 
    = do i <- getIState
         case lookupCtxt fn (idris_classes i) of
              [c] -> return (mkClassBodies i (class_methods c))
              _ -> do ty <- getInternalApp fp l
                      ist <- get
                      let ap = mkApp ist ty []
                      return (show fn ++ " " ++ ap ++ "= ?" 
                                      ++ show fn ++ "_rhs")
   where mkApp :: IState -> PTerm -> [Name] -> String
         mkApp i (PPi (Exp _ _ False) (MN _ _) ty sc) used
               = let n = getNameFrom i used ty in
                     show n ++ " " ++ mkApp i sc (n : used) 
         mkApp i (PPi (Exp _ _ False) (UN n) ty sc) used
            | thead n == '_'
               = let n = getNameFrom i used ty in
                     show n ++ " " ++ mkApp i sc (n : used) 
         mkApp i (PPi (Exp _ _ False) n _ sc) used 
               = show n ++ " " ++ mkApp i sc (n : used) 
         mkApp i (PPi _ _ _ sc) used = mkApp i sc used
         mkApp i _ _ = ""

         getNameFrom i used (PPi _ _ _ _) 
              = uniqueNameFrom (mkSupply [sUN "f", sUN "g"]) used
         getNameFrom i used (PApp fc f as) = getNameFrom i used f
         getNameFrom i used (PEq _ _ _) = uniqueNameFrom [sUN "prf"] used 
         getNameFrom i used (PRef fc f) 
            = case getNameHints i f of
                   [] -> uniqueName (sUN "x") used
                   ns -> uniqueNameFrom (mkSupply ns) used
         getNameFrom i used _ = uniqueName (sUN "x") used 

         -- write method declarations, indent with 4 spaces
         mkClassBodies :: IState -> [(Name, (FnOpts, PTerm))] -> String
         mkClassBodies i ns 
             = showSep "\n"
                  (zipWith (\(n, (_, ty)) m -> "    " ++ 
                            def (show (nsroot n)) ++ " "
                                 ++ mkApp i ty []
                                 ++ "= ?" 
                                 ++ show fn ++ "_rhs_" ++ show m) ns [1..])

         def n@(x:xs) | not (isAlphaNum x) = "(" ++ n ++ ")"
         def n = n

getProofClause :: Int      -- ^ line number that the type is declared
               -> Name     -- ^ Function name
               -> FilePath -- ^ Source file name
               -> Idris String
getProofClause l fn fp
                  = do ty <- getInternalApp fp l
                       return (mkApp ty ++ " = ?" ++ show fn ++ "_rhs")
   where mkApp (PPi _ _ _ sc) = mkApp sc
         mkApp rt = "(" ++ show rt ++ ") <== " ++ show fn

-- Purely syntactic - turn a pattern match clause into a with and a new
-- match clause

mkWith :: String -> Name -> String
mkWith str n = let str' = replaceRHS str "with (_)"
               in str' ++ "\n" ++ newpat str

   where replaceRHS [] str = str
         replaceRHS ('?':'=': rest) str = str
         replaceRHS ('=': rest) str
              | not ('=' `elem` rest) = str
         replaceRHS (x : rest) str = x : replaceRHS rest str

         newpat ('>':patstr) = '>':newpat patstr
         newpat patstr =
           "  " ++
           replaceRHS patstr "| with_pat = ?" ++ show n ++ "_rhs"

-- Replace _ with names in missing clauses

nameMissing :: [PTerm] -> Idris [PTerm]
nameMissing ps = do ist <- get
                    newPats <- mapM nm ps
                    let newPats' = mergeAllPats ist (sUN "_") (base (head ps))
                                                newPats
                    return (map fst newPats')
  where
    base (PApp fc f args) = PApp fc f (map (fmap (const (PRef fc (sUN "_")))) args)
    base t = t

    nm ptm = do mptm <- elabNewPat ptm
                case mptm of
                     Nothing -> return ptm
                     Just ptm' -> return ptm'
                       




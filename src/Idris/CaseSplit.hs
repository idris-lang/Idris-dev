{-|
Module      : Idris.CaseSplit
Description : Module to provide case split functionality.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.

Given a pattern clause and a variable 'n', elaborate the clause and find the
type of 'n'.

Make new pattern clauses by replacing 'n' with all the possibly constructors
applied to '_', and replacing all other variables with '_' in order to
resolve other dependencies.

Finally, merge the generated patterns with the original, by matching.
Always take the "more specific" argument when there is a discrepancy, i.e.
names over '_', patterns over names, etc.
-}

{-# LANGUAGE PatternGuards #-}

module Idris.CaseSplit(
    splitOnLine, replaceSplits
  , getClause, getProofClause
  , mkWith
  , nameMissing
  , getUniq, nameRoot
  ) where

import Idris.AbsSyntax
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate
import Idris.Elab.Term
import Idris.Elab.Value
import Idris.ElabDecls
import Idris.Error
import Idris.Output
import Idris.Parser

import Control.Monad
import Control.Monad.State.Strict
import Data.Char
import Data.List (isPrefixOf, isSuffixOf)

-- | Given a variable to split, and a term application, return a list
-- of variable updates, paired with a flag to say whether the given
-- update typechecks (False = impossible) if the flag is 'False' the
-- splits should be output with the 'impossible' flag, otherwise they
-- should be output as normal
split :: Name -> PTerm -> Idris (Bool, [[(Name, PTerm)]])
split n t'
   = do ist <- getIState
        -- Make sure all the names in the term are accessible
        mapM_ (\n -> setAccessibility n Public) (allNamesIn t')
        -- ETyDecl rather then ELHS because there'll be explicit type
        -- matching
        (tm, ty, pats) <- elabValBind (recinfo (fileFC "casesplit")) ETyDecl True (addImplPat ist t')
        -- ASSUMPTION: tm is in normal form after elabValBind, so we don't
        -- need to do anything special to find out what family each argument
        -- is in
        logElab 4 ("Elaborated:\n" ++ show tm ++ " : " ++ show ty ++ "\n" ++ show pats)
--         iputStrLn (show (delab ist tm) ++ " : " ++ show (delab ist ty))
--         iputStrLn (show pats)
        let t = mergeUserImpl (addImplPat ist t') (delabDirect ist tm)
        let ctxt = tt_ctxt ist
        case lookup n pats of
             Nothing -> ifail $ show n ++ " is not a pattern variable"
             Just ty ->
                do let splits = findPats ist ty
                   logElab 1 ("New patterns " ++ showSep ", "
                         (map showTmImpls splits))
                   let newPats_in = zipWith (replaceVar ctxt n) splits (repeat t)
                   logElab 4 ("Working from " ++ showTmImpls t)
                   logElab 4 ("Trying " ++ showSep "\n"
                               (map (showTmImpls) newPats_in))
                   newPats_in <- mapM elabNewPat newPats_in
                   case anyValid [] [] newPats_in of
                        Left fails -> do
                           let fails' = mergeAllPats ist n t fails
                           return (False, (map snd fails'))
                        Right newPats -> do
                           logElab 3 ("Original:\n" ++ show t)
                           logElab 3 ("Split:\n" ++
                                      (showSep "\n" (map show newPats)))
                           logElab 3 "----"
                           let newPats' = mergeAllPats ist n t newPats
                           logElab 1 ("Name updates " ++ showSep "\n"
                                 (map (\ (p, u) -> show u ++ " " ++ show p) newPats'))
                           return (True, (map snd newPats'))
   where
     anyValid ok bad [] = if null ok then Left (reverse bad)
                                     else Right (reverse ok)
     anyValid ok bad ((tc, p) : ps)
         | tc = anyValid (p : ok) bad ps
         | otherwise = anyValid ok (p : bad) ps

data MergeState = MS { namemap :: [(Name, Name)],
                       invented :: [(Name, Name)],
                       explicit :: [Name],
                       updates :: [(Name, PTerm)] }

addUpdate :: Name -> PTerm -> State MergeState ()
addUpdate n tm = do ms <- get
                    put (ms { updates = ((n, stripNS tm) : updates ms) } )

inventName :: IState -> Maybe Name -> Name -> State MergeState Name
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

mkSupply :: [Name] -> [Name]
mkSupply ns = mkSupply' ns (map nextName ns)
  where mkSupply' xs ns' = xs ++ mkSupply ns'

varlist :: [Name]
varlist = map (sUN . (:[])) "xyzwstuv" -- EB's personal preference :)

stripNS :: PTerm -> PTerm
stripNS tm = mapPT dens tm where
    dens (PRef fc hls n) = PRef fc hls (nsroot n)
    dens t = t

mergeAllPats :: IState -> Name -> PTerm -> [PTerm] -> [(PTerm, [(Name, PTerm)])]
mergeAllPats ist cv t [] = []
mergeAllPats ist cv t (p : ps)
    = let (p', MS _ _ _ u) = runState (mergePat ist t p Nothing)
                                      (MS [] [] (filter (/=cv) (patvars t)) [])
          ps' = mergeAllPats ist cv t ps in
          ((p', u) : ps')
  where patvars (PRef _ _ n) = [n]
        patvars (PApp _ _ as) = concatMap (patvars . getTm) as
        patvars (PPatvar _ n) = [n]
        patvars _ = []

mergePat :: IState -> PTerm -> PTerm -> Maybe Name -> State MergeState PTerm
mergePat ist orig new t =
    do -- collect user names for name map, by matching user pattern against
       -- the generated pattern
       case matchClause ist orig new of
            Left _ -> return ()
            Right ns -> mapM_ addNameMap ns
       mergePat' ist orig new t
  where
    addNameMap (n, PRef fc _ n') = do ms <- get
                                      put (ms { namemap = ((n', n) : namemap ms) })
    addNameMap _ = return ()

-- | If any names are unified, make sure they stay unified. Always
-- prefer user provided name (first pattern)
mergePat' ist (PPatvar fc n) new t
  = mergePat' ist (PRef fc [] n) new t
mergePat' ist old (PPatvar fc n) t
  = mergePat' ist old (PRef fc [] n) t
mergePat' ist orig@(PRef fc _ n) new@(PRef _ _ n') t
  | isDConName n' (tt_ctxt ist) = do addUpdate n new
                                     return new
  | otherwise
    = do ms <- get
         case lookup n' (namemap ms) of
              Just x -> do addUpdate n (PRef fc [] x)
                           return (PRef fc [] x)
              Nothing -> do put (ms { namemap = ((n', n) : namemap ms) })
                            return (PRef fc [] n)
mergePat' ist (PApp _ _ args) (PApp fc f args') t
      = do newArgs <- zipWithM mergeArg args (zip args' (argTys ist f))
           return (PApp fc f newArgs)
   where mergeArg x (y, t)
              = do tm' <- mergePat' ist (getTm x) (getTm y) t
                   case x of
                        (PImp _ _ _ _ _) ->
                             return (y { machine_inf = machine_inf x,
                                         getTm = tm' })
                        _ -> return (y { getTm = tm' })
mergePat' ist (PRef fc _ n) tm ty = do tm <- tidy ist tm ty
                                       addUpdate n tm
                                       return tm
mergePat' ist x y t = return y

mergeUserImpl :: PTerm -> PTerm -> PTerm
mergeUserImpl x y = x

argTys :: IState -> PTerm -> [Maybe Name]
argTys ist (PRef fc hls n)
    = case lookupTy n (tt_ctxt ist) of
           [ty] -> let ty' = normalise (tt_ctxt ist) [] ty in
                       map (tyName . snd) (getArgTys ty') ++ repeat Nothing
           _ -> repeat Nothing
  where tyName (Bind _ (Pi _ _ _ _) _) = Just (sUN "->")
        tyName t | (P _ d _, [_, ty]) <- unApply t,
                   d == sUN "Delayed" = tyName ty
                 | (P _ n _, _) <- unApply t = Just n
                 | otherwise = Nothing
argTys _ _ = repeat Nothing

tidy :: IState -> PTerm -> Maybe Name -> State MergeState PTerm
tidy ist orig@(PRef fc hls n) ty
     = do ms <- get
          case lookup n (namemap ms) of
               Just x -> return (PRef fc [] x)
               Nothing -> case n of
                               (UN _) -> return orig
                               _ -> do n' <- inventName ist ty n
                                       return (PRef fc [] n')
tidy ist (PApp fc f args) ty
     = do args' <- zipWithM tidyArg args (argTys ist f)
          return (PApp fc f args')
    where tidyArg x ty' = do tm' <- tidy ist (getTm x) ty'
                             return (x { getTm = tm' })
tidy ist tm ty = return tm


-- mapPT tidyVar tm
--   where tidyVar (PRef _ _) = Placeholder
--         tidyVar t = t

elabNewPat :: PTerm -> Idris (Bool, PTerm)
elabNewPat t = idrisCatch (do (tm, ty) <- elabVal (recinfo (fileFC "casesplit")) ELHS t
                              i <- getIState
                              return (True, delabDirect i tm))
                          (\e -> do i <- getIState
                                    logElab 5 $ "Not a valid split:\n" ++ showTmImpls t ++ "\n"
                                                     ++ pshow i e
                                    return (False, t))

findPats :: IState -> Type -> [PTerm]
findPats ist t | (P _ n _, _) <- unApply t
    = case lookupCtxt n (idris_datatypes ist) of
           [ti] -> map genPat (con_names ti)
           _ -> [Placeholder]
    where genPat n = case lookupCtxt n (idris_implicits ist) of
                        [args] -> PApp emptyFC (PRef emptyFC [] n)
                                         (map toPlaceholder args)
                        _ -> error $ "Can't happen (genPat) " ++ show n
          toPlaceholder tm = tm { getTm = Placeholder }
findPats ist t = [Placeholder]

replaceVar :: Context -> Name -> PTerm -> PTerm -> PTerm
replaceVar ctxt n t (PApp fc f pats) = PApp fc f (map substArg pats)
  where subst :: PTerm -> PTerm
        subst orig@(PPatvar _ v) | v == n = t
                                 | otherwise = Placeholder
        subst orig@(PRef _ _ v) | v == n = t
                                | isDConName v ctxt = orig
        subst (PRef _ _ _) = Placeholder
        subst (PApp fc (PRef _ _ t) pats)
            | isTConName t ctxt = Placeholder -- infer types
        subst (PApp fc f pats) = PApp fc f (map substArg pats)
        subst x = x

        substArg arg = arg { getTm = subst (getTm arg) }

replaceVar ctxt n t pat = pat

splitOnLine :: Int         -- ^ line number
            -> Name        -- ^ variable
            -> FilePath    -- ^ name of file
            -> Idris (Bool, [[(Name, PTerm)]])
splitOnLine l n fn = do
    cl <- getInternalApp fn l
    logElab 3 ("Working with " ++ showTmImpls cl)
    tms <- split n cl
    return tms

replaceSplits :: String -> [[(Name, PTerm)]] -> Bool -> Idris [String]
replaceSplits l ups impossible
    = do ist <- getIState
         updateRHSs 1 (map (rep ist (expandBraces l)) ups)
  where
    rep ist str [] = str ++ "\n"
    rep ist str ((n, tm) : ups)
        = rep ist (updatePat False (show n) (nshow (resugar ist tm)) str) ups

    updateRHSs i [] = return []
    updateRHSs i (x : xs)
       | impossible = do xs' <- updateRHSs i xs
                         return (setImpossible False x : xs')
       | otherwise = do (x', i') <- updateRHS (null xs) i x
                        xs' <- updateRHSs i' xs
                        return (x' : xs')

    updateRHS last i ('?':'=':xs) = do (xs', i') <- updateRHS last i xs
                                       return ("?=" ++ xs', i')
    updateRHS last i ('?':xs)
        = do let (nm, rest_in) = span (not . (\x -> isSpace x || x == ')'
                                                              || x == '(')) xs
             let rest = if last then rest_in else
                           case span (not . (=='\n')) rest_in of
                                (_, restnl) -> restnl
             (nm', i') <- getUniq nm i
             return ('?':nm' ++ rest, i')
    updateRHS last i (x : xs) = do (xs', i') <- updateRHS last i xs
                                   return (x : xs', i')
    updateRHS last i [] = return ("", i)

    setImpossible brace ('}':xs) = '}' : setImpossible False xs
    setImpossible brace ('{':xs) = '{' : setImpossible True xs
    setImpossible False ('=':xs) = "impossible\n"
    setImpossible brace (x : xs) = x : setImpossible brace xs
    setImpossible brace [] = ""

    -- TMP HACK: If there are Nats, we don't want to show as numerals since
    -- this isn't supported in a pattern, so special case here
    nshow (PRef _ _ (UN z)) | z == txt "Z" = "Z"
    nshow (PApp _ (PRef _ _ (UN s)) [x]) | s == txt "S" =
               "(S " ++ addBrackets (nshow (getTm x)) ++ ")"
    nshow t = show t

    -- if there's any {n} replace with {n=n}
    -- but don't replace it in comments
    expandBraces ('{' : '-' : xs) = '{' : '-' : xs
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
    updatePat start n tm done@('?':rest) = done
    updatePat True n tm xs@(c:rest) | length xs > length n
        = let (before, after@(next:_)) = splitAt (length n) xs in
              if (before == n && not (isAlphaNum next))
                 then addBrackets tm ++ updatePat False n tm after
                 else c : updatePat (not (isAlphaNum c)) n tm rest
    updatePat start n tm (c:rest) = c : updatePat (not ((isAlphaNum c) || c == '_')) n tm rest

    addBrackets tm | ' ' `elem` tm
                   , not (isPrefixOf "(" tm && isSuffixOf ")" tm)
                       = "(" ++ tm ++ ")"
                   | otherwise = tm


getUniq :: (Show t, Num t) => [Char] -> t -> Idris ([Char], t)
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

-- Show a name for use in pattern definitions on the lhs
showLHSName :: Name -> String
showLHSName n = let fn = show n in
                    if any (flip elem opChars) fn
                       then "(" ++ fn ++ ")"
                       else fn

-- Show a name for the purpose of generating a metavariable name on the rhs
showRHSName :: Name -> String
showRHSName n = let fn = show n in
                    if any (flip elem opChars) fn
                       then "op"
                       else fn

getClause :: Int      -- ^ line number that the type is declared on
          -> Name     -- ^ Function name
          -> Name     -- ^ User given name
          -> FilePath -- ^ Source file name
          -> Idris String
getClause l _ un fp
    = do i <- getIState
         indentClause <- getIndentClause
--         runIO . traceIO $ "indentClause = " ++ show indentClause
         case lookupCtxt un (idris_interfaces i) of
              [c] -> return (mkInterfaceBodies indentClause i (interface_methods c))
              _ -> do ty_in <- getInternalApp fp l
                      let ty = case ty_in of
                                    PTyped _ t -> t
                                    x -> x
                      ist <- get
                      let app = mkApp ist ty []
                      return (showLHSName un ++ " " ++ app ++ "= ?"
                                      ++ showRHSName un ++ "_rhs")
   where mkApp :: IState -> PTerm -> [Name] -> String
         mkApp i (PPi (Exp _ _ False _) (MN _ _) _ ty sc) used
               = let n = getNameFrom i used ty in
                     show n ++ " " ++ mkApp i sc (n : used)
         mkApp i (PPi (Exp _ _ False _) (UN n) _ ty sc) used
            | thead n == '_'
               = let n = getNameFrom i used ty in
                     show n ++ " " ++ mkApp i sc (n : used)
         mkApp i (PPi (Exp _ _ False _) n _ _ sc) used
               = show n ++ " " ++ mkApp i sc (n : used)
         mkApp i (PPi _ _ _ _ sc) used = mkApp i sc used
         mkApp i _ _ = ""

         getNameFrom i used (PPi _ _ _ _ _)
              = uniqueNameFrom (mkSupply [sUN "f", sUN "g"]) used
         getNameFrom i used (PApp fc f as) = getNameFrom i used f
         getNameFrom i used (PRef fc _ f)
            = case getNameHints i f of
                   [] -> uniqueNameFrom (mkSupply [sUN "x", sUN "y",
                                                   sUN "z"]) used
                   ns -> uniqueNameFrom (mkSupply ns) used
         getNameFrom i used _ = uniqueNameFrom (mkSupply [sUN "x", sUN "y",
                                                          sUN "z"]) used

         -- write method declarations, indent with `indent` spaces.
         mkInterfaceBodies :: Int -> IState -> [(Name, (Bool, FnOpts, PTerm))] -> String
         mkInterfaceBodies indent i ns
             = showSep "\n"
                  (zipWith (\(n, (_, _, ty)) m -> replicate indent ' ' ++
                            def (show (nsroot n)) ++ " "
                                 ++ mkApp i ty []
                                 ++ "= ?"
                                 ++ showRHSName un ++ "_rhs_" ++ show m) ns [1..])

         def n@(x:xs) | not (isAlphaNum x) = "(" ++ n ++ ")"
         def n = n

getProofClause :: Int      -- ^ line number that the type is declared
               -> Name     -- ^ Function name
               -> FilePath -- ^ Source file name
               -> Idris String
getProofClause l fn fp
                  = do ty_in <- getInternalApp fp l
                       let ty = case ty_in of
                                     PTyped n t -> t
                                     x -> x
                       return (mkApp ty ++ " = ?" ++ showRHSName fn ++ "_rhs")
   where mkApp (PPi _ _ _ _ sc) = mkApp sc
         mkApp rt = "(" ++ show rt ++ ") <== " ++ show fn

-- Purely syntactic - turn a pattern match clause into a with and a new
-- match clause

mkWith :: String -> Name -> Int -> String
mkWith str n indent = let str' = replaceRHS str "with (_)"
                      in str' ++ "\n" ++ newpat str

   where replaceRHS [] str = str
         replaceRHS ('?':'=': rest) str = str
         replaceRHS ('=': rest) str
              | not ('=' `elem` rest) = str
         replaceRHS (x : rest) str = x : replaceRHS rest str

         newpat ('>':patstr) = '>':newpat patstr
         newpat patstr = replicate indent ' ' ++
           replaceRHS patstr "| with_pat = ?" ++ showRHSName n ++ "_rhs"

-- Replace _ with names in missing clauses

nameMissing :: [PTerm] -> Idris [PTerm]
nameMissing ps = do ist <- get
                    newPats <- mapM nm ps
                    let newPats' = mergeAllPats ist (sUN "_") (base (head ps))
                                                newPats
                    return (map fst newPats')
  where
    base (PApp fc f args) = PApp fc f (map (fmap (const (PRef fc [] (sUN "_")))) args)
    base t = t

    nm ptm = do mptm <- elabNewPat ptm
                case mptm of
                     (False, _) -> return ptm
                     (True, ptm') -> return ptm'

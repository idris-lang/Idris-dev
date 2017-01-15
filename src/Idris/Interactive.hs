{-|
Module      : Idris.Interactive
Description : Bits and pieces for editing source files interactively, called from the REPL
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE PatternGuards #-}

module Idris.Interactive(
    caseSplitAt, addClauseFrom, addProofClauseFrom
  , addMissing, makeWith, makeCase, doProofSearch
  , makeLemma
  ) where

import Idris.AbsSyntax
import Idris.CaseSplit
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate
import Idris.Elab.Term
import Idris.Elab.Value
import Idris.ElabDecls
import Idris.Error
import Idris.ErrReverse
import Idris.IdeMode hiding (IdeModeCommand(..))
import Idris.Output

import Util.Pretty
import Util.System

import Data.Char
import Data.List (isSuffixOf)
import System.Directory
import System.IO

caseSplitAt :: FilePath -> Bool -> Int -> Name -> Idris ()
caseSplitAt fn updatefile l n
   = do src <- runIO $ readSource fn
        (ok, res) <- splitOnLine l n fn
        logLvl 1 (showSep "\n" (map show res))
        let (before, (ap : later)) = splitAt (l-1) (lines src)
        res' <- replaceSplits ap res (not ok)
        let new = concat res'
        if updatefile
          then do let fb = fn ++ "~" -- make a backup!
                  runIO $ writeSource fb (unlines before ++ new ++ unlines later)
                  runIO $ copyFile fb fn
          else -- do iputStrLn (show res)
            iPrintResult new

addClauseFrom :: FilePath -> Bool -> Int -> Name -> Idris ()
addClauseFrom fn updatefile l n = do
    -- if a definition already exists, add missing cases rather than
    -- adding a new definition.
    ist <- getIState
    cl <- getInternalApp fn l
    let fulln = getAppName cl
    let metavars = lookup fulln (idris_metavars ist)
    case metavars of
      Nothing -> addMissing fn updatefile l n
      Just _ -> do
        src <- runIO $ readSource fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getClause l fulln n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeSource fb (unlines (before ++ nonblank) ++
                                        replicate indent ' ' ++
                                        cl ++ "\n" ++
                                        unlines rest)
                  runIO $ copyFile fb fn
          else iPrintResult cl
  where
    getIndent i n [] = 0
    getIndent i n xs | take 9 xs == "implementation " = i
    getIndent i n xs | take (length n) xs == n = i
    getIndent i n (x : xs) = getIndent (i + 1) n xs

    getAppName (PApp _ r _) = getAppName r
    getAppName (PRef _ _ r) = r
    getAppName (PTyped n _) = getAppName n
    getAppName _ = n

addProofClauseFrom :: FilePath -> Bool -> Int -> Name -> Idris ()
addProofClauseFrom fn updatefile l n
   = do src <- runIO $ readSource fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getProofClause l n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeSource fb (unlines (before ++ nonblank) ++
                                        replicate indent ' ' ++
                                        cl ++ "\n" ++
                                        unlines rest)
                  runIO $ copyFile fb fn
          else iPrintResult cl
    where
       getIndent i n [] = 0
       getIndent i n xs | take (length n) xs == n = i
       getIndent i n (x : xs) = getIndent (i + 1) n xs

addMissing :: FilePath -> Bool -> Int -> Name -> Idris ()
addMissing fn updatefile l n
   = do src <- runIO $ readSource fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        i <- getIState
        cl <- getInternalApp fn l
        let n' = getAppName cl

        extras <- case lookupCtxtExact n' (idris_patdefs i) of
                       Nothing -> return ""
                       Just (_, tms) -> do tms' <- nameMissing tms
                                           showNew (show n ++ "_rhs") 1 indent tms'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeSource fb (unlines (before ++ nonblank)
                                        ++ extras ++
                                           (if null extras then ""
                                                    else "\n" ++ unlines rest))
                  runIO $ copyFile fb fn
          else iPrintResult extras
    where showPat = show . stripNS
          stripNS tm = mapPT dens tm where
              dens (PRef fc hls n) = PRef fc hls (nsroot n)
              dens t = t

          nsroot (NS n _) = nsroot n
          nsroot (SN (WhereN _ _ n)) = nsroot n
          nsroot n = n

          getAppName (PApp _ r _) = getAppName r
          getAppName (PRef _ _ r) = r
          getAppName (PTyped n _) = getAppName n
          getAppName _ = n

          makeIndent ind | ".lidr" `isSuffixOf` fn = '>' : ' ' : replicate (ind-2) ' '
                         | otherwise               = replicate ind ' '

          showNew nm i ind (tm : tms)
                        = do (nm', i') <- getUniq nm i
                             rest <- showNew nm i' ind tms
                             return (makeIndent ind ++
                                     showPat tm ++ " = ?" ++ nm' ++
                                     (if null rest then "" else
                                         "\n" ++ rest))
          showNew nm i _ [] = return ""

          getIndent i n [] = 0
          getIndent i n xs | take (length n) xs == n = i
          getIndent i n (x : xs) = getIndent (i + 1) n xs


makeWith :: FilePath -> Bool -> Int -> Name -> Idris ()
makeWith fn updatefile l n = do
  src <- runIO $ readSource fn
  i <- getIState
  indentWith <- getIndentWith
  let (before, tyline : later) = splitAt (l-1) (lines src)
  let ind = getIndent tyline
--  runIO . traceIO $ "indentWith = " ++ show indentWith
  let with = mkWith tyline n indentWith
  -- add clause before first blank line in 'later',
  -- or (TODO) before first line with same indentation as tyline
  let (nonblank, rest) = span (\x -> not (all isSpace x) &&
                                     not (ind == getIndent x)) later
  if updatefile
    then do
      let fb = fn ++ "~"
      runIO $ writeSource fb (unlines (before ++ nonblank) ++
                              with ++ "\n" ++ unlines rest)
      runIO $ copyFile fb fn
    else iPrintResult (with ++ "\n")
  where getIndent s = length (takeWhile isSpace s)

-- Replace the given metavariable on the given line with a 'case'
-- block, using a _ for the scrutinee
makeCase :: FilePath -> Bool -> Int -> Name -> Idris ()
makeCase fn updatefile l n
   = do src <- runIO $ readSource fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let newcase = addCaseSkel (show n) tyline

        if updatefile then
           do let fb = fn ++ "~"
              runIO $ writeSource fb (unlines (before ++ newcase ++ later))
              runIO $ copyFile fb fn
           else iPrintResult (showSep "\n" newcase ++"\n")
  where addCaseSkel n line =
            let b = brackets False line in
            case findSubstr ('?':n) line of
                 Just (before, pos, after) ->
                      [before ++ (if b then "(" else "") ++ "case _ of",
                       take (pos + (if b then 6 else 5)) (repeat ' ') ++
                             "case_val => ?" ++ n ++ (if b then ")" else "")
                             ++ after]
                 Nothing -> fail "No such metavariable"

        -- Assume case needs to be bracketed unless the metavariable is
        -- on its own after an =
        brackets eq line | line == '?' : show n = not eq
        brackets eq ('=':ls) = brackets True ls
        brackets eq (' ':ls) = brackets eq ls
        brackets eq (l : ls) = brackets False ls
        brackets eq [] = True

        findSubstr n xs = findSubstr' [] 0 n xs

        findSubstr' acc i n xs | take (length n) xs == n
                = Just (reverse acc, i, drop (length n) xs)
        findSubstr' acc i n [] = Nothing
        findSubstr' acc i n (x : xs) = findSubstr' (x : acc) (i + 1) n xs


doProofSearch :: FilePath -> Bool -> Bool ->
                 Int -> Name -> [Name] -> Maybe Int -> Idris ()
doProofSearch fn updatefile rec l n hints Nothing
    = doProofSearch fn updatefile rec l n hints (Just 20)
doProofSearch fn updatefile rec l n hints (Just depth)
    = do src <- runIO $ readSource fn
         let (before, tyline : later) = splitAt (l-1) (lines src)
         ctxt <- getContext
         mn <- case lookupNames n ctxt of
                    [x] -> return x
                    [] -> return n
                    ns -> ierror (CantResolveAlts ns)
         i <- getIState
         let (top, envlen, psnames)
              = case lookup mn (idris_metavars i) of
                     Just (t, e, ns, False, d) -> (t, e, ns)
                     _ -> (Nothing, 0, [])
         let fc = fileFC fn
         let body t = PProof [Try (TSeq Intros (ProofSearch rec False depth t psnames hints))
                                  (ProofSearch rec False depth t psnames hints)]
         let def = PClause fc mn (PRef fc [] mn) [] (body top) []
         newmv_pre <- idrisCatch
             (do elabDecl' EAll (recinfo (fileFC "proofsearch")) (PClauses fc [] mn [def])
                 (tm, ty) <- elabVal (recinfo (fileFC "proofsearch")) ERHS (PRef fc [] mn)
                 ctxt <- getContext
                 i <- getIState
                 return . flip displayS "" . renderPretty 1.0 80 $
                   pprintPTerm defaultPPOption [] [] (idris_infixes i)
                     (stripNS
                        (dropCtxt envlen
                           (delab i (fst (specialise ctxt [] [(mn, 1)] tm))))))
             (\e -> return ("?" ++ show n))
         let newmv = guessBrackets False tyline (show n) newmv_pre
         if updatefile then
            do let fb = fn ++ "~"
               runIO $ writeSource fb (unlines before ++
                                     updateMeta tyline (show n) newmv ++ "\n"
                                       ++ unlines later)
               runIO $ copyFile fb fn
            else iPrintResult newmv
    where dropCtxt 0 sc = sc
          dropCtxt i (PPi _ _ _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt i (PLet _ _ _ _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt i (PLam _ _ _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt _ t = t

          stripNS tm = mapPT dens tm where
              dens (PRef fc hls n) = PRef fc hls (nsroot n)
              dens t = t

          nsroot (NS n _) = nsroot n
          nsroot (SN (WhereN _ _ n)) = nsroot n
          nsroot n = n

updateMeta ('?':cs) n new
    | length cs >= length n
      = case splitAt (length n) cs of
             (mv, c:cs) ->
                  if ((isSpace c || c == ')' || c == '}') && mv == n)
                     then new ++ (c : cs)
                     else '?' : mv ++ c : updateMeta cs n new
             (mv, []) -> if (mv == n) then new else '?' : mv
updateMeta ('=':'>':cs) n new = '=':'>':updateMeta cs n new
updateMeta ('=':cs) n new = '=':updateMeta cs n new
updateMeta (c:cs) n new
  = c : updateMeta cs n new
updateMeta [] n new = ""

guessBrackets brack ('?':cs) n new
    | length cs >= length n
      = case splitAt (length n) cs of
             (mv, c:cs) ->
                  if ((isSpace c || c == ')' || c == '}') && mv == n)
                     then addBracket brack new
                     else guessBrackets True cs n new
             (mv, []) -> if (mv == n) then addBracket brack new else '?' : mv
guessBrackets brack ('=':'>':cs) n new = guessBrackets False cs n new
guessBrackets brack ('-':'>':cs) n new = guessBrackets False cs n new
guessBrackets brack ('=':cs) n new = guessBrackets False cs n new
guessBrackets brack (c:cs) n new
  = guessBrackets (brack || not (isSpace c)) cs n new
guessBrackets brack [] n new = ""

checkProv line n = isProv' False line n
  where
    isProv' p cs n | take (length n) cs == n = p
    isProv' _ ('?':cs) n = isProv' False cs n
    isProv' _ ('{':cs) n = isProv' True cs n
    isProv' _ ('}':cs) n = isProv' True cs n
    isProv' p (_:cs) n = isProv' p cs n
    isProv' _ [] n = False

addBracket False new = new
addBracket True new@('(':xs) | last xs == ')' = new
addBracket True new | any isSpace new = '(' : new ++ ")"
                    | otherwise = new


makeLemma :: FilePath -> Bool -> Int -> Name -> Idris ()
makeLemma fn updatefile l n
   = do src <- runIO $ readSource fn
        let (before, tyline : later) = splitAt (l-1) (lines src)

        -- if the name is in braces, rather than preceded by a ?, treat it
        -- as a lemma in a provisional definition

        let isProv = checkProv tyline (show n)

        ctxt <- getContext
        (fname, mty_full) <- case lookupTyName n ctxt of
                                  [t] -> return t
                                  [] -> ierror (NoSuchVariable n)
                                  ns -> ierror (CantResolveAlts (map fst ns))

        i <- getIState
        let mty = errReverse i mty_full

        margs <- case lookup fname (idris_metavars i) of
                      Just (_, arity, _, _, _) -> return arity
                      _ -> return (-1)

        if (not isProv) then do
            let skip = guessImps i (tt_ctxt i) mty
            let impty = stripMNBind skip margs (delab i mty)
            let interfaces = guessInterfaces i (tt_ctxt i) [] (allNamesIn impty) mty

            let lem = show n ++ " : " ++
                            constraints i interfaces mty ++
                            showTmOpts (defaultPPOption { ppopt_pinames = True })
                                       impty
            let lem_app = guessBrackets False tyline (show n) (show n ++ appArgs skip margs mty)

            if updatefile then
               do let fb = fn ++ "~"
                  runIO $ writeSource fb (addLem before tyline lem lem_app later)
                  runIO $ copyFile fb fn
               else case idris_outputmode i of
                      RawOutput _  -> iPrintResult $ lem ++ "\n" ++ lem_app
                      IdeMode n h ->
                        let good = SexpList [SymbolAtom "ok",
                                             SexpList [SymbolAtom "metavariable-lemma",
                                                       SexpList [SymbolAtom "replace-metavariable",
                                                                 StringAtom lem_app],
                                                       SexpList [SymbolAtom "definition-type",
                                                                 StringAtom lem]]]
                        in runIO . hPutStrLn h $ convSExp "return" good n

          else do -- provisional definition
            let lem_app = show n ++ appArgs [] (-1) mty ++
                                 " = ?" ++ show n ++ "_rhs"
            if updatefile then
               do let fb = fn ++ "~"
                  runIO $ writeSource fb (addProv before tyline lem_app later)
                  runIO $ copyFile fb fn
               else case idris_outputmode i of
                      RawOutput _  -> iPrintResult lem_app
                      IdeMode n h ->
                        let good = SexpList [SymbolAtom "ok",
                                             SexpList [SymbolAtom "provisional-definition-lemma",
                                                       SexpList [SymbolAtom "definition-clause",
                                                                 StringAtom lem_app]]]
                        in runIO . hPutStrLn h $ convSExp "return" good n

  where getIndent s = length (takeWhile isSpace s)

        appArgs skip 0 _ = ""
        appArgs skip i (Bind n@(UN c) (Pi _ _ _ _) sc)
           | (thead c /= '_' && n `notElem` skip)
                = " " ++ show n ++ appArgs skip (i - 1) sc
        appArgs skip i (Bind _ (Pi _ _ _ _) sc) = appArgs skip (i - 1) sc
        appArgs skip i _ = ""

        stripMNBind _ args t | args <= 0 = stripImp t
        stripMNBind skip args (PPi b n@(UN c) _ ty sc)
           | n `notElem` skip ||
               take 4 (str c) == "__pi" -- keep in type, but not in app
                = PPi b n NoFC (stripImp ty) (stripMNBind skip (args - 1) sc)
        stripMNBind skip args (PPi b _ _ ty sc) = stripMNBind skip (args - 1) sc
        stripMNBind skip args t = stripImp t

        stripImp (PApp fc f as) = PApp fc (stripImp f) (map placeholderImp as)
          where
            placeholderImp tm@(PImp _ _ _ _ _) = tm { getTm = Placeholder }
            placeholderImp tm = tm { getTm = stripImp (getTm tm) }
        stripImp (PPi b n f ty sc) = PPi b n f (stripImp ty) (stripImp sc)
        stripImp t = t

        constraints :: IState -> [Name] -> Type -> String
        constraints i [] ty = ""
        constraints i [n] ty = showSep ", " (showConstraints i [n] ty) ++ " => "
        constraints i ns ty = "(" ++ showSep ", " (showConstraints i ns ty) ++ ") => "

        showConstraints i ns (Bind n (Pi _ _ ty _) sc)
            | n `elem` ns = show (delab i ty) :
                              showConstraints i ns (substV (P Bound n Erased) sc)
            | otherwise = showConstraints i ns (substV (P Bound n Erased) sc)
        showConstraints _ _ _ = []

        -- Guess which binders should be implicits in the generated lemma.
        -- Make them implicit if they appear guarded by a top level constructor,
        -- or at the top level themselves.
        -- Also, make interface implementations implicit
        guessImps :: IState -> Context -> Term -> [Name]
        -- machine names aren't lifted
        guessImps ist ctxt (Bind n@(MN _ _) (Pi _ _ ty _) sc)
           = n : guessImps ist ctxt sc
        guessImps ist ctxt (Bind n (Pi _ _ ty _) sc)
           | guarded ctxt n (substV (P Bound n Erased) sc)
                = n : guessImps ist ctxt sc
           | isInterface ist ty
                = n : guessImps ist ctxt sc
           | paramty ty = n : guessImps ist ctxt sc
           | ignoreName n = n : guessImps ist ctxt sc
           | otherwise = guessImps ist ctxt sc
        guessImps ist ctxt _ = []

        paramty (TType _) = True
        paramty (Bind _ (Pi _ _ (TType _) _) sc) = paramty sc
        paramty _ = False

        -- TMP HACK unusable name so don't lift
        ignoreName n = case show n of
                            "_aX" -> True
                            _ -> False

        guessInterfaces :: IState -> Context -> [Name] -> [Name] -> Term -> [Name]
        guessInterfaces ist ctxt binders usednames (Bind n (Pi _ _ ty _) sc)
           | isParamInterface ist ty && any (\x -> elem x usednames)
                                            (paramNames binders ty)
                = n : guessInterfaces ist ctxt (n : binders) usednames sc
           | otherwise = guessInterfaces ist ctxt (n : binders) usednames sc
        guessInterfaces ist ctxt _ _ _ = []

        paramNames bs ty | (P _ _ _, args) <- unApply ty
             = vnames args
          where vnames [] = []
                vnames (V i : xs) | i < length bs = bs !! i : vnames xs
                vnames (_ : xs) = vnames xs

        isInterface ist t
           | (P _ n _, args) <- unApply t
                = case lookupCtxtExact n (idris_interfaces ist) of
                       Just _ -> True
                       _ -> False
           | otherwise = False

        isParamInterface ist t
           | (P _ n _, args) <- unApply t
                = case lookupCtxtExact n (idris_interfaces ist) of
                       Just _ -> any isV args
                       _ -> False
           | otherwise = False
          where isV (V _) = True
                isV _ = False

        guarded ctxt n (P _ n' _) | n == n' = True
        guarded ctxt n ap@(App _ _ _)
            | (P _ f _, args) <- unApply ap,
              isConName f ctxt = any (guarded ctxt n) args
--         guarded ctxt n (Bind (UN cn) (Pi t) sc) -- ignore shadows
--             | thead cn /= '_' = guarded ctxt n t || guarded ctxt n sc
        guarded ctxt n (Bind _ (Pi _ _ t _) sc)
            = guarded ctxt n t || guarded ctxt n sc
        guarded ctxt n _ = False

        blank = all isSpace

        addLem before tyline lem lem_app later
            = let (bef_end, blankline : bef_start)
                       = case span (not . blank) (reverse before) of
                              (bef, []) -> (bef, [""])
                              x -> x
                  mvline = updateMeta tyline (show n) lem_app in
                unlines $ reverse bef_start ++
                          [blankline, lem, blankline] ++
                          reverse bef_end ++ mvline : later

        addProv before tyline lem_app later
            = let (later_bef, blankline : later_end)
                      = case span (not . blank) later of
                             (bef, []) -> (bef, [""])
                             x -> x in
                  unlines $ before ++ tyline :
                            (later_bef ++ [blankline, lem_app, blankline] ++
                                      later_end)

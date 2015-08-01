{-# LANGUAGE PatternGuards #-}

module Idris.Interactive(caseSplitAt, addClauseFrom, addProofClauseFrom,
                         addMissing, makeWith, makeCase, doProofSearch,
                         makeLemma) where

{- Bits and pieces for editing source files interactively, called from
   the REPL -}

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.CaseSplit
import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.Error
import Idris.Delaborate
import Idris.Output
import Idris.IdeMode hiding (IdeModeCommand(..))
import Idris.Elab.Value
import Idris.Elab.Term

import Util.Pretty
import Util.System

import System.FilePath
import System.Directory
import System.IO
import Data.Char
import Data.Maybe (fromMaybe)
import Data.List (isSuffixOf)

import Debug.Trace

caseSplitAt :: FilePath -> Bool -> Int -> Name -> Idris ()
caseSplitAt fn updatefile l n
   = do src <- runIO $ readSource fn
        res <- splitOnLine l n fn
        logLvl 1 (showSep "\n" (map show res))
        let (before, (ap : later)) = splitAt (l-1) (lines src)
        res' <- replaceSplits ap res
        let new = concat res'
        if updatefile
          then do let fb = fn ++ "~" -- make a backup!
                  runIO $ writeSource fb (unlines before ++ new ++ unlines later)
                  runIO $ copyFile fb fn
          else -- do iputStrLn (show res)
            iPrintResult new

addClauseFrom :: FilePath -> Bool -> Int -> Name -> Idris ()
addClauseFrom fn updatefile l n
   = do src <- runIO $ readSource fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getClause l n fn
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
       getIndent i n xs | take 9 xs == "instance " = i
       getIndent i n xs | take (length n) xs == n = i
       getIndent i n (x : xs) = getIndent (i + 1) n xs

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

        extras <- case lookupCtxt n' (idris_patdefs i) of
                       [] -> return ""
                       [(_, tms)] -> do tms' <- nameMissing tms
                                        showNew (show n ++ "_rhs") 1 indent tms'
                       other -> return "" -- happens if called on a metavar, or with no clauses
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeSource fb (unlines (before ++ nonblank)
                                        ++ extras ++ unlines rest)
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
          getAppName _ = n

          makeIndent ind | ".lidr" `isSuffixOf` fn = '>' : ' ' : replicate (ind-2) ' '
                         | otherwise               = replicate ind ' '

          showNew nm i ind (tm : tms)
                        = do (nm', i') <- getUniq nm i
                             rest <- showNew nm i' ind tms
                             return (makeIndent ind ++
                                     showPat tm ++ " = ?" ++ nm' ++
                                     "\n" ++ rest)
          showNew nm i _ [] = return ""

          getIndent i n [] = 0
          getIndent i n xs | take (length n) xs == n = i
          getIndent i n (x : xs) = getIndent (i + 1) n xs


makeWith :: FilePath -> Bool -> Int -> Name -> Idris ()
makeWith fn updatefile l n
   = do src <- runIO $ readSource fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let ind = getIndent tyline
        let with = mkWith tyline n
        -- add clause before first blank line in 'later',
        -- or (TODO) before first line with same indentation as tyline
        let (nonblank, rest) = span (\x -> not (all isSpace x) &&
                                           not (ind == getIndent x)) later
        if updatefile then
           do let fb = fn ++ "~"
              runIO $ writeSource fb (unlines (before ++ nonblank)
                                        ++ with ++ "\n" ++
                                    unlines rest)
              runIO $ copyFile fb fn
           else iPrintResult with
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
           else iPrintResult (showSep "\n" newcase)
  where addCaseSkel n line =
            let b = brackets False line in
            case findSubstr ('?':n) line of
                 Just (before, pos, after) ->
                      [before ++ (if b then "(" else "") ++ "case _ of",
                       take (pos + (if b then 6 else 5)) (repeat ' ') ++ 
                             "case_val => ?" ++ n ++ if b then ")" else "",
                       after]
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
         let (top, envlen, psnames, _) 
              = case lookup mn (idris_metavars i) of
                     Just (t, e, ns, False) -> (t, e, ns, False)
                     _ -> (Nothing, 0, [], True)
         let fc = fileFC fn
         let body t = PProof [Try (TSeq Intros (ProofSearch rec False depth t psnames hints))
                                  (ProofSearch rec False depth t psnames hints)]
         let def = PClause fc mn (PRef fc [] mn) [] (body top) []
         newmv <- idrisCatch
             (do elabDecl' EAll recinfo (PClauses fc [] mn [def])
                 (tm, ty) <- elabVal recinfo ERHS (PRef fc [] mn)
                 ctxt <- getContext
                 i <- getIState
                 return . flip displayS "" . renderPretty 1.0 80 $
                   pprintPTerm defaultPPOption [] [] (idris_infixes i)
                     (stripNS
                        (dropCtxt envlen
                           (delab i (fst (specialise ctxt [] [(mn, 1)] tm))))))
             (\e -> return ("?" ++ show n))
         if updatefile then
            do let fb = fn ++ "~"
               runIO $ writeSource fb (unlines before ++
                                     updateMeta False tyline (show n) newmv ++ "\n"
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

updateMeta brack ('?':cs) n new
    | length cs >= length n
      = case splitAt (length n) cs of
             (mv, c:cs) ->
                  if ((isSpace c || c == ')' || c == '}') && mv == n)
                     then addBracket brack new ++ (c : cs)
                     else '?' : mv ++ c : updateMeta True cs n new
             (mv, []) -> if (mv == n) then addBracket brack new else '?' : mv
updateMeta brack ('=':cs) n new = '=':updateMeta False cs n new
updateMeta brack (c:cs) n new 
  = c : updateMeta (brack || not (isSpace c)) cs n new
updateMeta brack [] n new = ""

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
        mty <- case lookupTyName n ctxt of
                    [(_,t)] -> return t
                    [] -> ierror (NoSuchVariable n)
                    ns -> ierror (CantResolveAlts (map fst ns))
        i <- getIState
        margs <- case lookup n (idris_metavars i) of
                      Just (_, arity, _, _) -> return arity
                      _ -> return (-1)

        if (not isProv) then do
            let skip = guessImps i (tt_ctxt i) mty
            let classes = guessClasses i (tt_ctxt i) mty

            let lem = show n ++ " : " ++ 
                            constraints i classes mty ++
                            show (stripMNBind skip (delab i mty))
            let lem_app = show n ++ appArgs skip margs mty

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
                      RawOutput _  -> iPrintResult $ lem_app
                      IdeMode n h ->
                        let good = SexpList [SymbolAtom "ok",
                                             SexpList [SymbolAtom "provisional-definition-lemma",
                                                       SexpList [SymbolAtom "definition-clause",
                                                                 StringAtom lem_app]]]
                        in runIO . hPutStrLn h $ convSExp "return" good n

  where getIndent s = length (takeWhile isSpace s)

        appArgs skip 0 _ = ""
        appArgs skip i (Bind n@(UN c) (Pi _ _ _) sc) 
           | (thead c /= '_' && n `notElem` skip)
                = " " ++ show n ++ appArgs skip (i - 1) sc
        appArgs skip i (Bind _ (Pi _ _ _) sc) = appArgs skip (i - 1) sc
        appArgs skip i _ = ""

        stripMNBind skip (PPi b n@(UN c) _ ty sc) 
           | (thead c /= '_' && n `notElem` skip) ||
               take 4 (str c) == "__pi" -- keep in type, but not in app
                = PPi b n NoFC ty (stripMNBind skip sc)
        stripMNBind skip (PPi b _ _ ty sc) = stripMNBind skip sc
        stripMNBind skip t = t

        constraints :: IState -> [Name] -> Type -> String
        constraints i [] ty = ""
        constraints i [n] ty = showSep ", " (showConstraints i [n] ty) ++ " => "
        constraints i ns ty = "(" ++ showSep ", " (showConstraints i ns ty) ++ ") => "

        showConstraints i ns (Bind n (Pi _ ty _) sc)
            | n `elem` ns = show (delab i ty) : 
                              showConstraints i ns (substV (P Bound n Erased) sc)
            | otherwise = showConstraints i ns (substV (P Bound n Erased) sc)
        showConstraints _ _ _ = []

        -- Guess which binders should be implicits in the generated lemma.
        -- Make them implicit if they appear guarded by a top level constructor,
        -- or at the top level themselves.
        -- Also, make type class instances implicit
        guessImps :: IState -> Context -> Term -> [Name]
        guessImps ist ctxt (Bind n (Pi _ ty _) sc)
           | guarded ctxt n (substV (P Bound n Erased) sc) 
                = n : guessImps ist ctxt sc
           | isClass ist ty
                = n : guessImps ist ctxt sc
           | otherwise = guessImps ist ctxt sc
        guessImps ist ctxt _ = []

        guessClasses :: IState -> Context -> Term -> [Name]
        guessClasses ist ctxt (Bind n (Pi _ ty _) sc)
           | isParamClass ist ty
                = n : guessClasses ist ctxt sc
           | otherwise = guessClasses ist ctxt sc
        guessClasses ist ctxt _ = []

        isClass ist t
           | (P _ n _, args) <- unApply t
                = case lookupCtxtExact n (idris_classes ist) of
                       Just _ -> True
                       _ -> False
           | otherwise = False
        
        isParamClass ist t
           | (P _ n _, args) <- unApply t
                = case lookupCtxtExact n (idris_classes ist) of
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
        guarded ctxt n (Bind _ (Pi _ t _) sc) 
            = guarded ctxt n t || guarded ctxt n sc
        guarded ctxt n _ = False

        blank = all isSpace

        addLem before tyline lem lem_app later
            = let (bef_end, blankline : bef_start) 
                       = case span (not . blank) (reverse before) of
                              (bef, []) -> (bef, "" : [])
                              x -> x
                  mvline = updateMeta False tyline (show n) lem_app in
                unlines $ reverse bef_start ++
                          [blankline, lem, blankline] ++
                          reverse bef_end ++ mvline : later

        addProv before tyline lem_app later
            = let (later_bef, blankline : later_end)
                      = case span (not . blank) later of
                             (bef, []) -> (bef, "" : [])
                             x -> x in
                  unlines $ before ++ tyline : 
                            (later_bef ++ [blankline, lem_app, blankline] ++
                                      later_end)

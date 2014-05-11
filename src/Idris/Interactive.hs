module Idris.Interactive(caseSplitAt, addClauseFrom, addProofClauseFrom,
                         addMissing, makeWith, doProofSearch,
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

import Util.Pretty
import Util.System

import System.FilePath
import System.Directory
import System.IO
import Data.Char


caseSplitAt :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
caseSplitAt h fn updatefile l n
   = do src <- runIO $ readFile fn
        res <- splitOnLine l n fn
        iLOG (showSep "\n" (map show res))
        let (before, (ap : later)) = splitAt (l-1) (lines src)
        res' <- replaceSplits ap res
        let new = concat res'
        if updatefile
          then do let fb = fn ++ "~" -- make a backup!
                  runIO $ writeFile fb (unlines before ++ new ++ unlines later)
                  runIO $ copyFile fb fn
          else -- do ihputStrLn h (show res)
            ihPrintResult h new

addClauseFrom :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
addClauseFrom h fn updatefile l n
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getClause l n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeFile fb (unlines (before ++ nonblank) ++
                                        replicate indent ' ' ++
                                        cl ++ "\n" ++
                                        unlines rest)
                  runIO $ copyFile fb fn
          else ihPrintResult h cl
    where
       getIndent i n [] = 0
       getIndent i n xs | take (length n) xs == n = i
       getIndent i n (x : xs) = getIndent (i + 1) n xs

addProofClauseFrom :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
addProofClauseFrom h fn updatefile l n
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getProofClause l n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeFile fb (unlines (before ++ nonblank) ++
                                        replicate indent ' ' ++
                                        cl ++ "\n" ++
                                        unlines rest)
                  runIO $ copyFile fb fn
          else ihPrintResult h cl
    where
       getIndent i n [] = 0
       getIndent i n xs | take (length n) xs == n = i
       getIndent i n (x : xs) = getIndent (i + 1) n xs

addMissing :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
addMissing h fn updatefile l n
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        i <- getIState
        cl <- getInternalApp fn l
        let n' = getAppName cl

        extras <- case lookupCtxt n' (idris_patdefs i) of
                       [] -> return ""
                       [(_, tms)] -> do tms' <- nameMissing tms
                                        showNew (show n ++ "_rhs") 1 indent tms'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ writeFile fb (unlines (before ++ nonblank)
                                        ++ extras ++ unlines rest)
                  runIO $ copyFile fb fn
          else ihPrintResult h extras
    where showPat = show . stripNS
          stripNS tm = mapPT dens tm where
              dens (PRef fc n) = PRef fc (nsroot n)
              dens t = t

          nsroot (NS n _) = nsroot n
          nsroot (SN (WhereN _ _ n)) = nsroot n
          nsroot n = n

          getAppName (PApp _ r _) = getAppName r
          getAppName (PRef _ r) = r
          getAppName _ = n

          showNew nm i ind (tm : tms)
                        = do (nm', i') <- getUniq nm i
                             rest <- showNew nm i' ind tms
                             return (replicate ind ' ' ++
                                     showPat tm ++ " = ?" ++ nm' ++
                                     "\n" ++ rest)
          showNew nm i _ [] = return ""

          getIndent i n [] = 0
          getIndent i n xs | take (length n) xs == n = i
          getIndent i n (x : xs) = getIndent (i + 1) n xs


makeWith :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
makeWith h fn updatefile l n
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let ind = getIndent tyline
        let with = mkWith tyline n
        -- add clause before first blank line in 'later',
        -- or (TODO) before first line with same indentation as tyline
        let (nonblank, rest) = span (\x -> not (all isSpace x) &&
                                           not (ind == getIndent x)) later
        if updatefile then
           do let fb = fn ++ "~"
              runIO $ writeFile fb (unlines (before ++ nonblank)
                                        ++ with ++ "\n" ++
                                    unlines rest)
              runIO $ copyFile fb fn
           else ihPrintResult h with
  where getIndent s = length (takeWhile isSpace s)


doProofSearch :: Handle -> FilePath -> Bool -> Bool -> 
                 Int -> Name -> [Name] -> Idris ()
doProofSearch h fn updatefile rec l n hints
    = do src <- runIO $ readFile fn
         let (before, tyline : later) = splitAt (l-1) (lines src)
         ctxt <- getContext
         mn <- case lookupNames n ctxt of
                    [x] -> return x
                    [] -> return n
                    ns -> ierror (CantResolveAlts (map show ns))
         i <- getIState
         let (top, envlen, _) = case lookup mn (idris_metavars i) of
                                  Just (t, e, False) -> (t, e, False)
                                  _ -> (Nothing, 0, True)
         let fc = fileFC fn
         let body t = PProof [Try (TSeq Intros (ProofSearch rec t hints))
                                  (ProofSearch rec t hints)]
         let def = PClause fc mn (PRef fc mn) [] (body top) []
         newmv <- idrisCatch
             (do elabDecl' EAll toplevel (PClauses fc [] mn [def])
                 (tm, ty) <- elabVal toplevel False (PRef fc mn)
                 ctxt <- getContext
                 i <- getIState
                 return . flip displayS "" . renderPretty 1.0 80 $
                   pprintPTerm defaultPPOption [] [] (idris_infixes i)
                     (stripNS
                        (dropCtxt envlen
                           (delab i (specialise ctxt [] [(mn, 1)] tm)))))
             (\e -> return ("?" ++ show n))
         if updatefile then
            do let fb = fn ++ "~"
               runIO $ writeFile fb (unlines before ++
                                     updateMeta False tyline (show n) newmv ++ "\n"
                                       ++ unlines later)
               runIO $ copyFile fb fn
            else ihPrintResult h newmv
    where dropCtxt 0 sc = sc
          dropCtxt i (PPi _ _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt i (PLet _ _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt i (PLam _ _ sc) = dropCtxt (i - 1) sc
          dropCtxt _ t = t

          stripNS tm = mapPT dens tm where
              dens (PRef fc n) = PRef fc (nsroot n)
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

addBracket False new = new
addBracket True new@('(':xs) | last xs == ')' = new
addBracket True new | any isSpace new = '(' : new ++ ")"
                    | otherwise = new


makeLemma :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
makeLemma h fn updatefile l n
   = do src <- runIO $ readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)

        ctxt <- getContext
        mty <- case lookupTy n ctxt of
                    [t] -> return t
                    [] -> ierror (NoSuchVariable n)
                    ns -> ierror (CantResolveAlts (map show ns))

        i <- getIState
        let lem = show n ++ " : " ++ show (stripMNBind (delab i mty))
        let lem_app = show n ++ appArgs mty

        if updatefile then
           do let fb = fn ++ "~"
              runIO $ writeFile fb (addLem before tyline lem lem_app later)
              runIO $ copyFile fb fn
           else ihPrintResult h $ lem ++ "\n" ++ lem_app

  where getIndent s = length (takeWhile isSpace s)

        appArgs (Bind n@(UN c) (Pi _) sc) 
           | thead c /= '_' = " " ++ show n ++ appArgs sc
        appArgs (Bind _ (Pi _) sc) = appArgs sc
        appArgs _ = ""

        stripMNBind (PPi b n@(UN c) ty sc) 
           | thead c /= '_' = PPi b n ty (stripMNBind sc)
        stripMNBind (PPi b _ ty sc) = stripMNBind sc
        stripMNBind t = t

        blank = all isSpace

        addLem before tyline lem lem_app later
            = let (bef_end, blankline : bef_start) 
                       = span (not . blank) (reverse before)
                  mvline = updateMeta False tyline (show n) lem_app in
                unlines $ reverse bef_start ++
                          [blankline, lem, blankline] ++
                          reverse bef_end ++ mvline : later




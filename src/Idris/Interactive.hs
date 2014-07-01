{-# LANGUAGE PatternGuards #-}

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
import Idris.IdeSlave hiding (IdeSlaveCommand(..))

import Util.Pretty
import Util.System

import System.FilePath
import System.Directory
import System.IO (Handle(..))
import Data.Char
import Data.Maybe (fromMaybe)
import qualified System.IO.UTF8 as UTF8


caseSplitAt :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
caseSplitAt h fn updatefile l n
   = do src <- runIO $ UTF8.readFile fn
        res <- splitOnLine l n fn
        iLOG (showSep "\n" (map show res))
        let (before, (ap : later)) = splitAt (l-1) (lines src)
        res' <- replaceSplits ap res
        let new = concat res'
        if updatefile
          then do let fb = fn ++ "~" -- make a backup!
                  runIO $ UTF8.writeFile fb (unlines before ++ new ++ unlines later)
                  runIO $ copyFile fb fn
          else -- do ihputStrLn h (show res)
            ihPrintResult h new

addClauseFrom :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
addClauseFrom h fn updatefile l n
   = do src <- runIO $ UTF8.readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getClause l n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ UTF8.writeFile fb (unlines (before ++ nonblank) ++
                                        replicate indent ' ' ++
                                        cl ++ "\n" ++
                                        unlines rest)
                  runIO $ copyFile fb fn
          else ihPrintResult h cl
    where
       getIndent i n [] = 0
       getIndent i n xs | take 9 xs == "instance " = i
       getIndent i n xs | take (length n) xs == n = i
       getIndent i n (x : xs) = getIndent (i + 1) n xs

addProofClauseFrom :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
addProofClauseFrom h fn updatefile l n
   = do src <- runIO $ UTF8.readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let indent = getIndent 0 (show n) tyline
        cl <- getProofClause l n fn
        -- add clause before first blank line in 'later'
        let (nonblank, rest) = span (not . all isSpace) (tyline:later)
        if updatefile
          then do let fb = fn ++ "~"
                  runIO $ UTF8.writeFile fb (unlines (before ++ nonblank) ++
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
   = do src <- runIO $ UTF8.readFile fn
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
                  runIO $ UTF8.writeFile fb (unlines (before ++ nonblank)
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
   = do src <- runIO $ UTF8.readFile fn
        let (before, tyline : later) = splitAt (l-1) (lines src)
        let ind = getIndent tyline
        let with = mkWith tyline n
        -- add clause before first blank line in 'later',
        -- or (TODO) before first line with same indentation as tyline
        let (nonblank, rest) = span (\x -> not (all isSpace x) &&
                                           not (ind == getIndent x)) later
        if updatefile then
           do let fb = fn ++ "~"
              runIO $ UTF8.writeFile fb (unlines (before ++ nonblank)
                                        ++ with ++ "\n" ++
                                    unlines rest)
              runIO $ copyFile fb fn
           else ihPrintResult h with
  where getIndent s = length (takeWhile isSpace s)


doProofSearch :: Handle -> FilePath -> Bool -> Bool -> 
                 Int -> Name -> [Name] -> Maybe Int -> Idris ()
doProofSearch h fn updatefile rec l n hints Nothing
    = doProofSearch h fn updatefile rec l n hints (Just 10)
doProofSearch h fn updatefile rec l n hints (Just depth)
    = do src <- runIO $ UTF8.readFile fn
         let (before, tyline : later) = splitAt (l-1) (lines src)
         ctxt <- getContext
         mn <- case lookupNames n ctxt of
                    [x] -> return x
                    [] -> return n
                    ns -> ierror (CantResolveAlts ns)
         i <- getIState
         let (top, envlen, _) = case lookup mn (idris_metavars i) of
                                  Just (t, e, False) -> (t, e, False)
                                  _ -> (Nothing, 0, True)
         let fc = fileFC fn
         let body t = PProof [Try (TSeq Intros (ProofSearch rec False depth t hints))
                                  (ProofSearch rec False depth t hints)]
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
               runIO $ UTF8.writeFile fb (unlines before ++
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


makeLemma :: Handle -> FilePath -> Bool -> Int -> Name -> Idris ()
makeLemma h fn updatefile l n
   = do src <- runIO $ UTF8.readFile fn
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

        if (not isProv) then do
            let skip = guessImps (tt_ctxt i) mty

            let lem = show n ++ " : " ++ show (stripMNBind skip (delab i mty))
            let lem_app = show n ++ appArgs skip mty

            if updatefile then
               do let fb = fn ++ "~"
                  runIO $ UTF8.writeFile fb (addLem before tyline lem lem_app later)
                  runIO $ copyFile fb fn
               else case idris_outputmode i of
                      RawOutput -> ihPrintResult h $ lem ++ "\n" ++ lem_app
                      IdeSlave n ->
                        let good = SexpList [SymbolAtom "ok",
                                             SexpList [SymbolAtom "metavariable-lemma",
                                                       SexpList [SymbolAtom "replace-metavariable",
                                                                 StringAtom lem_app],
                                                       SexpList [SymbolAtom "definition-type",
                                                                 StringAtom lem]]]
                        in runIO . UTF8.hPutStrLn h $ convSExp "return" good n

          else do -- provisional definition
            let lem_app = show n ++ appArgs [] mty ++
                                 " = ?" ++ show n ++ "_rhs"
            if updatefile then
               do let fb = fn ++ "~"
                  runIO $ UTF8.writeFile fb (addProv before tyline lem_app later)
                  runIO $ copyFile fb fn
               else case idris_outputmode i of
                      RawOutput -> ihPrintResult h $ lem_app
                      IdeSlave n ->
                        let good = SexpList [SymbolAtom "ok",
                                             SexpList [SymbolAtom "provisional-definition-lemma",
                                                       SexpList [SymbolAtom "definition-clause",
                                                                 StringAtom lem_app]]]
                        in runIO . UTF8.hPutStrLn h $ convSExp "return" good n

  where getIndent s = length (takeWhile isSpace s)

        appArgs skip (Bind n@(UN c) (Pi _) sc) 
           | thead c /= '_' && n `notElem` skip
                = " " ++ show n ++ appArgs skip sc
        appArgs skip (Bind _ (Pi _) sc) = appArgs skip sc
        appArgs skip _ = ""

        stripMNBind skip (PPi b n@(UN c) ty sc) 
           | thead c /= '_' && 
             n `notElem` skip = PPi b n ty (stripMNBind skip sc)
        stripMNBind skip (PPi b _ ty sc) = stripMNBind skip sc
        stripMNBind skip t = t

        -- Guess which binders should be implicits in the generated lemma.
        -- Make them implicit if they appear guarded by a top level constructor,
        -- or at the top level themselves.
        guessImps :: Context -> Term -> [Name]
        guessImps ctxt (Bind n (Pi _) sc)
           | guarded ctxt n (substV (P Bound n Erased) sc) 
                = n : guessImps ctxt sc
           | otherwise = guessImps ctxt sc
        guessImps ctxt _ = []

        guarded ctxt n (P _ n' _) | n == n' = True
        guarded ctxt n ap@(App _ _)
            | (P _ f _, args) <- unApply ap,
              isConName f ctxt = any (guarded ctxt n) args
--         guarded ctxt n (Bind (UN cn) (Pi t) sc) -- ignore shadows
--             | thead cn /= '_' = guarded ctxt n t || guarded ctxt n sc
        guarded ctxt n (Bind _ (Pi t) sc) 
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

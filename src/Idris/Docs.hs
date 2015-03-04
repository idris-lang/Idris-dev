{-# LANGUAGE DeriveFunctor, PatternGuards #-}
module Idris.Docs (pprintDocs, getDocs, pprintConstDocs, FunDoc, FunDoc'(..), Docs, Docs'(..)) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Delaborate
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Docstrings (Docstring, emptyDocstring, noDocs, nullDocstring, renderDocstring, DocTerm, renderDocTerm, overview)

import Util.Pretty

import Data.Maybe
import Data.List
import qualified Data.Text as T

-- TODO: Only include names with public/abstract accessibility
--
-- Issue #1573 on the Issue tracker.
--    https://github.com/idris-lang/Idris-dev/issues/1573
data FunDoc' d = FD Name d
                    [(Name, PTerm, Plicity, Maybe d)] -- args: name, ty, implicit, docs
                    PTerm -- function type
                    (Maybe Fixity)
  deriving Functor

type FunDoc = FunDoc' (Docstring DocTerm)

data Docs' d = FunDoc (FunDoc' d)
             | DataDoc (FunDoc' d) -- type constructor docs
                       [FunDoc' d] -- data constructor docs
             | ClassDoc Name d   -- class docs
                        [FunDoc' d] -- method docs
                        [(Name, Maybe d)] -- parameters and their docstrings
                        [PTerm] -- instances
                        [PTerm] -- superclasses
             | ModDoc [String] -- Module name
                      d
  deriving Functor

type Docs = Docs' (Docstring DocTerm)

showDoc ist d
  | nullDocstring d = empty
  | otherwise = text "  -- " <>
                renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) [])) d

pprintFD :: IState -> FunDoc -> Doc OutputAnnotation
pprintFD ist (FD n doc args ty f)
    = nest 4 (prettyName True (ppopt_impl ppo) [] n <+> colon <+>
              pprintPTerm ppo [] [ n | (n@(UN n'),_,_,_) <- args
                                     , not (T.isPrefixOf (T.pack "__") n') ] infixes ty <$>
              renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) [])) doc <$>
              maybe empty (\f -> text (show f) <> line) f <>
              let argshow = showArgs args [] in
              if not (null argshow)
                then nest 4 $ text "Arguments:" <$> vsep argshow
                else empty)

    where ppo = ppOptionIst ist
          infixes = idris_infixes ist
          showArgs ((n, ty, Exp {}, Just d):args) bnd
             = bindingOf n False <+> colon <+>
               pprintPTerm ppo bnd [] infixes ty <>
               showDoc ist d <> line
               :
               showArgs args ((n, False):bnd)
          showArgs ((n, ty, Constraint {}, Just d):args) bnd
             = text "Class constraint" <+>
               pprintPTerm ppo bnd [] infixes ty <> showDoc ist d <> line
               :
               showArgs args ((n, True):bnd)
          showArgs ((n, ty, Imp {}, Just d):args) bnd
             = text "(implicit)" <+>
               bindingOf n True <+> colon <+>
               pprintPTerm ppo bnd [] infixes ty <>
               showDoc ist d <> line
               :
               showArgs args ((n, True):bnd)
          showArgs ((n, _, _, _):args) bnd = showArgs args ((n, True):bnd)
          showArgs []                  _ = []


pprintDocs :: IState -> Docs -> Doc OutputAnnotation
pprintDocs ist (FunDoc d) = pprintFD ist d
pprintDocs ist (DataDoc t args)
           = text "Data type" <+> pprintFD ist t <$>
             if null args then text "No constructors."
             else nest 4 (text "Constructors:" <> line <>
                          vsep (map (pprintFD ist) args))
pprintDocs ist (ClassDoc n doc meths params instances superclasses)
           = nest 4 (text "Type class" <+> prettyName True (ppopt_impl ppo) [] n <>
                     if nullDocstring doc
                       then empty
                       else line <> renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) [])) doc)
             <> line <$>
             nest 4 (text "Parameters:" <$> prettyParameters)
             <> line <$>
             nest 4 (text "Methods:" <$>
                      vsep (map (pprintFD ist) meths))
             <$>
             nest 4 (text "Instances:" <$>
                     vsep (if null instances' then [text "<no instances>"]
                           else map dumpInstance instances'))
             <>
             (if null subclasses then empty
              else line <$> nest 4 (text "Subclasses:" <$>
                                    vsep (map (dumpInstance . prettifySubclasses) subclasses)))
             <>
             (if null superclasses then empty
              else line <$> nest 4 (text "Default superclass instances:" <$>
                                     vsep (map dumpInstance superclasses)))
  where
    params' = zip pNames (repeat False)

    pNames  = map fst params

    ppo = ppOptionIst ist
    infixes = idris_infixes ist

    dumpInstance :: PTerm -> Doc OutputAnnotation
    dumpInstance = pprintPTerm ppo params' [] infixes

    prettifySubclasses (PPi (Constraint _ _) _ tm _)   = prettifySubclasses tm
    prettifySubclasses (PPi plcity           nm t1 t2) = PPi plcity (safeHead nm pNames) (prettifySubclasses t1) (prettifySubclasses t2)
    prettifySubclasses (PApp fc ref args)              = PApp fc ref $ updateArgs pNames args
    prettifySubclasses tm                              = tm

    safeHead _ (y:_) = y
    safeHead x []    = x

    updateArgs (p:ps) ((PExp prty opts _ ref):as) = (PExp prty opts p (updateRef p ref)) : updateArgs ps as
    updateArgs ps     (a:as)                      = a : updateArgs ps as
    updateArgs _      _                           = []

    updateRef nm (PRef fc _) = PRef fc nm
    updateRef _  pt          = pt

    isSubclass (PPi (Constraint _ _) _ (PApp _ _ args) (PApp _ (PRef _ nm) args')) = nm == n && map getTm args == map getTm args'
    isSubclass (PPi _                _ _ pt)                                       = isSubclass pt
    isSubclass _                                                                   = False

    (subclasses, instances') = partition isSubclass instances

    prettyParameters = if any (isJust . snd) params
                       then vsep (map (\(nm,md) -> prettyName True False params' nm <+> maybe empty (showDoc ist) md) params)
                       else hsep (punctuate comma (map (prettyName True False params' . fst) params))

pprintDocs ist (ModDoc mod docs)
   = nest 4 $ text "Module" <+> text (concat (intersperse "." mod)) <> colon <$>
              renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) [])) docs

-- | Determine a truncation function depending how much docs the user
-- wants to see
howMuch FullDocs     = id
howMuch OverviewDocs = overview

-- | Given a fully-qualified, disambiguated name, construct the
-- documentation object for it
getDocs :: Name -> HowMuchDocs -> Idris Docs
getDocs n@(NS n' ns) w | n' == modDocName
   = do i <- getIState
        case lookupCtxtExact n (idris_moduledocs i) of
          Just doc -> return . ModDoc (reverse (map T.unpack ns)) $ howMuch w doc
          Nothing  -> fail $ "Module docs for " ++ show (reverse (map T.unpack ns)) ++
                             " do not exist! This shouldn't have happened and is a bug."
getDocs n w
   = do i <- getIState
        docs <- case lookupCtxt n (idris_classes i) of
                  [ci] -> docClass n ci
                  _ -> case lookupCtxt n (idris_datatypes i) of
                         [ti] -> docData n ti
                         _ -> do fd <- docFun n
                                 return (FunDoc fd)
        return $ fmap (howMuch w) docs

docData :: Name -> TypeInfo -> Idris Docs
docData n ti
  = do tdoc <- docFun n
       cdocs <- mapM docFun (con_names ti)
       return (DataDoc tdoc cdocs)

docClass :: Name -> ClassInfo -> Idris Docs
docClass n ci
  = do i <- getIState
       let docStrings = listToMaybe $ lookupCtxt n $ idris_docstrings i
           docstr = maybe emptyDocstring fst docStrings
           params = map (\pn -> (pn, docStrings >>= (lookup pn . snd))) (class_params ci)
           instances = map (delabTy i) (class_instances ci)
           superclasses = catMaybes $ map getDInst (class_default_superclasses ci)
       mdocs <- mapM (docFun . fst) (class_methods ci)
       return $ ClassDoc n docstr mdocs params instances superclasses
  where
    getDInst (PInstance _ _ _ _ _ _ t _ _) = Just t
    getDInst _                           = Nothing

docFun :: Name -> Idris FunDoc
docFun n
  = do i <- getIState
       let (docstr, argDocs) = case lookupCtxt n (idris_docstrings i) of
                                  [d] -> d
                                  _ -> noDocs
       let ty = delabTy i n
       let args = getPArgNames ty argDocs
       let infixes = idris_infixes i
       let fixdecls = filter (\(Fix _ x) -> x == funName n) infixes
       let f = case fixdecls of
                    []          -> Nothing
                    (Fix x _:_) -> Just x

       return (FD n docstr args ty f)
       where funName :: Name -> String
             funName (UN n)   = str n
             funName (NS n _) = funName n

getPArgNames :: PTerm -> [(Name, Docstring DocTerm)] -> [(Name, PTerm, Plicity, Maybe (Docstring DocTerm))]
getPArgNames (PPi plicity name ty body) ds =
  (name, ty, plicity, lookup name ds) : getPArgNames body ds
getPArgNames _ _ = []

pprintConstDocs :: IState -> Const -> String -> Doc OutputAnnotation
pprintConstDocs ist c str = text "Primitive" <+> text (if constIsType c then "type" else "value") <+>
                            pprintPTerm (ppOptionIst ist) [] [] [] (PConstant c) <+> colon <+>
                            pprintPTerm (ppOptionIst ist) [] [] [] (t c) <>
                            nest 4 (line <> text str)

  where t (Fl _)  = PConstant $ AType ATFloat
        t (BI _)  = PConstant $ AType (ATInt ITBig)
        t (Str _) = PConstant StrType
        t (Ch c)  = PConstant $ AType (ATInt ITChar)
        t _       = PType

{-# LANGUAGE DeriveFunctor, PatternGuards, MultiWayIf #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Docs (pprintDocs, getDocs, pprintConstDocs, FunDoc, FunDoc'(..), Docs, Docs'(..)) where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Delaborate
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Docstrings (Docstring, emptyDocstring, noDocs, nullDocstring, renderDocstring, DocTerm, renderDocTerm, overview)

import Util.Pretty

import Prelude hiding ((<$>))

import Control.Arrow (first)

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
                        [(Maybe Name, PTerm, (d, [(Name, d)]))] -- instances: name for named instances, the constraint term, the docs
                        [PTerm] -- subclasses
                        [PTerm] -- superclasses
                        (Maybe (FunDoc' d)) -- explicit constructor
             | NamedInstanceDoc Name (FunDoc' d) -- name is class
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
pprintDocs ist (ClassDoc n doc meths params instances subclasses superclasses ctor)
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
             maybe empty
                   ((<> line) . nest 4 .
                    (text "Instance constructor:" <$>) .
                    pprintFD ist)
                   ctor
             <>
             nest 4 (text "Instances:" <$>
                       vsep (if null instances then [text "<no instances>"]
                             else map pprintInstance normalInstances))
             <>
             (if null namedInstances then empty
              else line <$> nest 4 (text "Named instances:" <$>
                                    vsep (map pprintInstance namedInstances)))
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
    
    (normalInstances, namedInstances) = partition (\(n, _, _) -> not $ isJust n)
                                                  instances

    pNames  = map fst params

    ppo = ppOptionIst ist
    infixes = idris_infixes ist

    pprintInstance (mname, term, (doc, argDocs)) =
      nest 4 (iname mname <> dumpInstance term <>
              (if nullDocstring doc
                  then empty
                  else line <>
                       renderDocstring
                         (renderDocTerm
                            (pprintDelab ist)
                            (normaliseAll (tt_ctxt ist) []))
                         doc) <>
              if null argDocs
                 then empty
                 else line <> vsep (map (prettyInstanceParam (map fst argDocs)) argDocs))


    iname Nothing = empty
    iname (Just n) = annName n <+> colon <> space

    prettyInstanceParam params (name, doc) =
      if nullDocstring doc
         then empty
         else prettyName True False (zip params (repeat False)) name <+>
              showDoc ist doc

-- if any (isJust . snd) params
-- then vsep (map (\(nm,md) -> prettyName True False params' nm <+> maybe empty (showDoc ist) md) params)
-- else hsep (punctuate comma (map (prettyName True False params' . fst) params))

    dumpInstance :: PTerm -> Doc OutputAnnotation
    dumpInstance = pprintPTerm ppo params' [] infixes

    prettifySubclasses (PPi (Constraint _ _) _ _ tm _)   = prettifySubclasses tm
    prettifySubclasses (PPi plcity           nm fc t1 t2) = PPi plcity (safeHead nm pNames) NoFC (prettifySubclasses t1) (prettifySubclasses t2)
    prettifySubclasses (PApp fc ref args)              = PApp fc ref $ updateArgs pNames args
    prettifySubclasses tm                              = tm

    safeHead _ (y:_) = y
    safeHead x []    = x

    updateArgs (p:ps) ((PExp prty opts _ ref):as) = (PExp prty opts p (updateRef p ref)) : updateArgs ps as
    updateArgs ps     (a:as)                      = a : updateArgs ps as
    updateArgs _      _                           = []

    updateRef nm (PRef fc _) = PRef fc nm
    updateRef _  pt          = pt

    isSubclass (PPi (Constraint _ _) _ _ (PApp _ _ args) (PApp _ (PRef _ nm) args')) = nm == n && map getTm args == map getTm args'
    isSubclass (PPi _   _            _ _ pt)                                       = isSubclass pt
    isSubclass _                                                                   = False

    prettyParameters =
      if any (isJust . snd) params
         then vsep (map (\(nm,md) -> prettyName True False params' nm <+> maybe empty (showDoc ist) md) params)
         else hsep (punctuate comma (map (prettyName True False params' . fst) params))

pprintDocs ist (NamedInstanceDoc _cls doc)
   = nest 4 (text "Named instance:" <$> pprintFD ist doc)

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
        docs <- if | Just ci <- lookupCtxtExact n (idris_classes i)
                     -> docClass n ci
                   | Just ti <- lookupCtxtExact n (idris_datatypes i)
                     -> docData n ti
                   | Just class_ <- classNameForInst i n
                     -> do fd <- docFun n
                           return $ NamedInstanceDoc class_ fd
                   | otherwise
                     -> do fd <- docFun n
                           return (FunDoc fd)
        return $ fmap (howMuch w) docs
  where classNameForInst :: IState -> Name -> Maybe Name
        classNameForInst ist n =
          listToMaybe [ cn
                      | (cn, ci) <- toAlist (idris_classes ist)
                      , n `elem` map fst (class_instances ci)
                      ]

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
           params = map (\pn -> (pn, docStrings >>= (lookup pn . snd)))
                        (class_params ci)
           docsForInstance inst = fromMaybe (emptyDocstring, []) .
                                  flip lookupCtxtExact (idris_docstrings i) $
                                  inst
           instances = map (\inst -> (namedInst inst,
                                      delabTy i inst,
                                      docsForInstance inst))
                           (nub (map fst (class_instances ci)))
           (subclasses, instances') = partition (isSubclass . (\(_,tm,_) -> tm)) instances
           superclasses = catMaybes $ map getDInst (class_default_superclasses ci)
       mdocs <- mapM (docFun . fst) (class_methods ci)
       let ctorN = instanceCtorName ci
       ctorDocs <- case basename ctorN of
                     SN _ -> return Nothing
                     _    -> fmap Just $ docFun ctorN
       return $ ClassDoc
                  n docstr mdocs params
                  instances' (map (\(_,tm,_) -> tm) subclasses) superclasses
                  ctorDocs
  where
    namedInst (NS n ns) = fmap (flip NS ns) (namedInst n)
    namedInst n@(UN _)  = Just n
    namedInst _         = Nothing
    
    getDInst (PInstance _ _ _ _ _ _ _ _ t _ _) = Just t
    getDInst _                                 = Nothing

    isSubclass (PPi (Constraint _ _) _ _ (PApp _ _ args) (PApp _ (PRef _ nm) args'))
      = nm == n && map getTm args == map getTm args'
    isSubclass (PPi _ _ _ _ pt)
      = isSubclass pt
    isSubclass _
      = False

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
             funName n        = show n

getPArgNames :: PTerm -> [(Name, Docstring DocTerm)] -> [(Name, PTerm, Plicity, Maybe (Docstring DocTerm))]
getPArgNames (PPi plicity name _ ty body) ds =
  (name, ty, plicity, lookup name ds) : getPArgNames body ds
getPArgNames _ _ = []

pprintConstDocs :: IState -> Const -> String -> Doc OutputAnnotation
pprintConstDocs ist c str = text "Primitive" <+> text (if constIsType c then "type" else "value") <+>
                            pprintPTerm (ppOptionIst ist) [] [] [] (PConstant NoFC c) <+> colon <+>
                            pprintPTerm (ppOptionIst ist) [] [] [] (t c) <>
                            nest 4 (line <> text str)

  where t (Fl _)  = PConstant NoFC $ AType ATFloat
        t (BI _)  = PConstant NoFC $ AType (ATInt ITBig)
        t (Str _) = PConstant NoFC StrType
        t (Ch c)  = PConstant NoFC $ AType (ATInt ITChar)
        t _       = PType NoFC

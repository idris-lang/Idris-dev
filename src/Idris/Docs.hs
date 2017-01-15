{-|
Module      : Idris.Docs
Description : Data structures and utilities to work with Idris Documentation.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

{-# LANGUAGE DeriveFunctor, MultiWayIf, PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.Docs (
    pprintDocs
  , getDocs, pprintConstDocs, pprintTypeDoc
  , FunDoc, FunDoc'(..), Docs, Docs'(..)
  ) where

import Idris.AbsSyntax (FixDecl(..), Fixity, HowMuchDocs(..), IState(..), Idris,
                        InterfaceInfo(..), PArg'(..), PDecl'(..), PPOption(..),
                        PTerm(..), Plicity(..), RecordInfo(..), basename,
                        getIState, modDocName, ppOptionIst, pprintPTerm,
                        prettyIst, prettyName, type1Doc, typeDescription)
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate
import Idris.Docstrings (DocTerm, Docstring, emptyDocstring, noDocs,
                         nullDocstring, overview, renderDocTerm,
                         renderDocstring)

import Util.Pretty

import Prelude hiding ((<$>))

import Data.List
import Data.Maybe
import qualified Data.Text as T

-- TODO: Only include names with public/export accessibility
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
             | InterfaceDoc Name d  -- interface docs
                            [FunDoc' d] -- method docs
                            [(Name, Maybe d)] -- parameters and their docstrings
                            [PTerm] -- parameter constraints
                            [(Maybe Name, PTerm, (d, [(Name, d)]))] -- implementations: name for named implementations, the constraint term, the docs
                            [PTerm] -- sub interfaces
                            [PTerm] -- super interfaces
                            (Maybe (FunDoc' d)) -- explicit constructor
             | RecordDoc Name d -- record docs
                         (FunDoc' d) -- data constructor docs
                         [FunDoc' d] -- projection docs
                         [(Name, PTerm, Maybe d)] -- parameters with type and doc
             | NamedImplementationDoc Name (FunDoc' d) -- name is interface
             | ModDoc [String] -- Module name
                      d
  deriving Functor

type Docs = Docs' (Docstring DocTerm)

showDoc ist d
  | nullDocstring d = empty
  | otherwise = text "  -- " <>
                renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) [])) d

pprintFD :: IState -> Bool -> Bool -> FunDoc -> Doc OutputAnnotation
pprintFD ist totalityFlag nsFlag (FD n doc args ty f) =
          nest 4 (prettyName True nsFlag [] n
      <+> colon
      <+> pprintPTerm ppo [] [ n | (n@(UN n'),_,_,_) <- args
                             , not (T.isPrefixOf (T.pack "__") n') ] infixes ty
      -- show doc
      <$> renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) [])) doc
      -- show fixity
      <$> maybe empty (\f -> text (show f) <> line) f
      -- show arguments doc
      <> let argshow = showArgs args [] in
           (if not (null argshow)
             then nest 4 $ text "Arguments:" <$> vsep argshow
             else empty)
      -- show totality status
      <> let totality = getTotality in
           (if totalityFlag && not (null totality)
              then line <> (vsep . map (\t -> text "The function is" <+> t) $ totality)
              else empty))

    where
      ppo = ppOptionIst ist

      infixes = idris_infixes ist

      -- Recurse over and show the Function's Documented arguments
      showArgs ((n, ty, Exp {}, Just d):args)        bnd = -- Explicitly bound.
            bindingOf n False
        <+> colon
        <+> pprintPTerm ppo bnd [] infixes ty
        <> showDoc ist d
        <> line : showArgs args ((n, False):bnd)
      showArgs ((n, ty, Constraint {}, Just d):args) bnd = -- Interface constraints.
            text "Interface constraint"
        <+> pprintPTerm ppo bnd [] infixes ty
        <> showDoc ist d
        <> line : showArgs args ((n, True):bnd)
      showArgs ((n, ty, Imp {}, Just d):args)        bnd = -- Implicit arguments.
            text "(implicit)"
        <+> bindingOf n True
        <+> colon
        <+> pprintPTerm ppo bnd [] infixes ty
        <> showDoc ist d
        <> line : showArgs args ((n, True):bnd)
      showArgs ((n, ty, TacImp{}, Just d):args)      bnd = -- Tacit implicits
            text "(auto implicit)"
        <+> bindingOf n True
        <+> colon
        <+> pprintPTerm ppo bnd [] infixes ty
        <> showDoc ist d
        <> line : showArgs args ((n, True):bnd)
      showArgs ((n, _, _, _):args)                   bnd = -- Anything else
            showArgs args ((n, True):bnd)
      showArgs []                                    _   = [] -- end of arguments

      getTotality = map (text . show) $ lookupTotal n (tt_ctxt ist)

pprintFDWithTotality :: IState -> Bool -> FunDoc -> Doc OutputAnnotation
pprintFDWithTotality ist = pprintFD ist True

pprintFDWithoutTotality :: IState -> Bool -> FunDoc -> Doc OutputAnnotation
pprintFDWithoutTotality ist = pprintFD ist False

pprintDocs :: IState -> Docs -> Doc OutputAnnotation
pprintDocs ist (FunDoc d) = pprintFDWithTotality ist True d
pprintDocs ist (DataDoc t args)
           = text "Data type" <+> pprintFDWithoutTotality ist True t <$>
             if null args then text "No constructors."
             else nest 4 (text "Constructors:" <> line <>
                          vsep (map (pprintFDWithoutTotality ist False) args))
pprintDocs ist (InterfaceDoc n doc meths params constraints implementations sub_interfaces super_interfaces ctor)
           = nest 4 (text "Interface" <+> prettyName True (ppopt_impl ppo) [] n <>
                     if nullDocstring doc
                       then empty
                       else line <> renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) [])) doc)
             <> line <$>
             nest 4 (text "Parameters:" <$> prettyParameters)

             <> (if null constraints
                 then empty
                 else line <$> nest 4 (text "Constraints:" <$> prettyConstraints))

             <> line <$>
             nest 4 (text "Methods:" <$>
                      vsep (map (pprintFDWithTotality ist False) meths))
             <$>
             maybe empty
                   ((<> line) . nest 4 .
                    (text "Implementation constructor:" <$>) .
                    pprintFDWithoutTotality ist False)
                   ctor
             <>
             nest 4 (text "Implementations:" <$>
                       vsep (if null implementations then [text "<no implementations>"]
                             else map pprintImplementation normalImplementations))
             <>
             (if null namedImplementations then empty
              else line <$> nest 4 (text "Named implementations:" <$>
                                    vsep (map pprintImplementation namedImplementations)))
             <>
             (if null sub_interfaces then empty
              else line <$> nest 4 (text "Child interfaces:" <$>
                                    vsep (map (dumpImplementation . prettifySubInterfaces) sub_interfaces)))
             <>
             (if null super_interfaces then empty
              else line <$> nest 4 (text "Default parent implementations:" <$>
                                     vsep (map dumpImplementation super_interfaces)))
  where
    params' = zip pNames (repeat False)

    (normalImplementations, namedImplementations) = partition (\(n, _, _) -> not $ isJust n)
                                                              implementations

    pNames  = map fst params

    ppo = ppOptionIst ist
    infixes = idris_infixes ist

    pprintImplementation (mname, term, (doc, argDocs)) =
      nest 4 (iname mname <> dumpImplementation term <>
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
                 else line <> vsep (map (prettyImplementationParam (map fst argDocs)) argDocs))


    iname Nothing = empty
    iname (Just n) = annName n <+> colon <> space

    prettyImplementationParam params (name, doc) =
      if nullDocstring doc
         then empty
         else prettyName True False (zip params (repeat False)) name <+>
              showDoc ist doc

-- if any (isJust . snd) params
-- then vsep (map (\(nm,md) -> prettyName True False params' nm <+> maybe empty (showDoc ist) md) params)
-- else hsep (punctuate comma (map (prettyName True False params' . fst) params))

    dumpImplementation :: PTerm -> Doc OutputAnnotation
    dumpImplementation = pprintPTerm ppo params' [] infixes

    prettifySubInterfaces (PPi (Constraint _ _ _) _ _ tm _)  = prettifySubInterfaces tm
    prettifySubInterfaces (PPi plcity           nm fc t1 t2) = PPi plcity (safeHead nm pNames) NoFC (prettifySubInterfaces t1) (prettifySubInterfaces t2)
    prettifySubInterfaces (PApp fc ref args)                 = PApp fc ref $ updateArgs pNames args
    prettifySubInterfaces tm                                 = tm

    safeHead _ (y:_) = y
    safeHead x []    = x

    updateArgs (p:ps) ((PExp prty opts _ ref):as) = (PExp prty opts p (updateRef p ref)) : updateArgs ps as
    updateArgs ps     (a:as)                      = a : updateArgs ps as
    updateArgs _      _                           = []

    updateRef nm (PRef fc _ _) = PRef fc [] nm
    updateRef _  pt          = pt

    isSubInterface (PPi (Constraint _ _ _) _ _ (PApp _ _ args) (PApp _ (PRef _ _ nm) args')) = nm == n && map getTm args == map getTm args'
    isSubInterface (PPi _   _            _ _ pt)                                           = isSubInterface pt
    isSubInterface _                                                                       = False

    prettyConstraints =
      cat (punctuate (comma <> space) (map (pprintPTerm ppo params' [] infixes) constraints))

    prettyParameters =
      if any (isJust . snd) params
         then vsep (map (\(nm,md) -> prettyName True False params' nm <+> maybe empty (showDoc ist) md) params)
         else hsep (punctuate comma (map (prettyName True False params' . fst) params))

pprintDocs ist (RecordDoc n doc ctor projs params)
  = nest 4 (text "Record" <+> prettyName True (ppopt_impl ppo) [] n <>
             if nullDocstring doc
                then empty
                else line <>
                     renderDocstring (renderDocTerm (pprintDelab ist) (normaliseAll (tt_ctxt ist) [])) doc)
    -- Parameters
    <$> (if null params
            then empty
            else line <> nest 4 (text "Parameters:" <$> prettyParameters) <> line)
    -- Constructor
    <$> nest 4 (text "Constructor:" <$> pprintFDWithoutTotality ist False ctor)
    -- Projections
    <$> nest 4 (text "Projections:" <$> vsep (map (pprintFDWithoutTotality ist False) projs))
  where
    ppo = ppOptionIst ist
    infixes = idris_infixes ist

    pNames  = [n | (n,_,_) <- params]
    params' = zip pNames (repeat False)

    prettyParameters =
      if any isJust [d | (_,_,d) <- params]
         then vsep (map (\(n,pt,d) -> prettyParam (n,pt) <+> maybe empty (showDoc ist) d) params)
         else hsep (punctuate comma (map prettyParam [(n,pt) | (n,pt,_) <- params]))
    prettyParam (n,pt) = prettyName True False params' n <+> text ":" <+> pprintPTerm ppo params' [] infixes pt

pprintDocs ist (NamedImplementationDoc _cls doc)
   = nest 4 (text "Named implementation:" <$> pprintFDWithoutTotality ist True doc)

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
        docs <- if | Just ci <- lookupCtxtExact n (idris_interfaces i)
                     -> docInterface n ci
                   | Just ri <- lookupCtxtExact n (idris_records i)
                     -> docRecord n ri
                   | Just ti <- lookupCtxtExact n (idris_datatypes i)
                     -> docData n ti
                   | Just interface_ <- interfaceNameForImpl i n
                     -> do fd <- docFun n
                           return $ NamedImplementationDoc interface_ fd
                   | otherwise
                     -> do fd <- docFun n
                           return (FunDoc fd)
        return $ fmap (howMuch w) docs
  where interfaceNameForImpl :: IState -> Name -> Maybe Name
        interfaceNameForImpl ist n =
          listToMaybe [ cn
                      | (cn, ci) <- toAlist (idris_interfaces ist)
                      , n `elem` map fst (interface_implementations ci)
                      ]

docData :: Name -> TypeInfo -> Idris Docs
docData n ti
  = do tdoc <- docFun n
       cdocs <- mapM docFun (con_names ti)
       return (DataDoc tdoc cdocs)

docInterface :: Name -> InterfaceInfo -> Idris Docs
docInterface n ci
  = do i <- getIState
       let docStrings = listToMaybe $ lookupCtxt n $ idris_docstrings i
           docstr = maybe emptyDocstring fst docStrings
           params = map (\pn -> (pn, docStrings >>= (lookup pn . snd)))
                        (interface_params ci)
           docsForImplementation impl = fromMaybe (emptyDocstring, []) .
                                  flip lookupCtxtExact (idris_docstrings i) $
                                  impl
           implementations = map (\impl -> (namedImpl impl,
                                            delabTy i impl,
                                            docsForImplementation impl))
                             (nub (map fst (interface_implementations ci)))
           (sub_interfaces, implementations') = partition (isSubInterface . (\(_,tm,_) -> tm)) implementations
           super_interfaces = catMaybes $ map getDImpl (interface_default_super_interfaces ci)
       mdocs <- mapM (docFun . fst) (interface_methods ci)
       let ctorN = implementationCtorName ci
       ctorDocs <- case basename ctorN of
                     SN _ -> return Nothing
                     _    -> fmap Just $ docFun ctorN
       return $ InterfaceDoc
                  n docstr mdocs params (interface_constraints ci)
                  implementations' (map (\(_,tm,_) -> tm) sub_interfaces) super_interfaces
                  ctorDocs
  where
    namedImpl (NS n ns) = fmap (flip NS ns) (namedImpl n)
    namedImpl n@(UN _)  = Just n
    namedImpl _         = Nothing

    getDImpl (PImplementation _ _ _ _ _ _ _ _ _ _ _ _ t _ _) = Just t
    getDImpl _                                         = Nothing

    isSubInterface (PPi (Constraint _ _ _) _ _ (PApp _ _ args) (PApp _ (PRef _ _ nm) args'))
      = nm == n && map getTm args == map getTm args'
    isSubInterface (PPi _ _ _ _ pt)
      = isSubInterface pt
    isSubInterface _
      = False

docRecord :: Name -> RecordInfo -> Idris Docs
docRecord n ri
  = do i <- getIState
       let docStrings = listToMaybe $ lookupCtxt n $ idris_docstrings i
           docstr = maybe emptyDocstring fst docStrings
           params = map (\(pn,pt) -> (pn, pt, docStrings >>= (lookup (nsroot pn) . snd)))
                        (record_parameters ri)
       pdocs <- mapM docFun (record_projections ri)
       ctorDocs <- docFun $ record_constructor ri
       return $ RecordDoc n docstr ctorDocs pdocs params

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


pprintTypeDoc :: IState -> Doc OutputAnnotation
pprintTypeDoc ist = prettyIst ist (PType emptyFC) <+> colon <+> type1Doc <+>
                     nest 4 (line <> text typeDescription)

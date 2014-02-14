module Idris.Docs where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Delaborate
import Idris.Core.TT
import Idris.Core.Evaluate

import Util.Pretty

import Data.Maybe
import Data.List

-- TODO: Only include names with public/abstract accessibility

data FunDoc = FD Name String
                 [(Name, PTerm, Plicity)] -- args: name, ty, plicity
                 PTerm -- function type
                 (Maybe Fixity)

data Docs = FunDoc FunDoc
          | DataDoc FunDoc -- type constructor docs
                    [FunDoc] -- data constructor docs
          | ClassDoc Name String -- class docs
                     [FunDoc] -- method docs

showDoc "" = empty
showDoc x = text "  -- " <> text x

pprintFD :: Bool -> FunDoc -> Doc OutputAnnotation
pprintFD imp (FD n doc args ty f)
    = prettyName imp [] n <+> colon <+> prettyImp imp ty <$> showDoc doc <$>
      maybe empty (\f -> text (show f) <> line) f <>
      let argshow = mapMaybe showArg args in
      if not (null argshow)
        then nest 4 $ text "Arguments:" <$> vsep argshow
        else empty

    where showArg (n, ty, arg@(Exp {}))
             = Just $ bindingOf n False <+> colon <+> prettyImp imp ty <>
                      showDoc (pdocstr arg) <> line
          showArg (n, ty, arg@(Constraint {}))
             = Just $ text "Class constraint" <+>
                      prettyImp imp ty <> showDoc (pdocstr arg) <> line
          showArg (n, ty, arg@(Imp {}))
           | not (null doc)
             = Just $ text "(implicit)" <+>
                      bindingOf n True <+> colon <+> prettyImp imp ty
                      <> showDoc (pdocstr arg) <> line
          showArg (n, _, _) = Nothing



pprintDocs imp (FunDoc d) = pprintFD imp d
pprintDocs imp (DataDoc t args)
           = text "Data type" <+> pprintFD imp t <$>
             nest 4 (text "Constructors:" <> line <>
                     vsep (map (pprintFD imp) args))
pprintDocs imp (ClassDoc n doc meths)
           = text "Type class" <+> prettyName imp [] n <$> -- parameters?
             nest 4 (text "Methods:" <$>
                     vsep (map (pprintFD imp) meths))

getDocs :: Name -> Idris Docs
getDocs n
   = do i <- getIState
        case lookupCtxt n (idris_classes i) of
             [ci] -> docClass n ci
             _ -> case lookupCtxt n (idris_datatypes i) of
                       [ti] -> docData n ti
                       _ -> do fd <- docFun n
                               return (FunDoc fd)

docData :: Name -> TypeInfo -> Idris Docs
docData n ti
  = do tdoc <- docFun n
       cdocs <- mapM docFun (con_names ti)
       return (DataDoc tdoc cdocs)

docClass :: Name -> ClassInfo -> Idris Docs
docClass n ci
  = do i <- getIState
       let docstr = case lookupCtxt n (idris_docstrings i) of
                         [str] -> str
                         _ -> ""
       mdocs <- mapM docFun (map fst (class_methods ci))
       return (ClassDoc n docstr mdocs)

docFun :: Name -> Idris FunDoc
docFun n
  = do i <- getIState
       let docstr = case lookupCtxt n (idris_docstrings i) of
                         [str] -> str
                         _ -> ""
       let ty = delabTy i n
       let args = getPArgNames ty
       let infixes = idris_infixes i
       let fixdecls = filter (\(Fix _ x) -> x == funName n) infixes
       let f = case fixdecls of
                    []          -> Nothing
                    (Fix x _:_) -> Just x

       return (FD n docstr args ty f)
       where funName :: Name -> String
             funName (UN n)   = str n
             funName (NS n _) = funName n

getPArgNames :: PTerm -> [(Name, PTerm, Plicity)]
getPArgNames (PPi plicity name ty body) = ((name, ty, plicity) : getPArgNames body)
getPArgNames _ = []

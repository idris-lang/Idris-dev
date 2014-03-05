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
                 [(Name, PTerm, Plicity, Maybe String)] -- args: name, ty, implicit, docs
                 PTerm -- function type
                 (Maybe Fixity)
  deriving Show

data Docs = FunDoc FunDoc
          | DataDoc FunDoc -- type constructor docs
                    [FunDoc] -- data constructor docs
          | ClassDoc Name String -- class docs
                     [FunDoc] -- method docs
  deriving Show

showDoc "" = empty
showDoc x = text "  -- " <> text x

pprintFD :: Bool -> FunDoc -> Doc OutputAnnotation
pprintFD imp (FD n doc args ty f)
    = nest 4 (prettyName imp [] n <+> colon <+> prettyImp imp ty <$> showDoc doc <$>
              maybe empty (\f -> text (show f) <> line) f <>
              let argshow = showArgs args [] in
              if not (null argshow)
                then nest 4 $ text "Arguments:" <$> vsep argshow
                else empty)

    where showArgs ((n, ty, Exp {}, d):args) bnd
             = bindingOf n False <+> colon <+>
               pprintPTerm imp bnd ty <>
               showDoc (maybe "" id d) <> line
               :
               showArgs args ((n, False):bnd)
          showArgs ((n, ty, Constraint {}, d):args) bnd
             = text "Class constraint" <+>
               pprintPTerm imp bnd ty <> showDoc (maybe "" id d) <> line
               :
               showArgs args ((n, True):bnd)
          showArgs ((n, ty, Imp {}, d):args) bnd
           | not (null doc)
             = text "(implicit)" <+>
               bindingOf n True <+> colon <+>
               pprintPTerm imp bnd ty <>
               showDoc (maybe "" id d) <> line
               :
               showArgs args ((n, True):bnd)
          showArgs ((n, _, _, _):args) bnd = showArgs args ((n, True):bnd)
          showArgs []                  _ = []



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
                         [str] -> fst str
                         _ -> ""
       mdocs <- mapM docFun (map fst (class_methods ci))
       return (ClassDoc n docstr mdocs)

docFun :: Name -> Idris FunDoc
docFun n
  = do i <- getIState
       let (docstr, argDocs) = case lookupCtxt n (idris_docstrings i) of
                                  [d] -> d
                                  _ -> ("", [])
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

getPArgNames :: PTerm -> [(Name, String)] -> [(Name, PTerm, Plicity, Maybe String)]
getPArgNames (PPi plicity name ty body) ds =
  (name, ty, plicity, lookup name ds) : getPArgNames body ds
getPArgNames _ _ = []

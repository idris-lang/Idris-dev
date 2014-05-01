{-# LANGUAGE PatternGuards #-}
module Idris.Docs where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Delaborate
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Docstrings

import Util.Pretty

import Data.Maybe
import Data.List
import qualified Data.Text as T

-- TODO: Only include names with public/abstract accessibility

data FunDoc = FD Name Docstring
                 [(Name, PTerm, Plicity, Maybe Docstring)] -- args: name, ty, implicit, docs
                 PTerm -- function type
                 (Maybe Fixity)
  deriving Show

data Docs = FunDoc FunDoc
          | DataDoc FunDoc -- type constructor docs
                    [FunDoc] -- data constructor docs
          | ClassDoc Name Docstring -- class docs
                     [FunDoc] -- method docs
                     [Name] -- parameter docs
                     [PTerm] -- instances
  deriving Show

showDoc d | nullDocstring d = empty
          | otherwise       = text "  -- " <> renderDocstring d

pprintFD :: Bool -> FunDoc -> Doc OutputAnnotation
pprintFD imp (FD n doc args ty f)
    = nest 4 (prettyName imp [] n <+> colon <+>
              pprintPTerm imp [] [ n | (n@(UN n'),_,_,_) <- args
                                     , not (T.isPrefixOf (T.pack "__") n') ] ty <$>
              renderDocstring doc <$>
              maybe empty (\f -> text (show f) <> line) f <>
              let argshow = showArgs args [] in
              if not (null argshow)
                then nest 4 $ text "Arguments:" <$> vsep argshow
                else empty)

    where showArgs ((n, ty, Exp {}, Just d):args) bnd
             = bindingOf n False <+> colon <+>
               pprintPTerm imp bnd [] ty <>
               showDoc d <> line
               :
               showArgs args ((n, False):bnd)
          showArgs ((n, ty, Constraint {}, Just d):args) bnd
             = text "Class constraint" <+>
               pprintPTerm imp bnd [] ty <> showDoc d <> line
               :
               showArgs args ((n, True):bnd)
          showArgs ((n, ty, Imp {}, Just d):args) bnd
             = text "(implicit)" <+>
               bindingOf n True <+> colon <+>
               pprintPTerm imp bnd [] ty <>
               showDoc d <> line
               :
               showArgs args ((n, True):bnd)
          showArgs ((n, _, _, _):args) bnd = showArgs args ((n, True):bnd)
          showArgs []                  _ = []


pprintDocs :: Bool -> Docs -> Doc OutputAnnotation
pprintDocs imp (FunDoc d) = pprintFD imp d
pprintDocs imp (DataDoc t args)
           = text "Data type" <+> pprintFD imp t <$>
             nest 4 (text "Constructors:" <> line <>
                     vsep (map (pprintFD imp) args))
pprintDocs imp (ClassDoc n doc meths params instances)
           = nest 4 (text "Type class" <+> prettyName imp [] n <>
                     if nullDocstring doc then empty else line <> renderDocstring doc)
             <> line <$>
             nest 4 (text "Parameters:" <$>
                      hsep (punctuate comma (map (prettyName False params') params)))
             <> line <$>
             nest 4 (text "Methods:" <$>
                      vsep (map (pprintFD imp) meths))
             <$>
             nest 4 (text "Defined instances:" <$>
                     vsep (if null definedInstances then [text "<no instances>"]
                           else map dumpInstance definedInstances))
             <>
             if null generatedInstances then empty
             else line <$> nest 4 (text "Instances generated from subclasses:" <$>
                                   vsep (map dumpInstance generatedInstances))
  where
    params' = zip params (repeat False)

    dumpInstance :: PTerm -> Doc OutputAnnotation
    dumpInstance = pprintPTerm imp params' []

    hasConstraint (PPi (Constraint _ _) _ _ _)  = True
    hasConstraint (PPi _                _ _ pt) = hasConstraint pt
    hasConstraint _                             = False

    (generatedInstances, definedInstances) = partition hasConstraint instances

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
       ctxt <- getContext
       let docstr = case lookupCtxt n (idris_docstrings i) of
                         [str] -> fst str
                         _ -> emptyDocstring
           params = class_params ci
           instances = map (delabTy i) (class_instances ci)
       mdocs <- mapM docFun (map fst (class_methods ci))
       return $ ClassDoc n docstr mdocs params instances

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
             funName n
               | n == falseTy = "_|_"

getPArgNames :: PTerm -> [(Name, Docstring)] -> [(Name, PTerm, Plicity, Maybe Docstring)]
getPArgNames (PPi plicity name ty body) ds =
  (name, ty, plicity, lookup name ds) : getPArgNames body ds
getPArgNames _ _ = []

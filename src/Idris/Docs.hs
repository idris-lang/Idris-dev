{-# LANGUAGE PatternGuards #-}
module Idris.Docs (pprintDocs, getDocs, FunDoc(..), Docs (..)) where

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
                     [(Name, Maybe Docstring)] -- parameters and their docstrings
                     [PTerm] -- instances
  deriving Show

showDoc d | nullDocstring d = empty
          | otherwise       = text "  -- " <> renderDocstring d

pprintFD :: IState -> FunDoc -> Doc OutputAnnotation
pprintFD ist (FD n doc args ty f)
    = nest 4 (prettyName (ppopt_impl ppo) [] n <+> colon <+>
              pprintPTerm ppo [] [ n | (n@(UN n'),_,_,_) <- args
                                     , not (T.isPrefixOf (T.pack "__") n') ] infixes ty <$>
              renderDocstring doc <$>
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
               showDoc d <> line
               :
               showArgs args ((n, False):bnd)
          showArgs ((n, ty, Constraint {}, Just d):args) bnd
             = text "Class constraint" <+>
               pprintPTerm ppo bnd [] infixes ty <> showDoc d <> line
               :
               showArgs args ((n, True):bnd)
          showArgs ((n, ty, Imp {}, Just d):args) bnd
             = text "(implicit)" <+>
               bindingOf n True <+> colon <+>
               pprintPTerm ppo bnd [] infixes ty <>
               showDoc d <> line
               :
               showArgs args ((n, True):bnd)
          showArgs ((n, _, _, _):args) bnd = showArgs args ((n, True):bnd)
          showArgs []                  _ = []


pprintDocs :: IState -> Docs -> Doc OutputAnnotation
pprintDocs ist (FunDoc d) = pprintFD ist d
pprintDocs ist (DataDoc t args)
           = text "Data type" <+> pprintFD ist t <$>
             nest 4 (text "Constructors:" <> line <>
                     vsep (map (pprintFD ist) args))
pprintDocs ist (ClassDoc n doc meths params instances)
           = nest 4 (text "Type class" <+> prettyName (ppopt_impl ppo) [] n <>
                     if nullDocstring doc then empty else line <> renderDocstring doc)
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
             if null subclasses then empty
             else line <$> nest 4 (text "Subclasses:" <$>
                                   vsep (map (dumpInstance . prettifySubclasses) subclasses))
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

    hasConstraint (PPi (Constraint _ _) _ _ _)  = True
    hasConstraint (PPi _                _ _ pt) = hasConstraint pt
    hasConstraint _                             = False

    (subclasses, instances') = partition hasConstraint instances

    prettyParameters = if any (isJust . snd) params
                       then vsep (map (\(nm,md) -> prettyName False params' nm <+> maybe empty showDoc md) params)
                       else hsep (punctuate comma (map (prettyName False params' . fst) params))

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
       let docStrings = listToMaybe $ lookupCtxt n $ idris_docstrings i
           docstr = maybe emptyDocstring fst docStrings
           params = map (\pn -> (pn, docStrings >>= (lookup pn . snd))) (class_params ci)
           instances = map (delabTy i) (class_instances ci)
       mdocs <- mapM (docFun .fst) (class_methods ci)
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

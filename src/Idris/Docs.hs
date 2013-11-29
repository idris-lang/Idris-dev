module Idris.Docs where

import Idris.AbsSyntax
import Idris.AbsSyntaxTree
import Idris.Delaborate
import Idris.Core.TT
import Idris.Core.Evaluate

import Data.Maybe
import Data.List

-- TODO: Only include names with public/abstract accessibility

data FunDoc = Doc Name String
                  [(Name, PArg)] -- args
                  PTerm -- function type
                  (Maybe Fixity)

data Doc = FunDoc FunDoc
         | DataDoc FunDoc -- type constructor docs
                   [FunDoc] -- data constructor docs
         | ClassDoc Name String -- class docs
                    [FunDoc] -- method docs

showDoc "" = ""
showDoc x = "  -- " ++ x

instance Show FunDoc where
   show (Doc n doc args ty f)
      = show n ++ " : " ++ show ty ++ "\n" ++ showDoc doc ++ "\n" ++
        maybe "" (\f -> show f ++ "\n\n") f ++
        let argshow = mapMaybe showArg args in
            if not (null argshow)
               then "Arguments:\n\t" ++ showSep "\t" argshow
               else ""

    where showArg (n, arg@(PExp _ _ _ _))
             = Just $ showName n ++ show (getTm arg) ++
                      showDoc (pargdoc arg) ++ "\n"
          showArg (n, arg@(PConstraint _ _ _ _))
             = Just $ "Class constraint " ++
                      show (getTm arg) ++ showDoc (pargdoc arg)
                      ++ "\n"
          showArg (n, arg@(PImp _ _ _ _ _ doc))
           | not (null doc)
             = Just $ "(implicit) " ++
                      show n ++ " : " ++ show (getTm arg)
                      ++ showDoc (pargdoc arg) ++ "\n"
          showArg (n, _) = Nothing

          showName (MN _ _) = ""
          showName x = show x ++ " : "

instance Show Doc where

    show (FunDoc d) = show d
    show (DataDoc t args) = "Data type " ++ show t ++
       "\nConstructors:\n\n" ++
       showSep "\n" (map show args)
    show (ClassDoc n doc meths)
       = "Type class " ++ show n ++ -- parameters?
         "\nMethods:\n\n" ++
         showSep "\n" (map show meths)

getDocs :: Name -> Idris Doc
getDocs n
   = do i <- getIState
        case lookupCtxt n (idris_classes i) of
             [ci] -> docClass n ci
             _ -> case lookupCtxt n (idris_datatypes i) of
                       [ti] -> docData n ti
                       _ -> do fd <- docFun n
                               return (FunDoc fd)

docData :: Name -> TypeInfo -> Idris Doc
docData n ti
  = do tdoc <- docFun n
       cdocs <- mapM docFun (con_names ti)
       return (DataDoc tdoc cdocs)

docClass :: Name -> ClassInfo -> Idris Doc
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
       let ty = case lookupTy n (tt_ctxt i) of
                     (t : _) -> t
       let argnames = map fst (getArgTys ty)
       let args = case lookupCtxt n (idris_implicits i) of
                       [args] -> zip argnames args
                       _ -> []
       let infixes = idris_infixes i
       let fixdecls = filter (\(Fix _ x) -> x == funName n) infixes
       let f = case fixdecls of
                    []          -> Nothing
                    (Fix x _:_) -> Just x

       return (Doc n docstr args (delab i ty) f)
       where funName :: Name -> String
             funName (UN n)   = n
             funName (NS n _) = funName n



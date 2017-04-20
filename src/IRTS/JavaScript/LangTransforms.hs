{-|
Module      : IRTS.JavaScript.LangTransforms
Description : The JavaScript LDecl Transformations.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving, OverloadedStrings, DeriveGeneric, DeriveAnyClass, FlexibleInstances #-}

module IRTS.JavaScript.LangTransforms( used_decls
                                     ) where


import Control.DeepSeq
import Data.Text (Text)
import qualified Data.Text as T
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Idris.Core.TT
import IRTS.Lang
import Idris.Core.CaseTree
import Data.List
import Data.Maybe
import Control.Monad.Trans.State

import GHC.Generics (Generic)
import Data.Data
import Data.Generics.Uniplate.Data
import Idris.Core.DeepSeq

deriving instance Typeable (LAlt' LExp)
deriving instance Data (LAlt' LExp)
deriving instance Typeable FDesc
deriving instance Data FDesc
deriving instance Typeable LVar
deriving instance Data LVar
deriving instance Typeable PrimFn
deriving instance Data PrimFn
deriving instance Typeable CaseType
deriving instance Data CaseType
deriving instance Typeable LExp
deriving instance Data LExp
deriving instance Typeable LDecl
deriving instance Data LDecl
deriving instance Typeable LOpt
deriving instance Data LOpt

deriving instance Generic LDecl
deriving instance NFData LDecl
deriving instance Generic LOpt
deriving instance NFData LOpt
deriving instance Generic LExp
deriving instance NFData LExp
deriving instance NFData PrimFn
deriving instance Generic LVar
deriving instance NFData LVar
deriving instance NFData (LAlt' LExp)
deriving instance Generic (LAlt' e)
deriving instance NFData FDesc
deriving instance Generic FDesc

{-
deriving instance NFData FC
deriving instance NFData FC'
deriving instance NFData SpecialName
deriving instance NFData Name
deriving instance NFData ArithTy
deriving instance NFData IntTy
deriving instance NFData NativeTy
deriving instance NFData Const
deriving instance NFData CaseType
-}


restrictKeys :: Ord k => Map k a -> Set k -> Map k a
restrictKeys m s = Map.filterWithKey (\k _ -> k `Set.member` s) m

mapMapListKeys :: Ord k => (a->a) -> [k] -> Map k a -> Map k a
mapMapListKeys _ [] x = x
mapMapListKeys f (t:r) x = mapMapListKeys f r $ Map.adjust f t x

memberCtx ::  Name -> Ctxt a -> Bool
memberCtx n ctx =
  case lookupCtxtExact n ctx of
    Nothing -> False
    Just _ -> True


extract_globs :: LDefs -> LDecl -> [Name]
extract_globs defs (LConstructor _ _ _) = []
extract_globs defs (LFun _ _ _ e) =
  let f (LV (Glob x)) = Just x
      f (LLazyApp x _) = Just x
      f _ = Nothing
  in [x | Just x <- map f $ universe e, memberCtx x defs]

used_functions :: LDefs -> Set Name -> [Name] -> [Name]
used_functions _ _ [] = []
used_functions alldefs done names =
  let decls = catMaybes $ map (\x -> lookupCtxtExact x alldefs) names
      used_names = (nub $ concat $ map (extract_globs alldefs) decls) \\ names
      new_names = filter (\x -> not $ Set.member x done) used_names
  in  used_names ++ used_functions alldefs (Set.union done $ Set.fromList new_names) new_names


used_decls :: LDefs -> [Name] -> [LDecl]
used_decls dcls start =
  let used = reverse $ start ++ used_functions dcls (Set.fromList start) start
  in catMaybes $ map (\x -> lookupCtxtExact  x dcls) used

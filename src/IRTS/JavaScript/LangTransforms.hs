{-|
Module      : IRTS.JavaScript.LangTransforms
Description : The JavaScript LDecl Transformations.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
             FlexibleInstances, OverloadedStrings, StandaloneDeriving #-}

module IRTS.JavaScript.LangTransforms( used_defs
                                     ) where


import Control.DeepSeq
import Control.Monad.Trans.State
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Idris.Core.CaseTree
import Idris.Core.TT
import IRTS.Lang

import Data.Data
import Data.Generics.Uniplate.Data
import GHC.Generics (Generic)

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


restrictKeys :: Ord k => Map k a -> Set k -> Map k a
restrictKeys m s = Map.filterWithKey (\k _ -> k `Set.member` s) m

mapMapListKeys :: Ord k => (a->a) -> [k] -> Map k a -> Map k a
mapMapListKeys _ [] x = x
mapMapListKeys f (t:r) x = mapMapListKeys f r $ Map.adjust f t x


extract_globs :: Map Name LDecl -> LDecl -> [Name]
extract_globs defs (LConstructor _ _ _) = []
extract_globs defs (LFun _ _ _ e) =
  let f (LV (Glob x)) = Just x
      f (LLazyApp x _) = Just x
      f _ = Nothing
  in [x | Just x <- map f $ universe e, Map.member x defs]

used_functions :: Map Name LDecl -> Set Name -> [Name] -> [Name]
used_functions _ _ [] = []
used_functions alldefs done names =
  let decls = catMaybes $ map (\x -> Map.lookup x alldefs) names
      used_names = (nub $ concat $ map (extract_globs alldefs) decls) \\ names
      new_names = filter (\x -> not $ Set.member x done) used_names
  in  used_names ++ used_functions alldefs (Set.union done $ Set.fromList new_names) new_names


used_decls :: Map Name LDecl -> [Name] -> Map Name LDecl
used_decls dcls start =
  let used = reverse $ start ++ used_functions dcls (Set.fromList start) start
  in restrictKeys dcls (Set.fromList used) --catMaybes $ map (\x -> Map.lookup  x dcls) used

getUsedConstructors :: Map Name LDecl -> Set Name
getUsedConstructors x = Set.fromList [ n | LCon _ _ n _ <- universeBi x]

remove_unused_branches :: Set Name -> Map Name LDecl -> Map Name LDecl
remove_unused_branches used x =
  transformBi f x
  where
    f :: [LAlt] -> [LAlt]
    f ((LConCase x n y z):r) =
      if Set.member n used then ((LConCase x n y z):r)
        else r
    f x = x

used_defs :: Map Name LDecl -> [Name] -> Map Name LDecl
used_defs dcls start =
  let used = used_decls dcls start
      remCons = remove_unused_branches (getUsedConstructors used) used
  in if Map.keys remCons == Map.keys dcls then remCons
        else used_defs remCons start

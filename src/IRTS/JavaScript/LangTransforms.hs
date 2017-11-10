{-|
Module      : IRTS.JavaScript.LangTransforms
Description : The JavaScript LDecl Transformations.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveDataTypeable, OverloadedStrings, StandaloneDeriving #-}

module IRTS.JavaScript.LangTransforms( removeDeadCode
                                     , globlToCon
                                     ) where


import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Idris.Core.CaseTree
import Idris.Core.TT
import IRTS.Lang

import Data.Data
import Data.Generics.Uniplate.Data

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

extractGlobs :: Map Name LDecl -> LDecl -> [Name]
extractGlobs defs (LConstructor _ _ _) = []
extractGlobs defs (LFun _ _ _ e) =
  let f (LV x) = Just x
      f (LLazyApp x _) = Just x
      f _ = Nothing
  in [x | Just x <- map f $ universe e, Map.member x defs]

usedFunctions :: Map Name LDecl -> Set Name -> [Name] -> [Name]
usedFunctions _ _ [] = []
usedFunctions alldefs done names =
  let decls = catMaybes $ map (\x -> Map.lookup x alldefs) names
      used_names = (nub $ concat $ map (extractGlobs alldefs) decls) \\ names
      new_names = filter (\x -> not $ Set.member x done) used_names
  in  used_names ++ usedFunctions alldefs (Set.union done $ Set.fromList new_names) new_names


usedDecls :: Map Name LDecl -> [Name] -> Map Name LDecl
usedDecls dcls start =
  let used = reverse $ start ++ usedFunctions dcls (Set.fromList start) start
  in restrictKeys dcls (Set.fromList used)

getUsedConstructors :: Map Name LDecl -> Set Name
getUsedConstructors x = Set.fromList [ n | LCon _ _ n _ <- universeBi x]

removeUnusedBranches :: Set Name -> Map Name LDecl -> Map Name LDecl
removeUnusedBranches used x =
  transformBi f x
  where
    f :: [LAlt] -> [LAlt]
    f ((LConCase x n y z):r) =
      if Set.member n used then ((LConCase x n y z):r)
        else r
    f x = x

removeDeadCode :: Map Name LDecl -> [Name] -> Map Name LDecl
removeDeadCode dcls start =
  let used = usedDecls dcls start
      remCons = removeUnusedBranches (getUsedConstructors used) used
  in if Map.keys remCons == Map.keys dcls then remCons
        else removeDeadCode remCons start


globlToCon :: Map Name LDecl -> Map Name LDecl
globlToCon x =
  transformBi (f x) x
  where
    f :: Map Name LDecl -> LExp -> LExp
    f y x@(LV n) =
      case Map.lookup n y of
        Just (LConstructor _ conId arity) -> LCon Nothing conId n []
        _ -> x
    f y x = x

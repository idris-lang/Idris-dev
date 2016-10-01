{-|
Module      : Idris.WhoCalls
Description : Find function callers and callees.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.WhoCalls (whoCalls, callsWho) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT

import Data.List (nub)

occurs :: Name -> Term -> Bool
occurs n (P Bound _ _) = False
occurs n (P _ n' _) = n == n'
occurs n (Bind _ b sc) = occursBinder n b || occurs n sc
occurs n (App _ t1 t2) = occurs n t1 || occurs n t2
occurs n (Proj t _) = occurs n t
occurs n _ = False

names :: Term -> [Name]
names (P Bound _ _) = []
names (P _ n _) = [n]
names (Bind _ b sc) = namesBinder b ++ names sc
names (App _ t1 t2) = names t1 ++ names t2
names (Proj t _) = names t
names _ = []

occursBinder :: Name -> Binder Term -> Bool
occursBinder n (Let ty val) = occurs n ty || occurs n val
occursBinder n (NLet ty val) = occurs n ty || occurs n val
occursBinder n b = occurs n (binderTy b)

namesBinder :: Binder Term -> [Name]
namesBinder (Let ty val) = names ty ++ names val
namesBinder (NLet ty val) = names ty ++ names val
namesBinder b = names (binderTy b)

occursSC :: Name -> SC -> Bool
occursSC n (Case _ _ alts) = any (occursCaseAlt n) alts
occursSC n (ProjCase t alts) = occurs n t || any (occursCaseAlt n) alts
occursSC n (STerm t) = occurs n t
occursSC n _ = False

namesSC :: SC -> [Name]
namesSC (Case _ _ alts) = concatMap namesCaseAlt alts
namesSC (ProjCase t alts) = names t ++ concatMap namesCaseAlt alts
namesSC (STerm t) = names t
namesSC _ = []

occursCaseAlt :: Name -> CaseAlt -> Bool
occursCaseAlt n (ConCase n' _ _ sc) = n == n' || occursSC n sc
occursCaseAlt n (FnCase n' _ sc) = n == n' || occursSC n sc
occursCaseAlt n (ConstCase _ sc) = occursSC n sc
occursCaseAlt n (SucCase _ sc) = occursSC n sc
occursCaseAlt n (DefaultCase sc) = occursSC n sc

namesCaseAlt :: CaseAlt -> [Name]
namesCaseAlt (ConCase n' _ _ sc) = n' : namesSC sc
namesCaseAlt (FnCase n' _ sc) = n' : namesSC sc
namesCaseAlt (ConstCase _ sc) = namesSC sc
namesCaseAlt (SucCase _ sc) = namesSC sc
namesCaseAlt (DefaultCase sc) = namesSC sc

occursDef :: Name -> Def -> Bool
occursDef n (Function ty tm) = occurs n ty || occurs n tm
occursDef n (TyDecl _ ty) = occurs n ty
occursDef n (Operator ty _ _) = occurs n ty
occursDef n (CaseOp _ ty _ _ _ defs) = occurs n ty || occursSC n (snd (cases_compiletime defs))

namesDef :: Def -> [Name]
namesDef (Function ty tm) = names ty ++ names tm
namesDef (TyDecl _ ty) = names ty
namesDef (Operator ty _ _) = names ty
namesDef (CaseOp _ ty _ _ _ defs) = names ty ++ namesSC (snd (cases_compiletime defs))

findOccurs :: Name -> Idris [Name]
findOccurs n = do ctxt <- getContext
                  -- A definition calls a function if the function is in the type or RHS of the definition
                  let defs = (map fst . filter (\(n', def) -> n /= n' && occursDef n def) . ctxtAlist) ctxt
                  -- A datatype calls its
                  return defs

whoCalls :: Name -> Idris [(Name, [Name])]
whoCalls n = do ctxt <- getContext
                let names = lookupNames n ctxt
                    find nm = do ns <- findOccurs nm
                                 return (nm, nub ns)
                mapM find names

callsWho :: Name -> Idris [(Name, [Name])]
callsWho n = do ctxt <- getContext
                let defs = lookupNameDef n ctxt
                return $ map (\ (n, def) -> (n, nub $ namesDef def)) defs

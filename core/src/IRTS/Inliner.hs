{-|
Module      : IRTS.Inliner
Description : Inline expressions.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module IRTS.Inliner where

import Idris.Core.TT
import IRTS.Defunctionalise

inline :: DDefs -> DDefs
inline xs = let sep = toAlist xs
                inls = map (inl xs) sep in
                addAlist inls emptyContext

inl :: DDefs -> (Name, DDecl) -> (Name, DDecl)
inl ds d@(n, DFun n' args exp)
    = case evalD ds exp of
           Just exp' -> (n, DFun n' args exp')
           _ -> d
inl ds d = d

evalD _ e = ev e
  where
    ev e = Just e

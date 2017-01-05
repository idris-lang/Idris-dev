{-|
Module      : IRTS.Inliner
Description : Inline expressions.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module IRTS.Inliner(inline) where

import Idris.Core.TT
import IRTS.Defunctionalise

inline :: DDefs -> DDefs
inline xs = let sep = toAlist xs
                inls = map (inl xs) sep in
                addAlist inls emptyContext

inl :: DDefs -> (Name, DDecl) -> (Name, DDecl)
inl ds d@(n, DFun n' args body)
    = case evalD ds body of
           Just exp' -> (n, DFun n' args exp')
           _ -> d
  where
    evalD _ e = ev e
    ev e      = Just e
inl _  d = d

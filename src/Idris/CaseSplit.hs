{-# LANGUAGE PatternGuards #-}

module Idris.CaseSplit where

-- splitting a variable in a pattern clause

import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.ElabTerm
import Idris.Delaborate

import Core.TT

split :: Name -> PTerm -> Idris [PTerm]
split n t = do (tm, ty, pats) <- elabValBind toplevel True t
               ist <- getIState
               iputStrLn (show (delab ist tm) ++ " : " ++ show (delab ist ty))
               iputStrLn (show pats)
               return [t]

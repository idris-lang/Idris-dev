{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Value(elabVal, elabValBind) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.DSL
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Idris.ElabTerm
import Idris.Coverage
import Idris.DataOpts
import Idris.Providers
import Idris.Primitives
import Idris.Inliner
import Idris.PartialEval
import Idris.DeepSeq
import Idris.Output (iputStrLn, pshow, iWarn)
import IRTS.Lang

import Idris.Elab.Utils

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.Typecheck
import Idris.Core.CaseTree

import Idris.Docstrings

import Prelude hiding (id, (.))
import Control.Category

import Control.Applicative hiding (Const)
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import Data.List
import Data.Maybe
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Char(isLetter, toLower)
import Data.List.Split (splitOn)

import Util.Pretty(pretty, text)

-- Elaborate a value, returning any new bindings created (this will only
-- happen if elaborating as a pattern clause)
elabValBind :: ElabInfo -> ElabMode -> Bool -> PTerm -> Idris (Term, Type, [(Name, Type)])
elabValBind info aspat norm tm_in
   = do ctxt <- getContext
        i <- getIState
        let tm = addImpl i tm_in
        logLvl 10 (showTmImpls tm)
        -- try:
        --    * ordinary elaboration
        --    * elaboration as a Type
        --    * elaboration as a function a -> b

        ((tm', defer, is), _) <-
                tclift (elaborate ctxt (sMN 0 "val") infP []
                        (build i info aspat [Reflection] (sMN 0 "val") (infTerm tm)))
        let vtm = orderPats (getInferTerm tm')

        def' <- checkDef (fileFC "(input)") defer
        let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, True))) def'
        addDeferred def''
        mapM_ (elabCaseBlock info []) is

        logLvl 3 ("Value: " ++ show vtm)
        (vtm_in, vty) <- recheckC (fileFC "(input)") [] vtm

        let vtm = if norm then normalise (tt_ctxt i) [] vtm_in
                          else vtm_in
        let bargs = getPBtys vtm

        return (vtm, vty, bargs)

elabVal :: ElabInfo -> ElabMode -> PTerm -> Idris (Term, Type)
elabVal info aspat tm_in
   = do (tm, ty, _) <- elabValBind info aspat False tm_in
        return (tm, ty)



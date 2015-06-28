{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Elab.Value(elabVal, elabValBind, elabDocTerms, 
                        elabExec, elabREPL) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.DSL
import Idris.Error
import Idris.Delaborate
import Idris.Imports
import Idris.Coverage
import Idris.DataOpts
import Idris.Providers
import Idris.Primitives
import Idris.Inliner
import Idris.PartialEval
import Idris.DeepSeq
import Idris.Output (iputStrLn, pshow, iWarn, sendHighlighting)
import IRTS.Lang

import Idris.Elab.Utils
import Idris.Elab.Term

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate hiding (Unchecked)
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
import qualified Data.Traversable as Traversable
import Debug.Trace

import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Char(isLetter, toLower)
import Data.List.Split (splitOn)

import Util.Pretty(pretty, text)

-- | Elaborate a value, returning any new bindings created (this will only
-- happen if elaborating as a pattern clause)
elabValBind :: ElabInfo -> ElabMode -> Bool -> PTerm -> Idris (Term, Type, [(Name, Type)])
elabValBind info aspat norm tm_in
   = do ctxt <- getContext
        i <- getIState
        let tm = addImpl [] i tm_in
        logLvl 10 (showTmImpls tm)
        -- try:
        --    * ordinary elaboration
        --    * elaboration as a Type
        --    * elaboration as a function a -> b

        (ElabResult tm' defer is ctxt' newDecls highlights, _) <-
             tclift (elaborate ctxt (idris_datatypes i) (sMN 0 "val") infP initEState
                     (build i info aspat [Reflection] (sMN 0 "val") (infTerm tm)))

        -- Extend the context with new definitions created
        setContext ctxt'
        processTacticDecls info newDecls
        sendHighlighting highlights

        let vtm = orderPats (getInferTerm tm')

        def' <- checkDef (fileFC "(input)") iderr defer
        let def'' = map (\(n, (i, top, t)) -> (n, (i, top, t, True))) def'
        addDeferred def''
        mapM_ (elabCaseBlock info []) is

        logLvl 3 ("Value: " ++ show vtm)
        (vtm_in, vty) <- recheckC (fileFC "(input)") id [] vtm

        let vtm = if norm then normalise (tt_ctxt i) [] vtm_in
                          else vtm_in
        let bargs = getPBtys vtm

        return (vtm, vty, bargs)

elabVal :: ElabInfo -> ElabMode -> PTerm -> Idris (Term, Type)
elabVal info aspat tm_in
   = do (tm, ty, _) <- elabValBind info aspat False tm_in
        return (tm, ty)



elabDocTerms :: ElabInfo -> Docstring (Either Err PTerm) -> Idris (Docstring DocTerm)
elabDocTerms info str = do typechecked <- Traversable.mapM decorate str
                           return $ checkDocstring mkDocTerm typechecked
  where decorate (Left err) = return (Left err)
        decorate (Right pt) = fmap (fmap fst) (tryElabVal info ERHS pt)

        tryElabVal :: ElabInfo -> ElabMode -> PTerm -> Idris (Either Err (Term, Type))
        tryElabVal info aspat tm_in
           = idrisCatch (fmap Right $ elabVal info aspat tm_in)
                        (return . Left)

        mkDocTerm :: String -> [String] -> String -> Either Err Term -> DocTerm
        mkDocTerm lang attrs src (Left err)
          | map toLower lang == "idris" = Failing err
          | otherwise                   = Unchecked
        mkDocTerm lang attrs src (Right tm)
          | map toLower lang == "idris" = if "example" `elem` map (map toLower) attrs
                                            then Example tm
                                            else Checked tm
          | otherwise                   = Unchecked

-- | Try running the term directly (as IO ()), then printing it as an Integer
-- (as a default numeric tye), then printing it as any Showable thing
elabExec :: FC -> PTerm -> PTerm
elabExec fc tm = runtm (PAlternative FirstSuccess
                   [printtm (PApp fc (PRef fc (sUN "the"))
                     [pexp (PConstant NoFC (AType (ATInt ITBig))), pexp tm]),
                    tm,
                    printtm tm
                    ])
  where
    runtm t = PApp fc (PRef fc (sUN "run__IO")) [pexp t]
    printtm t = PApp fc (PRef fc (sUN "printLn"))
                  [pimp (sUN "ffi") (PRef fc (sUN "FFI_C")) False, pexp t]

elabREPL :: ElabInfo -> ElabMode -> PTerm -> Idris (Term, Type)
elabREPL info aspat tm
    = idrisCatch (elabVal info aspat tm) catchAmbig
  where
    catchAmbig (CantResolveAlts _)
       = elabVal info aspat (PDisamb [[txt "List"]] tm)
    catchAmbig e = ierror e

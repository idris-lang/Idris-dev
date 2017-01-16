{-|
Module      : Idris.Elab.Type
Description : Code to elaborate types.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Type (
    buildType, elabType, elabType'
  , elabPostulate, elabExtern
  ) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Core.CaseTree
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Core.WHNF
import Idris.Coverage
import Idris.DataOpts
import Idris.DeepSeq
import Idris.Delaborate
import Idris.Docstrings (Docstring)
import Idris.DSL
import Idris.Elab.Term
import Idris.Elab.Utils
import Idris.Elab.Value
import Idris.Error
import Idris.Imports
import Idris.Inliner
import Idris.Output (iWarn, iputStrLn, pshow, sendHighlighting)
import Idris.PartialEval
import Idris.Primitives
import Idris.Providers
import IRTS.Lang

import Util.Pretty (pretty, text)

import Prelude hiding (id, (.))

import Control.Applicative hiding (Const)
import Control.Category
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import Data.Char (isLetter, toLower)
import Data.List
import Data.List.Split (splitOn)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Traversable as Traversable
import Debug.Trace

buildType :: ElabInfo
          -> SyntaxInfo
          -> FC
          -> FnOpts
          -> Name
          -> PTerm
          -> Idris (Type, Type, PTerm, [(Int, Name)])
buildType info syn fc opts n ty' = do
         ctxt <- getContext
         i <- getIState

         logElab 2 $ show n ++ " pre-type " ++ showTmImpls ty' ++ show (no_imp syn)
         ty' <- addUsingConstraints syn fc ty'
         ty' <- addUsingImpls syn n fc ty'
         let ty = addImpl (imp_methods syn) i ty'

         logElab 5 $ show n ++ " type pre-addimpl " ++ showTmImpls ty'
         logElab 5 $ "with methods " ++ show (imp_methods syn)
         logElab 2 $ show n ++ " type " ++ show (using syn) ++ "\n" ++ showTmImpls ty

         ((ElabResult tyT' defer is ctxt' newDecls highlights newGName, est), log) <-
            tclift $ elaborate (constraintNS info) ctxt (idris_datatypes i) (idris_name i) n (TType (UVal 0)) initEState
                     (errAt "type of " n Nothing
                        (erunAux fc (build i info ETyDecl [] n ty)))

         displayWarnings est
         setContext ctxt'
         processTacticDecls info newDecls
         sendHighlighting highlights
         updateIState $ \i -> i { idris_name = newGName }

         let tyT = patToImp tyT'

         logElab 3 $ show ty ++ "\nElaborated: " ++ show tyT'

         ds <- checkAddDef True False info fc iderr True defer
         -- if the type is not complete, note that we'll need to infer
         -- things later (for solving metavariables)
         when (length ds > length is) -- more deferred than case blocks
              $ addTyInferred n

         mapM_ (elabCaseBlock info opts) is
         ctxt <- getContext
         logElab 5 "Rechecking"
         logElab 6 (show tyT)
         logElab 10 $ "Elaborated to " ++ showEnvDbg [] tyT
         (cty, ckind)   <- recheckC (constraintNS info) fc id [] tyT

         -- record the implicit and inaccessible arguments
         i <- getIState
         let (inaccData, impls) = unzip $ getUnboundImplicits i cty ty
         let inacc = inaccessibleImps 0 cty inaccData
         logElab 3 $ show n ++ ": inaccessible arguments: " ++ show inacc ++
                     " from " ++ show cty ++ "\n" ++ showTmImpls ty

         putIState $ i { idris_implicits = addDef n impls (idris_implicits i) }
         logElab 3 ("Implicit " ++ show n ++ " " ++ show impls)
         addIBC (IBCImp n)

         -- Add the names referenced to the call graph, and check we're not
         -- referring to anything less visible
         -- In particular, a public/export type can not refer to anything
         -- private, but can refer to any public/export
         let refs = freeNames cty
         nvis <- getFromHideList n
         case nvis of
              Nothing -> return ()
              Just acc -> mapM_ (checkVisibility fc n (max Frozen acc) acc) refs
         addCalls n refs
         addIBC (IBCCG n)

         when (Constructor `notElem` opts) $ do
             let pnames = getParamsInType i [] impls cty
             let fninfo = FnInfo (param_pos 0 pnames cty)
             setFnInfo n fninfo
             addIBC (IBCFnInfo n fninfo)

         -- If we use any types with linear constructor arguments, we'd better
         -- make sure they are use-once
         tcliftAt fc $ linearCheck ctxt (whnfArgs ctxt [] cty)

         return (cty, ckind, ty, inacc)
  where
    patToImp (Bind n (PVar rig t) sc) = Bind n (Pi rig Nothing t (TType (UVar [] 0))) (patToImp sc)
    patToImp (Bind n b sc) = Bind n b (patToImp sc)
    patToImp t = t

    param_pos i ns (Bind n (Pi _ _ t _) sc)
        | n `elem` ns = i : param_pos (i + 1) ns sc
        | otherwise = param_pos (i + 1) ns sc
    param_pos i ns t = []

-- | Elaborate a top-level type declaration - for example, "foo : Int -> Int".
elabType :: ElabInfo
         -> SyntaxInfo
         -> Docstring (Either Err PTerm)
         -> [(Name, Docstring (Either Err PTerm))]
         -> FC
         -> FnOpts
         -> Name
         -> FC -- ^ The precise location of the name
         -> PTerm
         -> Idris Type
elabType = elabType' False

elabType' :: Bool  -- normalise it
          -> ElabInfo
          -> SyntaxInfo
          -> Docstring (Either Err PTerm)
          -> [(Name, Docstring (Either Err PTerm))]
          -> FC
          -> FnOpts
          -> Name
          -> FC
          -> PTerm
          -> Idris Type
elabType' norm info syn doc argDocs fc opts n nfc ty' = {- let ty' = piBind (params info) ty_in
                                                       n  = liftname info n_in in    -}
      do checkUndefined fc n
         (cty, _, ty, inacc) <- buildType info syn fc opts n ty'

         addStatics n cty ty
         let nty = cty -- normalise ctxt [] cty
         -- if the return type is something coinductive, freeze the definition
         ctxt <- getContext
         logElab 2 $ "Rechecked to " ++ show nty
         let nty' = normalise ctxt [] nty
         logElab 2 $ "Rechecked to " ++ show nty'

         -- Add function name to internals (used for making :addclause know
         -- the name unambiguously)
         i <- getIState
         rep <- useREPL
         when rep $ do
           addInternalApp (fc_fname fc) (fst . fc_start $ fc) (PTyped (PRef fc [] n) ty') -- (mergeTy ty' (delab i nty')) -- TODO: Should use span instead of line and filename?
         addIBC (IBCLineApp (fc_fname fc) (fst . fc_start $ fc) (PTyped (PRef fc [] n) ty')) -- (mergeTy ty' (delab i nty')))

         let (fam, _) = unApply (getRetTy nty')
         let corec = case fam of
                        P _ rcty _ -> case lookupCtxt rcty (idris_datatypes i) of
                                        [TI _ True _ _ _ _] -> True
                                        _ -> False
                        _ -> False
         -- Productivity checking now via checking for guarded 'Delay'
         let opts' = opts -- if corec then (Coinductive : opts) else opts
         let usety = if norm then nty' else nty
         ds <- checkDef info fc iderr True [(n, (-1, Nothing, usety, []))]
         addIBC (IBCDef n)
         addDefinedName n
         let ds' = map (\(n, (i, top, fam, ns)) -> (n, (i, top, fam, ns, True, True))) ds
         addDeferred ds'
         setFlags n opts'
         checkDocs fc argDocs ty
         doc' <- elabDocTerms info doc
         argDocs' <- mapM (\(n, d) -> do d' <- elabDocTerms info d
                                         return (n, d')) argDocs
         addDocStr n doc' argDocs'
         addIBC (IBCDoc n)
         addIBC (IBCFlags n)
         fputState (opt_inaccessible . ist_optimisation n) inacc
         addIBC (IBCOpt n)
         when (Implicit `elem` opts') $ do addCoercion n
                                           addIBC (IBCCoercion n)
         when (AutoHint `elem` opts') $
             case fam of
                P _ tyn _ -> do addAutoHint tyn n
                                addIBC (IBCAutoHint tyn n)
                t -> ifail "Hints must return a data or record type"

         -- If the function is declared as an error handler and the language
         -- extension is enabled, then add it to the list of error handlers.
         errorReflection <- fmap (elem ErrorReflection . idris_language_extensions) getIState
         when (ErrorHandler `elem` opts) $ do
           if errorReflection
             then
               -- Check that the declared type is the correct type for an error handler:
               -- handler : List (TTName, TT) -> Err -> ErrorReport - for now no ctxt
               if tyIsHandler nty'
                 then do i <- getIState
                         putIState $ i { idris_errorhandlers = idris_errorhandlers i ++ [n] }
                         addIBC (IBCErrorHandler n)
                 else ifail $ "The type " ++ show nty' ++ " is invalid for an error handler"
             else ifail "Error handlers can only be defined when the ErrorReflection language extension is enabled."
         -- Send highlighting information about the name being declared
         sendHighlighting [(nfc, AnnName n Nothing Nothing Nothing)]
         -- if it's an export list type, make a note of it
         case (unApply usety) of
              (P _ ut _, _)
                 | ut == ffiexport -> do addIBC (IBCExport n)
                                         addExport n
              _ -> return ()
         return usety
  where
    -- for making an internalapp, we only want the explicit ones, and don't
    -- want the parameters, so just take the arguments which correspond to the
    -- user declared explicit ones
    mergeTy (PPi e n fc ty sc) (PPi e' n' _ _ sc')
         | e == e' = PPi e n fc ty (mergeTy sc sc')
         | otherwise = mergeTy sc sc'
    mergeTy _ sc = sc

    ffiexport = sNS (sUN "FFI_Export") ["FFI_Export"]

    err = txt "Err"
    maybe = txt "Maybe"
    lst = txt "List"
    errrep = txt "ErrorReportPart"

    tyIsHandler (Bind _ (Pi _ _ (P _ (NS (UN e) ns1) _) _)
                        (App _ (P _ (NS (UN m) ns2) _)
                             (App _ (P _ (NS (UN l) ns3) _)
                                  (P _ (NS (UN r) ns4) _))))
        | e == err && m == maybe && l == lst && r == errrep
        , ns1 == map txt ["Errors","Reflection","Language"]
        , ns2 == map txt ["Maybe", "Prelude"]
        , ns3 == map txt ["List", "Prelude"]
        , ns4 == map txt ["Reflection","Language"] = True
    tyIsHandler _                                           = False

elabPostulate :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm) ->
                 FC -> FC -> FnOpts -> Name -> PTerm -> Idris ()
elabPostulate info syn doc fc nfc opts n ty = do
    elabType info syn doc [] fc opts n NoFC ty
    putIState . (\ist -> ist{ idris_postulates = S.insert n (idris_postulates ist) }) =<< getIState
    addIBC (IBCPostulate n)
    sendHighlighting [(nfc, AnnName n (Just PostulateOutput) Nothing Nothing)]

    -- remove it from the deferred definitions list
    solveDeferred fc n

elabExtern :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm) ->
                 FC -> FC -> FnOpts -> Name -> PTerm -> Idris ()
elabExtern info syn doc fc nfc opts n ty = do
    cty <- elabType info syn doc [] fc opts n NoFC ty
    ist <- getIState
    let arity = length (getArgTys (normalise (tt_ctxt ist) [] cty))

    putIState . (\ist -> ist{ idris_externs = S.insert (n, arity) (idris_externs ist) }) =<< getIState
    addIBC (IBCExtern (n, arity))

    -- remove it from the deferred definitions list
    solveDeferred fc n

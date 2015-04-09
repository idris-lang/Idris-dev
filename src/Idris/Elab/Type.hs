{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Type (buildType, elabType, elabType', 
                        elabPostulate, elabExtern) where

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
import Idris.Elab.Value

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.Typecheck
import Idris.Core.CaseTree

import Idris.Docstrings (Docstring)

import Prelude hiding (id, (.))
import Control.Category

import Control.Applicative hiding (Const)
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict as State
import Data.List
import Data.Maybe
import Debug.Trace

import qualified Data.Traversable as Traversable

import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Char(isLetter, toLower)
import Data.List.Split (splitOn)

import Util.Pretty(pretty, text)

buildType :: ElabInfo -> SyntaxInfo -> FC -> FnOpts -> Name -> PTerm -> 
             Idris (Type, Type, PTerm, [(Int, Name)])
buildType info syn fc opts n ty' = do
         ctxt <- getContext
         i <- getIState

         logLvl 2 $ show n ++ " pre-type " ++ showTmImpls ty' ++ show (no_imp syn)
         ty' <- addUsingConstraints syn fc ty'
         ty' <- addUsingImpls syn n fc ty'
         let ty = addImpl (imp_methods syn) i ty'

         logLvl 5 $ show n ++ " type pre-addimpl " ++ showTmImpls ty'
         logLvl 2 $ show n ++ " type " ++ show (using syn) ++ "\n" ++ showTmImpls ty

         (ElabResult tyT' defer is ctxt' newDecls, log) <-
            tclift $ elaborate ctxt n (TType (UVal 0)) initEState
                     (errAt "type of " n (erun fc (build i info ETyDecl [] n ty)))
         setContext ctxt'
         processTacticDecls newDecls

         let tyT = patToImp tyT'

         logLvl 3 $ show ty ++ "\nElaborated: " ++ show tyT'

         ds <- checkAddDef True False fc iderr defer
         -- if the type is not complete, note that we'll need to infer
         -- things later (for solving metavariables)
         when (not (null ds)) $ addTyInferred n

         mapM_ (elabCaseBlock info opts) is
         ctxt <- getContext
         logLvl 5 $ "Rechecking"
         logLvl 6 $ show tyT
         logLvl 10 $ "Elaborated to " ++ showEnvDbg [] tyT
         (cty, ckind)   <- recheckC fc id [] tyT

         -- record the implicit and inaccessible arguments
         i <- getIState
         let (inaccData, impls) = unzip $ getUnboundImplicits i cty ty
         let inacc = inaccessibleImps 0 cty inaccData
         logLvl 3 $ show n ++ ": inaccessible arguments: " ++ show inacc ++
                     " from " ++ show cty ++ "\n" ++ showTmImpls ty

         putIState $ i { idris_implicits = addDef n impls (idris_implicits i) }
         logLvl 3 ("Implicit " ++ show n ++ " " ++ show impls)
         addIBC (IBCImp n)

         when (Constructor `notElem` opts) $ do
             let pnames = getParamsInType i [] impls cty
             let fninfo = FnInfo (param_pos 0 pnames cty)
             setFnInfo n fninfo
             addIBC (IBCFnInfo n fninfo)

         return (cty, ckind, ty, inacc)
  where
    patToImp (Bind n (PVar t) sc) = Bind n (Pi Nothing t (TType (UVar 0))) (patToImp sc)
    patToImp (Bind n b sc) = Bind n b (patToImp sc)
    patToImp t = t

    param_pos i ns (Bind n (Pi _ t _) sc) 
        | n `elem` ns = i : param_pos (i + 1) ns sc
        | otherwise = param_pos (i + 1) ns sc
    param_pos i ns t = []

-- | Elaborate a top-level type declaration - for example, "foo : Int -> Int".
elabType :: ElabInfo -> SyntaxInfo
         -> Docstring (Either Err PTerm) -> [(Name, Docstring (Either Err PTerm))]
         -> FC -> FnOpts -> Name -> PTerm -> Idris Type
elabType = elabType' False

elabType' :: Bool -> -- normalise it
             ElabInfo -> SyntaxInfo ->
             Docstring (Either Err PTerm) -> [(Name, Docstring (Either Err PTerm))] ->
             FC -> FnOpts -> Name -> PTerm -> Idris Type
elabType' norm info syn doc argDocs fc opts n ty' = {- let ty' = piBind (params info) ty_in
                                                       n  = liftname info n_in in    -}
      do checkUndefined fc n
         (cty, _, ty, inacc) <- buildType info syn fc opts n ty'

         addStatics n cty ty
         let nty = cty -- normalise ctxt [] cty
         -- if the return type is something coinductive, freeze the definition
         ctxt <- getContext
         logLvl 2 $ "Rechecked to " ++ show nty
         let nty' = normalise ctxt [] nty
         logLvl 2 $ "Rechecked to " ++ show nty'

         -- Add normalised type to internals
         i <- getIState
         rep <- useREPL
         when rep $ do
           addInternalApp (fc_fname fc) (fst . fc_start $ fc) ty' -- (mergeTy ty' (delab i nty')) -- TODO: Should use span instead of line and filename?
           addIBC (IBCLineApp (fc_fname fc) (fst . fc_start $ fc) ty') -- (mergeTy ty' (delab i nty')))

         let (fam, _) = unApply (getRetTy nty')
         let corec = case fam of
                        P _ rcty _ -> case lookupCtxt rcty (idris_datatypes i) of
                                        [TI _ True _ _ _] -> True
                                        _ -> False
                        _ -> False
         -- Productivity checking now via checking for guarded 'Delay' 
         let opts' = opts -- if corec then (Coinductive : opts) else opts
         let usety = if norm then nty' else nty
         ds <- checkDef fc iderr [(n, (-1, Nothing, usety))]
         addIBC (IBCDef n)
         let ds' = map (\(n, (i, top, fam)) -> (n, (i, top, fam, True))) ds
         addDeferred ds'
         setFlags n opts'
         checkDocs fc argDocs ty
         doc' <- elabDocTerms info doc
         argDocs' <- mapM (\(n, d) -> do d' <- elabDocTerms info d
                                         return (n, d')) argDocs
         addDocStr n doc' argDocs'
         addIBC (IBCDoc n)
         addIBC (IBCFlags n opts')
         fput (opt_inaccessible . ist_optimisation n) inacc
         addIBC (IBCOpt n)
         when (Implicit `elem` opts') $ do addCoercion n
                                           addIBC (IBCCoercion n)
         when (AutoHint `elem` opts') $ 
             case fam of
                P _ tyn _ -> do addAutoHint tyn n
                                addIBC (IBCAutoHint tyn n)
                t -> ifail $ "Hints must return a data or record type"

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
    mergeTy (PPi e n ty sc) (PPi e' n' _ sc')
         | e == e' = PPi e n ty (mergeTy sc sc')
         | otherwise = mergeTy sc sc'
    mergeTy _ sc = sc

    ffiexport = sNS (sUN "FFI_Export") ["FFI_Export"]

    err = txt "Err"
    maybe = txt "Maybe"
    lst = txt "List"
    errrep = txt "ErrorReportPart"

    tyIsHandler (Bind _ (Pi _ (P _ (NS (UN e) ns1) _) _)
                        (App (P _ (NS (UN m) ns2) _)
                             (App (P _ (NS (UN l) ns3) _)
                                  (P _ (NS (UN r) ns4) _))))
        | e == err && m == maybe && l == lst && r == errrep
        , ns1 == map txt ["Errors","Reflection","Language"]
        , ns2 == map txt ["Maybe", "Prelude"]
        , ns3 == map txt ["List", "Prelude"]
        , ns4 == map txt ["Reflection","Language"] = True
    tyIsHandler _                                           = False

elabPostulate :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm) ->
                 FC -> FnOpts -> Name -> PTerm -> Idris ()
elabPostulate info syn doc fc opts n ty = do
    elabType info syn doc [] fc opts n ty
    putIState . (\ist -> ist{ idris_postulates = S.insert n (idris_postulates ist) }) =<< getIState
    addIBC (IBCPostulate n)

    -- remove it from the deferred definitions list
    solveDeferred n

elabExtern :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm) ->
                 FC -> FnOpts -> Name -> PTerm -> Idris ()
elabExtern info syn doc fc opts n ty = do
    cty <- elabType info syn doc [] fc opts n ty
    ist <- getIState
    let arity = length (getArgTys (normalise (tt_ctxt ist) [] cty))

    putIState . (\ist -> ist{ idris_externs = S.insert (n, arity) (idris_externs ist) }) =<< getIState
    addIBC (IBCExtern (n, arity))

    -- remove it from the deferred definitions list
    solveDeferred n




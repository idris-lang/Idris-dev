{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Instance(elabInstance) where

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

import Idris.Elab.Type
import Idris.Elab.Data
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

elabInstance :: ElabInfo -> SyntaxInfo ->
                Docstring (Either Err PTerm) ->
                [(Name, Docstring (Either Err PTerm))] ->
                ElabWhat -> -- phase
                FC -> [(Name, PTerm)] -> -- constraints
                Name -> -- the class
                [PTerm] -> -- class parameters (i.e. instance)
                PTerm -> -- full instance type
                Maybe Name -> -- explicit name
                [PDecl] -> Idris ()
elabInstance info syn doc argDocs what fc cs n ps t expn ds = do
    i <- getIState
    (n, ci) <- case lookupCtxtName n (idris_classes i) of
                  [c] -> return c
                  [] -> ifail $ show fc ++ ":" ++ show n ++ " is not a type class"
                  cs -> tclift $ tfail $ At fc
                           (CantResolveAlts (map fst cs))
    let constraint = PApp fc (PRef fc n) (map pexp ps)
    let iname = mkiname n (namespace info) ps expn
    let emptyclass = null (class_methods ci)
    when (what /= EDefns || (null ds && not emptyclass)) $ do
         nty <- elabType' True info syn doc argDocs fc [] iname t
         -- if the instance type matches any of the instances we have already,
         -- and it's not a named instance, then it's overlapping, so report an error
         case expn of
            Nothing -> do mapM_ (maybe (return ()) overlapping . findOverlapping i (class_determiners ci) (delab i nty))
                                (class_instances ci)
                          addInstance intInst n iname
            Just _ -> addInstance intInst n iname
    when (what /= ETypes && (not (null ds && not emptyclass))) $ do
         let ips = zip (class_params ci) ps
         let ns = case n of
                    NS n ns' -> ns'
                    _ -> []
         -- get the implicit parameters that need passing through to the
         -- where block
         wparams <- mapM (\p -> case p of
                                  PApp _ _ args -> getWParams (map getTm args)
                                  _ -> return []) ps
         let pnames = map pname (concat (nub wparams))
         let superclassInstances = map (substInstance ips pnames) (class_default_superclasses ci)
         undefinedSuperclassInstances <- filterM (fmap not . isOverlapping i) superclassInstances
         mapM_ (rec_elabDecl info EAll info) undefinedSuperclassInstances
         let all_meths = map (nsroot . fst) (class_methods ci)
         let mtys = map (\ (n, (op, t)) ->
                   let t_in = substMatchesShadow ips pnames t
                       mnamemap = map (\n -> (n, PRef fc (decorate ns iname n)))
                                      all_meths
                       t' = substMatchesShadow mnamemap pnames t_in in
                       (decorate ns iname n,
                           op, coninsert cs t', t'))
              (class_methods ci)
         logLvl 3 (show (mtys, ips))
         let ds' = insertDefaults i iname (class_defaults ci) ns ds
         iLOG ("Defaults inserted: " ++ show ds' ++ "\n" ++ show ci)
         mapM_ (warnMissing ds' ns iname) (map fst (class_methods ci))
         mapM_ (checkInClass (map fst (class_methods ci))) (concatMap defined ds')
         let wbTys = map mkTyDecl mtys
         let wbVals = map (decorateid (decorate ns iname)) ds'
         let wb = wbTys ++ wbVals
         logLvl 3 $ "Method types " ++ showSep "\n" (map (show . showDeclImp verbosePPOption . mkTyDecl) mtys)
         logLvl 3 $ "Instance is " ++ show ps ++ " implicits " ++
                                      show (concat (nub wparams))

         -- Bring variables in instance head into scope
         ist <- getIState
         let headVars = nub $ mapMaybe (\p -> case p of
                                               PRef _ n ->
                                                  case lookupTy n (tt_ctxt ist) of
                                                      [] -> Just n
                                                      _ -> Nothing
                                               _ -> Nothing) ps
--          let lhs = PRef fc iname
         let lhs = PApp fc (PRef fc iname)
                           (map (\n -> pimp n (PRef fc n) True) headVars)
         let rhs = PApp fc (PRef fc (instanceName ci))
                           (map (pexp . mkMethApp) mtys)

         logLvl 5 $ "Instance LHS " ++ show lhs ++ " " ++ show headVars
         logLvl 5 $ "Instance RHS " ++ show rhs

         let idecls = [PClauses fc [Dictionary] iname
                                 [PClause fc iname lhs [] rhs wb]]
         iLOG (show idecls)
         mapM_ (rec_elabDecl info EAll info) idecls
         addIBC (IBCInstance intInst n iname)

  where
    intInst = case ps of
                [PConstant (AType (ATInt ITNative))] -> True
                _ -> False

    mkiname n' ns ps' expn' =
        case expn' of
          Nothing -> case ns of
                          Nothing -> SN (sInstanceN n' (map show ps'))
                          Just m -> sNS (SN (sInstanceN n' (map show ps'))) m
          Just nm -> nm

    substInstance ips pnames (PInstance doc argDocs syn _ cs n ps t expn ds)
        = PInstance doc argDocs syn fc cs n (map (substMatchesShadow ips pnames) ps) (substMatchesShadow ips pnames t) expn ds

    isOverlapping i (PInstance doc argDocs syn _ _ n ps t expn _)
        = case lookupCtxtName n (idris_classes i) of
            [(n, ci)] -> let iname = (mkiname n (namespace info) ps expn) in
                            case lookupTy iname (tt_ctxt i) of
                              [] -> elabFindOverlapping i ci iname syn t
                              (_:_) -> return True
            _ -> return False -- couldn't find class, just let elabInstance fail later

    -- TODO: largely based upon elabType' - should try to abstract
    -- Issue #1614 in the issue tracker:
    --    https://github.com/idris-lang/Idris-dev/issues/1614
    elabFindOverlapping i ci iname syn t
        = do ty' <- addUsingConstraints syn fc t
             -- TODO think: something more in info?
             ty' <- implicit info syn iname ty'
             let ty = addImpl i ty'
             ctxt <- getContext
             (ElabResult tyT _ _ ctxt' newDecls, _) <-
                tclift $ elaborate ctxt iname (TType (UVal 0)) initEState
                         (errAt "type of " iname (erun fc (build i info ERHS [] iname ty)))
             setContext ctxt'
             processTacticDecls newDecls
             ctxt <- getContext
             (cty, _) <- recheckC fc [] tyT
             let nty = normalise ctxt [] cty
             return $ any (isJust . findOverlapping i (class_determiners ci) (delab i nty)) (class_instances ci)

    findOverlapping i dets t n
     | take 2 (show n) == "@@" = Nothing
     | otherwise
        = case lookupTy n (tt_ctxt i) of
            [t'] -> let tret = getRetType t
                        tret' = getRetType (delab i t') in
                        case matchArgs i dets tret' tret of
                           Right _ -> Just tret'
                           Left _ -> case matchArgs i dets tret tret' of
                                       Right _ -> Just tret'
                                       Left _ -> Nothing
            _ -> Nothing
    overlapping t' = tclift $ tfail (At fc (Msg $
                          "Overlapping instance: " ++ show t' ++ " already defined"))
    getRetType (PPi _ _ _ sc) = getRetType sc
    getRetType t = t

    matchArgs i dets x y =
        let x' = keepDets dets x
            y' = keepDets dets y in
            matchClause i x' y'

    keepDets dets (PApp fc f args)
        = PApp fc f $ let a' = zip [0..] args in
              map snd (filter (\(i, _) -> i `elem` dets) a')
    keepDets dets t = t

    mkMethApp (n, _, _, ty)
          = lamBind 0 ty (papp fc (PRef fc n) (methArgs 0 ty))
    lamBind i (PPi (Constraint _ _) _ _ sc) sc'
          = PLam fc (sMN i "meth") Placeholder (lamBind (i+1) sc sc')
    lamBind i (PPi _ n ty sc) sc'
          = PLam fc (sMN i "meth") Placeholder (lamBind (i+1) sc sc')
    lamBind i _ sc = sc
    methArgs i (PPi (Imp _ _ _ _) n ty sc)
        = PImp 0 True [] n (PRef fc (sMN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Exp _ _ _) n ty sc)
        = PExp 0 [] (sMN 0 "marg") (PRef fc (sMN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Constraint _ _) n ty sc)
        = PConstraint 0 [] (sMN 0 "marg") (PResolveTC fc) : methArgs (i+1) sc
    methArgs i _ = []

    papp fc f [] = f
    papp fc f as = PApp fc f as

    getWParams [] = return []
    getWParams (p : ps)
      | PRef _ n <- p
        = do ps' <- getWParams ps
             ctxt <- getContext
             case lookupP n ctxt of
                [] -> return (pimp n (PRef fc n) True : ps')
                _ -> return ps'
    getWParams (_ : ps) = getWParams ps

    decorate ns iname (UN n)        = NS (SN (MethodN (UN n))) ns
    decorate ns iname (NS (UN n) s) = NS (SN (MethodN (UN n))) ns

    mkTyDecl (n, op, t, _) = PTy emptyDocstring [] syn fc op n t

    conbind :: [(Name, PTerm)] -> PTerm -> PTerm
    conbind ((c,ty) : ns) x = PPi constraint c ty (conbind ns x)
    conbind [] x = x

    coninsert :: [(Name, PTerm)] -> PTerm -> PTerm
    coninsert cs (PPi p@(Imp _ _ _ _) n t sc) = PPi p n t (coninsert cs sc)
    coninsert cs sc = conbind cs sc

    insertDefaults :: IState -> Name ->
                      [(Name, (Name, PDecl))] -> [T.Text] ->
                      [PDecl] -> [PDecl]
    insertDefaults i iname [] ns ds = ds
    insertDefaults i iname ((n,(dn, clauses)) : defs) ns ds
       = insertDefaults i iname defs ns (insertDef i n dn clauses ns iname ds)

    insertDef i meth def clauses ns iname decls
        | null $ filter (clauseFor meth iname ns) decls
            = let newd = expandParamsD False i (\n -> meth) [] [def] clauses in
                  -- trace (show newd) $
                  decls ++ [newd]
        | otherwise = decls

    warnMissing decls ns iname meth
        | null $ filter (clauseFor meth iname ns) decls
            = iWarn fc . text $ "method " ++ show meth ++ " not defined"
        | otherwise = return ()

    checkInClass ns meth
        | not (null (filter (eqRoot meth) ns)) = return ()
        | otherwise = tclift $ tfail (At fc (Msg $
                                show meth ++ " not a method of class " ++ show n))

    eqRoot x y = nsroot x == nsroot y

    clauseFor m iname ns (PClauses _ _ m' _)
       = decorate ns iname m == decorate ns iname m'
    clauseFor m iname ns _ = False

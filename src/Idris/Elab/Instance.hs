{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Instance(elabInstance) where

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

import Idris.Elab.Type
import Idris.Elab.Data
import Idris.Elab.Utils
import Idris.Elab.Term

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
                Accessibility ->
                Name -> -- the class
                FC -> -- precise location of class name
                [PTerm] -> -- class parameters (i.e. instance)
                PTerm -> -- full instance type
                Maybe Name -> -- explicit name
                [PDecl] -> Idris ()
elabInstance info syn doc argDocs what fc cs acc n nfc ps t expn ds = do
    i <- getIState
    (n, ci) <- case lookupCtxtName n (idris_classes i) of
                  [c] -> return c
                  [] -> ifail $ show fc ++ ":" ++ show n ++ " is not a type class"
                  cs -> tclift $ tfail $ At fc
                           (CantResolveAlts (map fst cs))
    let constraint = PApp fc (PRef fc [] n) (map pexp ps)
    let iname = mkiname n (namespace info) ps expn
    putIState (i { hide_list = addDef iname acc (hide_list i) })
    i <- getIState

    let emptyclass = null (class_methods ci)
    when (what /= EDefns) $ do
         nty <- elabType' True info syn doc argDocs fc [] iname NoFC t
         -- if the instance type matches any of the instances we have already,
         -- and it's not a named instance, then it's overlapping, so report an error
         case expn of
            Nothing -> do mapM_ (maybe (return ()) overlapping . findOverlapping i (class_determiners ci) (delab i nty))
                                (map fst $ class_instances ci)
                          addInstance intInst True n iname
            Just _ -> addInstance intInst False n iname
    when (what /= ETypes && (not (null ds && not emptyclass))) $ do
         let ips = zip (class_params ci) ps
         let ns = case n of
                    NS n ns' -> ns'
                    _ -> []
         -- get the implicit parameters that need passing through to the
         -- where block
         wparams <- mapM (\p -> case p of
                                  PApp _ _ args -> getWParams (map getTm args)
                                  a@(PRef fc _ f) -> getWParams [a]
                                  _ -> return []) ps
         ist <- getIState
         let pnames = nub $ map pname (concat (nub wparams)) ++
                          concatMap (namesIn [] ist) ps
         let superclassInstances = map (substInstance ips pnames) (class_default_superclasses ci)
         undefinedSuperclassInstances <- filterM (fmap not . isOverlapping i) superclassInstances
         mapM_ (rec_elabDecl info EAll info) undefinedSuperclassInstances
         let all_meths = map (nsroot . fst) (class_methods ci)
         let mtys = map (\ (n, (op, t)) ->
                   let t_in = substMatchesShadow ips pnames t
                       mnamemap = map (\n -> (n, PRef fc [] (decorate ns iname n)))
                                      all_meths
                       t' = substMatchesShadow mnamemap pnames t_in in
                       (decorate ns iname n,
                           op, coninsert cs t', t'))
              (class_methods ci)
         logElab 3 (show (mtys, ips))
         logElab 5 ("Before defaults: " ++ show ds ++ "\n" ++ show (map fst (class_methods ci)))
         let ds_defs = insertDefaults i iname (class_defaults ci) ns ds
         logElab 3 ("After defaults: " ++ show ds_defs ++ "\n")
         let ds' = reorderDefs (map fst (class_methods ci)) $ ds_defs
         logElab 1 ("Reordered: " ++ show ds' ++ "\n")
         mapM_ (warnMissing ds' ns iname) (map fst (class_methods ci))
         mapM_ (checkInClass (map fst (class_methods ci))) (concatMap defined ds')
         let wbTys = map mkTyDecl mtys
         let wbVals = map (decorateid (decorate ns iname)) ds'
         let wb = wbTys ++ wbVals
         logElab 3 $ "Method types " ++ showSep "\n" (map (show . showDeclImp verbosePPOption . mkTyDecl) mtys)
         logElab 3 $ "Instance is " ++ show ps ++ " implicits " ++
                                      show (concat (nub wparams))

         -- Bring variables in instance head into scope
         let headVars = nub $ mapMaybe (\p -> case p of
                                               PRef _ _ n ->
                                                  case lookupTy n (tt_ctxt ist) of
                                                      [] -> Just n
                                                      _ -> Nothing
                                               _ -> Nothing) ps
--          let lhs = PRef fc iname
         let lhs = PApp fc (PRef fc [] iname)
                           (map (\n -> pimp n (PRef fc [] n) True) headVars)
         let rhs = PApp fc (PRef fc [] (instanceCtorName ci))
                           (map (pexp . mkMethApp) mtys)

         logElab 5 $ "Instance LHS " ++ show lhs ++ " " ++ show headVars
         logElab 5 $ "Instance RHS " ++ show rhs

         let idecls = [PClauses fc [Dictionary] iname
                                 [PClause fc iname lhs [] rhs wb]]
         logElab 1 (show idecls)
         push_estack iname True
         mapM_ (rec_elabDecl info EAll info) idecls
         pop_estack
         ist <- getIState
         checkInjectiveArgs fc n (class_determiners ci) (lookupTyExact iname (tt_ctxt ist))
         addIBC (IBCInstance intInst (isNothing expn) n iname)

  where
    intInst = case ps of
                [PConstant NoFC (AType (ATInt ITNative))] -> True
                _ -> False

    mkiname n' ns ps' expn' =
        case expn' of
          Nothing -> case ns of
                          Nothing -> SN (sInstanceN n' (map show ps'))
                          Just m -> sNS (SN (sInstanceN n' (map show ps'))) m
          Just nm -> nm

    substInstance ips pnames (PInstance doc argDocs syn _ cs acc n nfc ps t expn ds)
        = PInstance doc argDocs syn fc cs acc n nfc (map (substMatchesShadow ips pnames) ps) (substMatchesShadow ips pnames t) expn ds

    isOverlapping i (PInstance doc argDocs syn _ _ _ n nfc ps t expn _)
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
             let ty = addImpl [] i ty'
             ctxt <- getContext
             (ElabResult tyT _ _ ctxt' newDecls highlights, _) <-
                tclift $ elaborate ctxt (idris_datatypes i) iname (TType (UVal 0)) initEState
                         (errAt "type of " iname Nothing (erun fc (build i info ERHS [] iname ty)))
             setContext ctxt'
             processTacticDecls info newDecls
             sendHighlighting highlights
             ctxt <- getContext
             (cty, _) <- recheckC fc id [] tyT
             let nty = normalise ctxt [] cty
             return $ any (isJust . findOverlapping i (class_determiners ci) (delab i nty)) (map fst $ class_instances ci)

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
                          "Overlapping implementation: " ++ show t' ++ " already defined"))
    getRetType (PPi _ _ _ _ sc) = getRetType sc
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
          = lamBind 0 ty (papp fc (PRef fc [] n) (methArgs 0 ty))
    lamBind i (PPi (Constraint _ _) _ _ _ sc) sc'
          = PLam fc (sMN i "meth") NoFC Placeholder (lamBind (i+1) sc sc')
    lamBind i (PPi _ n _ ty sc) sc'
          = PLam fc (sMN i "meth") NoFC Placeholder (lamBind (i+1) sc sc')
    lamBind i _ sc = sc
    methArgs i (PPi (Imp _ _ _ _) n _ ty sc)
        = PImp 0 True [] n (PRef fc [] (sMN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Exp _ _ _) n _ ty sc)
        = PExp 0 [] (sMN 0 "marg") (PRef fc [] (sMN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Constraint _ _) n _ ty sc)
        = PConstraint 0 [] (sMN 0 "marg") (PResolveTC fc) : methArgs (i+1) sc
    methArgs i _ = []

    papp fc f [] = f
    papp fc f as = PApp fc f as

    getWParams [] = return []
    getWParams (p : ps)
      | PRef _ _ n <- p
        = do ps' <- getWParams ps
             ctxt <- getContext
             case lookupP n ctxt of
                [] -> return (pimp n (PRef fc [] n) True : ps')
                _ -> return ps'
    getWParams (_ : ps) = getWParams ps

    decorate ns iname (UN n)        = NS (SN (MethodN (UN n))) ns
    decorate ns iname (NS (UN n) s) = NS (SN (MethodN (UN n))) ns

    mkTyDecl (n, op, t, _)
        = PTy emptyDocstring [] syn fc op n NoFC
               (mkUniqueNames [] [] t)

    conbind :: [(Name, PTerm)] -> PTerm -> PTerm
    conbind ((c,ty) : ns) x = PPi constraint c NoFC ty (conbind ns x)
    conbind [] x = x

    coninsert :: [(Name, PTerm)] -> PTerm -> PTerm
    coninsert cs (PPi p@(Imp _ _ _ _) n fc t sc) = PPi p n fc t (coninsert cs sc)
    coninsert cs sc = conbind cs sc

    -- Reorder declarations to be in the same order as defined in the
    -- class declaration (important so that we insert default definitions
    -- in the right place, and so that dependencies between methods are
    -- respected)
    reorderDefs :: [Name] -> [PDecl] -> [PDecl]
    reorderDefs ns [] = []
    reorderDefs [] ds = ds
    reorderDefs (n : ns) ds = case pick n [] ds of
                                  Just (def, ds') -> def : reorderDefs ns ds'
                                  Nothing -> reorderDefs ns ds

    pick n acc [] = Nothing
    pick n acc (def@(PClauses _ _ cn cs) : ds)
         | nsroot n == nsroot cn = Just (def, acc ++ ds)
    pick n acc (d : ds) = pick n (acc ++ [d]) ds

    insertDefaults :: IState -> Name ->
                      [(Name, (Name, PDecl))] -> [T.Text] ->
                      [PDecl] -> [PDecl]
    insertDefaults i iname [] ns ds = ds
    insertDefaults i iname ((n,(dn, clauses)) : defs) ns ds
       = insertDefaults i iname defs ns (insertDef i n dn clauses ns iname ds)

    insertDef i meth def clauses ns iname decls
        | not $ any (clauseFor meth iname ns) decls
            = let newd = expandParamsD False i (\n -> meth) [] [def] clauses in
                  -- trace (show newd) $
                  decls ++ [newd]
        | otherwise = decls

    warnMissing decls ns iname meth
        | not $ any (clauseFor meth iname ns) decls
            = iWarn fc . text $ "method " ++ show meth ++ " not defined"
        | otherwise = return ()

    checkInClass ns meth
        | any (eqRoot meth) ns = return ()
        | otherwise = tclift $ tfail (At fc (Msg $
                                show meth ++ " not a method of class " ++ show n))

    eqRoot x y = nsroot x == nsroot y

    clauseFor m iname ns (PClauses _ _ m' _)
       = decorate ns iname m == decorate ns iname m'
    clauseFor m iname ns _ = False

checkInjectiveArgs :: FC -> Name -> [Int] -> Maybe Type -> Idris ()
checkInjectiveArgs fc n ds Nothing = return ()
checkInjectiveArgs fc n ds (Just ty)
   = do ist <- getIState
        let (_, args) = unApply (instantiateRetTy ty)
        ci 0 ist args
  where
    ci i ist (a : as) | i `elem` ds
       = if isInj ist a then ci (i + 1) ist as
            else tclift $ tfail (At fc (InvalidTCArg n a))
    ci i ist (a : as) = ci (i + 1) ist as
    ci i ist [] = return ()

    isInj i (P Bound n _) = True
    isInj i (P _ n _) = isConName n (tt_ctxt i)
    isInj i (App _ f a) = isInj i f && isInj i a
    isInj i (V _) = True
    isInj i (Bind n b sc) = isInj i sc
    isInj _ _ = True

    instantiateRetTy (Bind n (Pi _ _ _) sc)
       = substV (P Bound n Erased) (instantiateRetTy sc)
    instantiateRetTy t = t

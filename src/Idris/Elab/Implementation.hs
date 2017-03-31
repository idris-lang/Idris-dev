{-|
Module      : Idris.Elab.Implementation
Description : Code to elaborate instances.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Implementation(elabImplementation) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Core.CaseTree
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Coverage
import Idris.DataOpts
import Idris.DeepSeq
import Idris.Delaborate
import Idris.Docstrings
import Idris.DSL
import Idris.Elab.Data
import Idris.Elab.Term
import Idris.Elab.Type
import Idris.Elab.Utils
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
import Debug.Trace


elabImplementation :: ElabInfo
                   -> SyntaxInfo
                   -> Docstring (Either Err PTerm)
                   -> [(Name, Docstring (Either Err PTerm))]
                   -> ElabWhat        -- ^ phase
                   -> FC
                   -> [(Name, PTerm)] -- ^ constraints
                   -> [Name]          -- ^ parent dictionary names (optionally)
                   -> Accessibility
                   -> FnOpts
                   -> Name            -- ^ the interface
                   -> FC              -- ^ precise location of interface name
                   -> [PTerm]         -- ^ interface parameters (i.e. implementation)
                   -> [(Name, PTerm)] -- ^ Extra arguments in scope (e.g. implementation in where block)
                   -> PTerm           -- ^ full implementation type
                   -> Maybe Name      -- ^ explicit name
                   -> [PDecl]
                   -> Idris ()
elabImplementation info syn doc argDocs what fc cs parents acc opts n nfc ps pextra t expn ds = do
    ist <- getIState
    (n, ci) <- case lookupCtxtName n (idris_interfaces ist) of
                  [c] -> return c
                  [] -> ifail $ show fc ++ ":" ++ show n ++ " is not an interface"
                  cs -> tclift $ tfail $ At fc
                           (CantResolveAlts (map fst cs))
    let constraint = PApp fc (PRef fc [] n) (map pexp ps)
    let iname = mkiname n (namespace info) ps expn
    putIState (ist { hide_list = addDef iname acc (hide_list ist) })
    ist <- getIState

    let totopts = Dictionary : Inlinable : opts

    let emptyinterface = null (interface_methods ci)
    when (what /= EDefns) $ do
         nty <- elabType' True info syn doc argDocs fc totopts iname NoFC
                          (piBindp expl_param pextra t)
         -- if the implementation type matches any of the implementations we have already,
         -- and it's not a named implementation, then it's overlapping, so report an error
         case expn of
            Nothing
               | OverlappingDictionary `notElem` opts ->
                       do mapM_ (maybe (return ()) overlapping . findOverlapping ist (interface_determiners ci) (delab ist nty))
                                (map fst $ interface_implementations ci)
                          addImplementation intImpl True n iname
            _ -> addImplementation intImpl False n iname

    ist <- getIState
    checkInjectiveArgs fc n (interface_determiners ci) (lookupTyExact iname (tt_ctxt ist))

    when (what /= ETypes && (not (null ds && not emptyinterface))) $ do
         -- Add the parent implementation names to the privileged set
         oldOpen <- addOpenImpl parents

         let ips = zip (interface_params ci) ps
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

         let superInterfaceImplementations = map (substImplementation ips pnames) (interface_default_super_interfaces ci)
         undefinedSuperInterfaceImplementations <- filterM (fmap not . isOverlapping ist) superInterfaceImplementations
         mapM_ (rec_elabDecl info EAll info) undefinedSuperInterfaceImplementations

         ist <- getIState
         -- Bring variables in implementation head into scope when building the
         -- dictionary
         let headVars = nub $ concatMap getHeadVars ps
         let (headVarTypes, ty)
                = case lookupTyExact iname (tt_ctxt ist) of
                              Just ty -> (map (\n -> (n, getTypeIn ist n ty)) headVars, ty)
                              _ -> (zip headVars (repeat Placeholder), Erased)

         let impps = getImpParams ist (interface_impparams ci)
                          (snd (unApply (substRetTy ty)))
         let iimpps = zip (interface_impparams ci) impps

         logElab 5 $ "ImpPS: " ++ show impps ++ " --- " ++ show iimpps
         logElab 5 $ "Head var types " ++ show headVarTypes ++ " from " ++ show ty

         let all_meths = map (nsroot . fst) (interface_methods ci)
         let mtys = map (\ (n, (inj, op, t)) ->
                   let t_in = substMatchesShadow (iimpps ++ ips) pnames t
                       mnamemap =
                          map (\n -> (n, PApp fc (PRef fc [] (decorate ns iname n))
                                              (map (toImp fc) headVars)))
                                      all_meths
                       t' = substMatchesShadow mnamemap pnames t_in in
                       (decorate ns iname n,
                           op, coninsert cs pextra t', t'))
              (interface_methods ci)

         logElab 5 (show (mtys, (iimpps ++ ips)))
         logElab 5 ("Before defaults: " ++ show ds ++ "\n" ++ show (map fst (interface_methods ci)))
         let ds_defs = insertDefaults ist iname (interface_defaults ci) ns ds
         logElab 3 ("After defaults: " ++ show ds_defs ++ "\n")

         let ds' = reorderDefs (map fst (interface_methods ci)) ds_defs
         logElab 1 ("Reordered: " ++ show ds' ++ "\n")

         mapM_ (warnMissing ds' ns iname) (map fst (interface_methods ci))
         mapM_ (checkInInterface (map fst (interface_methods ci))) (concatMap defined ds')
         let wbTys = map mkTyDecl mtys
         let wbVals_orig = map (decorateid (decorate ns iname)) ds'
         ist <- getIState
         let wbVals = map (expandParamsD False ist id pextra (map methName mtys)) wbVals_orig
         let wb = wbTys ++ wbVals

         logElab 3 $ "Method types " ++ showSep "\n" (map (show . showDeclImp verbosePPOption . mkTyDecl) mtys)
         logElab 3 $ "Implementation is " ++ show ps ++ " implicits " ++ show (concat (nub wparams))

         let lhsImps = map (\n -> pimp n (PRef fc [] n) True) headVars

         let lhs = PApp fc (PRef fc [] iname) (lhsImps ++ map (toExp .fst) pextra)
         let rhs = PApp fc (PRef fc [] (implementationCtorName ci))
                           (map (pexp . (mkMethApp lhsImps)) mtys)

         logElab 5 $ "Implementation LHS " ++ show totopts ++ "\n" ++ showTmImpls lhs ++ " " ++ show headVars
         logElab 5 $ "Implementation RHS " ++ show rhs

         push_estack iname True
         logElab 3 ("Method types: " ++ show wbTys)
         logElab 3 ("Method bodies (before params): " ++ show wbVals_orig)
         logElab 3 ("Method bodies: " ++ show wbVals)

         let idecls = [PClauses fc totopts iname
                              [PClause fc iname lhs [] rhs []]]

         mapM_ (rec_elabDecl info EAll info) (map (impBind headVarTypes) wbTys)
         mapM_ (rec_elabDecl info EAll info) idecls

         ctxt <- getContext
         let ifn_ty = case lookupTyExact iname ctxt of
                           Just t -> t
                           Nothing -> error "Can't happen (interface constructor)"
         let ifn_is = case lookupCtxtExact iname (idris_implicits ist) of
                           Just t -> t
                           Nothing -> []
         let prop_params = getParamsInType ist [] ifn_is ifn_ty

         logElab 3 $ "Propagating parameters to methods: "
                           ++ show (iname, prop_params)

         let wbVals' = map (addParams prop_params) wbVals

         logElab 5 ("Elaborating method bodies: " ++ show wbVals')
         mapM_ (rec_elabDecl info EAll info) wbVals'

         mapM_ (checkInjectiveDef fc (interface_methods ci)) (zip ds' wbVals')

         pop_estack

         setOpenImpl oldOpen
--          totalityCheckBlock

         addIBC (IBCImplementation intImpl (isNothing expn) n iname)

  where
    getImpParams ist = zipWith (\n tm -> delab ist tm)

    intImpl = case ps of
                [PConstant NoFC (AType (ATInt ITNative))] -> True
                _ -> False

    mkiname n' ns ps' expn' =
        case expn' of
          Nothing -> case ns of
                          [] -> SN (sImplementationN n' (map show ps'))
                          m -> sNS (SN (sImplementationN n' (map show ps'))) m
          Just nm -> nm

    substImplementation ips pnames (PImplementation doc argDocs syn _ cs parents acc opts n nfc ps pextra t expn ds)
        = PImplementation doc argDocs syn fc cs parents acc opts n nfc
                     (map (substMatchesShadow ips pnames) ps)
                     pextra
                     (substMatchesShadow ips pnames t) expn ds

    isOverlapping i (PImplementation doc argDocs syn _ _ _ _ _ n nfc ps pextra t expn _)
        = case lookupCtxtName n (idris_interfaces i) of
            [(n, ci)] -> let iname = (mkiname n (namespace info) ps expn) in
                            case lookupTy iname (tt_ctxt i) of
                              [] -> elabFindOverlapping i ci iname syn t
                              (_:_) -> return True
            _ -> return False -- couldn't find interface, just let elabImplementation fail later

    elabFindOverlapping i ci iname syn t
        = do ty' <- addUsingConstraints syn fc t
             -- TODO think: something more in info?
             ty' <- implicit info syn iname ty'
             let ty = addImpl [] i ty'
             ctxt <- getContext
             (ElabResult tyT _ _ ctxt' newDecls highlights newGName, _) <-
                tclift $ elaborate (constraintNS info) ctxt (idris_datatypes i) (idris_name i) iname (TType (UVal 0)) initEState
                         (errAt "type of " iname Nothing (erun fc (build i info ERHS [] iname ty)))
             setContext ctxt'
             processTacticDecls info newDecls
             sendHighlighting highlights
             updateIState $ \i -> i { idris_name = newGName }

             ctxt <- getContext
             (cty, _) <- recheckC (constraintNS info) fc id [] tyT
             let nty = normalise ctxt [] cty
             return $ any (isJust . findOverlapping i (interface_determiners ci) (delab i nty)) (map fst $ interface_implementations ci)

    findOverlapping i dets t n
     | SN (ParentN _ _) <- n = Nothing
     | Just opts <- lookupCtxtExact n (idris_flags i),
       OverlappingDictionary `elem` opts = Nothing
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

    methName (n, _, _, _) = n
    toExp n = pexp (PRef fc [] n)

    mkMethApp ps (n, _, _, ty)
              = lamBind 0 ty (papp fc (PRef fc [] n)
                     (ps ++ map (toExp . fst) pextra ++ methArgs 0 ty))
       where
          needed is p = pname p `elem` map pname is

    lamBind i (PPi (Constraint _ _ _) _ _ _ sc) sc'
          = PLam fc (sMN i "meth") NoFC Placeholder (lamBind (i+1) sc sc')
    lamBind i (PPi _ n _ ty sc) sc'
          = PLam fc (sMN i "meth") NoFC Placeholder (lamBind (i+1) sc sc')
    lamBind i _ sc = sc
    methArgs i (PPi (Imp _ _ _ _ _ _) n _ ty sc)
        = PImp 0 True [] n (PRef fc [] (sMN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Exp _ _ _ _) n _ ty sc)
        = PExp 0 [] (sMN 0 "marg") (PRef fc [] (sMN i "meth")) : methArgs (i+1) sc
    methArgs i (PPi (Constraint _ _ _) n _ ty sc)
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

    decorate ns iname (NS (UN nm) s)
         = NS (SN (WhereN 0 iname (SN (MethodN (UN nm))))) ns
    decorate ns iname nm
         = NS (SN (WhereN 0 iname (SN (MethodN nm)))) ns

    mkTyDecl (n, op, t, _)
        = PTy emptyDocstring [] syn fc op n NoFC
               (mkUniqueNames [] [] t)

    conbind :: [(Name, PTerm)] -> PTerm -> PTerm
    conbind ((c,ty) : ns) x = PPi constraint c NoFC ty (conbind ns x)
    conbind [] x = x

    extrabind :: [(Name, PTerm)] -> PTerm -> PTerm
    extrabind ((c,ty) : ns) x = PPi expl c NoFC ty (extrabind ns x)
    extrabind [] x = x

    coninsert :: [(Name, PTerm)] -> [(Name, PTerm)] -> PTerm -> PTerm
    coninsert cs ex (PPi p@(Imp _ _ _ _ _ _) n fc t sc) = PPi p n fc t (coninsert cs ex sc)
    coninsert cs ex sc = conbind cs (extrabind ex sc)

    -- Reorder declarations to be in the same order as defined in the
    -- interface declaration (important so that we insert default definitions
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

    checkInInterface ns meth
        | any (eqRoot meth) ns = return ()
        | otherwise = tclift $ tfail (At fc (Msg $
                                show meth ++ " not a method of interface " ++ show n))

    eqRoot x y = nsroot x == nsroot y

    clauseFor m iname ns (PClauses _ _ m' _)
       = decorate ns iname m == decorate ns iname m'
    clauseFor m iname ns _ = False

getHeadVars :: PTerm -> [Name]
getHeadVars (PRef _ _ n) | implicitable n = [n]
getHeadVars (PApp _ _ args) = concatMap getHeadVars (map getTm args)
getHeadVars (PPair _ _ _ l r) = getHeadVars l ++ getHeadVars r
getHeadVars (PDPair _ _ _ l t r) = getHeadVars l ++ getHeadVars t ++ getHeadVars t
getHeadVars _ = []

-- | Implicitly bind variables from the implementation head in method types
impBind :: [(Name, PTerm)] -> PDecl -> PDecl
impBind vs (PTy d ds syn fc opts n fc' t)
     = PTy d ds syn fc opts n fc'
          (doImpBind (filter (\(n, ty) -> n `notElem` boundIn t) vs) t)
  where
    doImpBind [] ty = ty
    doImpBind ((n, argty) : ns) ty
       = PPi impl n NoFC argty (doImpBind ns ty)

    boundIn (PPi _ n _ _ sc) = n : boundIn sc
    boundIn _ = []

getTypeIn :: IState -> Name -> Type -> PTerm
getTypeIn ist n (Bind x b sc)
    | n == x = delab ist (binderTy b)
    | otherwise = getTypeIn ist n (substV (P Ref x Erased) sc)
getTypeIn ist n tm = Placeholder

toImp fc n = pimp n (PRef fc [] n) True

-- | Propagate interface parameters to method bodies, if they're not
-- already there, and they are needed (i.e. appear in method's type)
addParams :: [Name] -> PDecl -> PDecl
addParams ps (PClauses fc opts n cs) = PClauses fc opts n (map addCParams cs)
  where
    addCParams (PClause fc n lhs ws rhs wb)
        = PClause fc n (addTmParams (dropPs (allNamesIn lhs) ps) lhs) ws rhs wb
    addCParams (PWith fc n lhs ws sc pn ds)
        = PWith fc n (addTmParams (dropPs (allNamesIn lhs) ps) lhs) ws sc pn
                      (map (addParams ps) ds)
    addCParams c = c

    addTmParams ps (PRef fc hls n)
        = PApp fc (PRef fc hls n) (map (toImp fc) ps)
    addTmParams ps (PApp fc ap@(PRef fc' hls n) args)
        = PApp fc ap (mergePs (map (toImp fc) ps) args)
    addTmParams ps tm = tm

    mergePs [] args = args
    mergePs (p : ps) args
         | isImplicit p,
           pname p `notElem` map pname args
               = p : mergePs ps args
       where
         isImplicit (PExp{}) = False
         isImplicit _ = True
    mergePs (p : ps) args
         = mergePs ps args

    -- Don't propagate a parameter if the name is rebound explicitly
    dropPs :: [Name] -> [Name] -> [Name]
    dropPs ns = filter (\x -> x `notElem` ns)

addParams ps d = d

-- | Check a given method definition is injective, if the interface info
-- says it needs to be.  Takes originally written decl and the one
-- with name decoration, so we know which name to look up.
checkInjectiveDef :: FC -> [(Name, (Bool, FnOpts, PTerm))] ->
                           (PDecl, PDecl) -> Idris ()
checkInjectiveDef fc ns (PClauses _ _ n cs, PClauses _ _ elabn _)
   | Just (True, _, _) <- clookup n ns
          = do ist <- getIState
               case lookupDefExact elabn (tt_ctxt ist) of
                    Just (CaseOp _ _ _ _ _ cdefs) ->
                       checkInjectiveCase ist (snd (cases_compiletime cdefs))
  where
    checkInjectiveCase ist (STerm tm)
         = checkInjectiveApp ist (fst (unApply tm))
    checkInjectiveCase _ _ = notifail

    checkInjectiveApp ist (P (TCon _ _) n _) = return ()
    checkInjectiveApp ist (P (DCon _ _ _) n _) = return ()
    checkInjectiveApp ist (P Ref n _)
        | Just True <- lookupInjectiveExact n (tt_ctxt ist) = return ()
    checkInjectiveApp ist (P Ref n _) = notifail
    checkInjectiveApp _ _ = notifail

    notifail = ierror $ At fc (Msg (show n ++ " must be defined by a type or data constructor"))

    clookup n [] = Nothing
    clookup n ((n', d) : ds) | nsroot n == nsroot n' = Just d
                             | otherwise = Nothing
checkInjectiveDef fc ns _ = return ()

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
    isInj i (Bind n b@(Pi{}) sc) = isInj i (binderTy b) && isInj i sc
    isInj i (Bind n b sc) = False
    isInj _ _ = True

    instantiateRetTy (Bind n (Pi _ _ _ _) sc)
       = substV (P Bound n Erased) (instantiateRetTy sc)
    instantiateRetTy t = t

{-|
Module      : Idris.Elab.Interface
Description : Code to elaborate interfaces.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fwarn-missing-signatures #-}
module Idris.Elab.Interface(elabInterface) where

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
import Data.Generics.Uniplate.Data (transform)
import Data.List
import Data.List.Split (splitOn)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Debug.Trace


data MArgTy = IA Name | EA Name | CA deriving Show

elabInterface :: ElabInfo
              -> SyntaxInfo
              -> Docstring (Either Err PTerm)
              -> ElabWhat
              -> FC
              -> [(Name, PTerm)] -- ^ Superclass constraints
              -> Name
              -> FC
              -> [(Name, FC, PTerm)] -- ^ Parameters
              -> [(Name, Docstring (Either Err PTerm))]
              -> [(Name, FC)]                 -- ^ determining params
              -> [PDecl]                      -- ^ interface body
              -> Maybe (Name, FC)             -- ^ implementation ctor name and location
              -> Docstring (Either Err PTerm) -- ^ implementation ctor docs
              -> Idris ()
elabInterface info_in syn_in doc what fc constraints tn tnfc ps pDocs fds ds mcn cd
    = do let cn = fromMaybe (SN (ImplementationCtorN tn)) (fst <$> mcn)
         let constraint = PApp fc (PRef fc [] tn)
                                  (map (pexp . PRef fc []) (map (\(n, _, _) -> n) ps))

         let syn =
              syn_in { using = addToUsing (using syn_in)
                                 [(pn, pt) | (pn, _, pt) <- ps]
                     }

         -- Calculate implicit parameters
         ist <- getIState
         let impps_ns = nub $ map (\n -> (n, emptyFC, Placeholder)) $
                            concatMap (implicitNamesIn [] ist)
                                      (map (\ (_,_,x) -> x) ps)
         let impps = filter (\ (n, _, _) ->
                               n `notElem` (map (\ (n, _, _) -> n) ps)) impps_ns

         let tty = impbind (map (\(n, _, ty) -> (n, ty)) impps) $
                     pibind (map (\(n, _, ty) -> (n, ty)) ps) (PType fc)

         logElab 5 $ "Implicit parameters are " ++ show impps
         logElab 5 $ "Interface type is " ++ showTmImpls tty

         -- build data declaration
         let mdecls = filter tydecl ds -- method declarations
         let idecls = filter impldecl ds -- default super interface implementation declarations
         mapM_ checkDefaultSuperInterfaceImplementation idecls
         let mnames = map getMName mdecls
         let fullmnames = map getFullMName mdecls
         ist <- getIState
         let constraintNames = nub $
                 concatMap (namesIn [] ist) (map snd constraints)

         mapM_ (checkConstraintName (map (\(x, _, _) -> x) ps)) constraintNames

         let pre_ddecl = PLaterdecl tn NoFC tty
         -- Elaborate the interface header, as long as we haven't done it
         -- in an earlier pass
         when (what /= EDefns) $
            elabData info (syn { no_imp = no_imp syn ++ mnames,
                                 imp_methods = mnames }) doc pDocs fc [] pre_ddecl
         -- Continue only if we're not in the first pass of a mutual block
         when (what /= ETypes) $ do
             dets <- findDets tn (map fst fds)

             logElab 3 $ "Building methods " ++ show fullmnames
             ims <- mapM (tdecl impps mnames) mdecls
             defs <- mapM (defdecl (map (\ (x,y,z) -> z) ims) constraint)
                          (filter clause ds)
             let (methods, imethods)
                  = unzip (map (\ (x, y, z) -> (x, y)) ims)
             let defaults = map (\ (x, (y, z)) -> (x,y)) defs

             addInterface tn (CI cn (map nodoc imethods) defaults idecls
                                  (map (\(n, _, _) -> n) impps)
                                  (map (\(n, _, _) -> n) ps)
                                  (map snd constraints)
                                  [] dets)

             -- for each constraint, build a top level function to chase it
             -- elaborate types now, bodies later (after we've done the constructor
             -- of the interface)
             cfns <- mapM (cfun cn constraint syn (map fst imethods)) constraints
             let (cfnTyDecls, cfnDefs) = unzip cfns
             mapM_ (rec_elabDecl info EAll info) cfnTyDecls

             -- for each method, build a top level function
             -- 'tfun' builds appropriate implicits for the constructor
             -- declaration
             fns <- mapM (tfun cn constraint (syn { imp_methods = mnames }) -- mnames })
                               (map fst imethods)) imethods
             let (fnTyDecls, fnDefs) = unzip fns
             mapM_ (rec_elabDecl info EAll info) fnTyDecls

             elabMethTys <- mapM getElabMethTy fullmnames

             logElab 3 $ "Method types:\n" ++ showSep "\n" (map showTmImpls elabMethTys)

             let cpos = map (\ (n, ty) -> (n, findConstraint ty))
                            (zip fullmnames elabMethTys)
             logElab 5 $ "Constraint pos: " ++ show cpos

             -- Method types to store in the IState, taken from the elaborated
             -- types with the parameter removed
             let storemeths = map (mkMethTy True cpos) (zip fullmnames elabMethTys)
             updateIMethods tn storemeths

             -- build implementation constructor type
             let cty = impbind [(pn, pt) | (pn, _, pt) <- impps ++ ps] $
                             conbind constraints $
                             pibind (map (mkMethTy False cpos) (zip fullmnames elabMethTys))
                             constraint
             logElab 3 $ "Constraint constructor type: " ++ showTmImpls cty

             let cons = [(cd, pDocs ++ mapMaybe memberDocs ds, cn, NoFC, cty, fc, [])]
             let ddecl = PDatadecl tn NoFC tty cons

             logElab 10 $ "Interface " ++ show (showDImp verbosePPOption ddecl)


             -- Elaborate the data declaration
             elabData info (syn { no_imp = no_imp syn ++ mnames,
                                  imp_methods = [] }) doc pDocs fc [] ddecl


             logElab 5 $ "Function types " ++ show fnTyDecls
             logElab 5 $ "Method types now: " ++ show imethods

             -- Elaborate the the top level constraint chasers
             -- (Types elaborated earlier)
             mapM_ (rec_elabDecl info EAll info) cfnDefs
             -- Elaborate the the top level method bodies
             mapM_ (rec_elabDecl info EAll info) fnDefs

             -- Flag all the top level data declarations as injective
             mapM_ (\n -> do setInjectivity n True
                             addIBC (IBCInjective n True))
                   (map fst (filter (\(_, (inj, _, _, _, _)) -> inj) imethods))

             -- add the default definitions
             mapM_ (rec_elabDecl info EAll info) (concatMap (snd.snd) defs)
             addIBC (IBCInterface tn)

             sendHighlighting $
               [(tnfc, AnnName tn Nothing Nothing Nothing)] ++
               [(pnfc, AnnBoundName pn False) | (pn, pnfc, _) <- ps] ++
               [(fdfc, AnnBoundName fc False) | (fc, fdfc) <- fds] ++
               maybe [] (\(conN, conNFC) -> [(conNFC, AnnName conN Nothing Nothing Nothing)]) mcn

  where
    info = info_in { noCaseLift = tn : noCaseLift info_in }

    getElabMethTy :: Name -> Idris PTerm
    getElabMethTy n = do ist <- getIState
                         let impls = case lookupCtxtExact n (idris_implicits ist) of
                                          Just i -> i
                                          Nothing -> []
                         case lookupTyExact n (tt_ctxt ist) of
                              Just ty -> return (delabTy' ist impls [] ty False False False)
                              Nothing -> tclift $ tfail (At fc (InternalMsg "Can't happen, elabMethTy"))

    -- Find the argument position of the current interface in a method type
    -- (we'll use this to update the elaborated top level method types before
    -- building a data declaration
    findConstraint :: PTerm -> Int
    findConstraint = findPos 0
      where
        findPos i (PPi _ _ _ (PRef _ _ n) sc)
            | n == tn = i
        findPos i (PPi _ _ _ (PApp _ (PRef _ _ n) _) sc)
            | n == tn = i
        findPos i (PPi _ _ _ ty sc) = findPos (i + 1) sc
        findPos i _ = -1 -- Can't happen!

    -- Make the method component of the constructor type by taking the
    -- elaborated top level method and removing the implicits/constraint
    mkMethTy :: Bool -> [(Name, Int)] -> (Name, PTerm) -> (Name, PTerm)
    mkMethTy keepns cpos (n, tm)
        = (if keepns then n else nsroot n, dropPis num (mapPT dropImp tm))
      where
        num = case lookup n cpos of
                   Just i -> i + 1
                   Nothing -> 0

        dropPis n (PPi _ _ _ _ sc) | n > 0 = dropPis (n - 1) sc
        dropPis _ tm = tm

        dropImp (PApp fc (PRef fcr fcs n) args)
            | Just pos <- lookup n cpos
                 = PApp fc (PRef fcr fcs (nsroot n))
                           (filter notConstr (drop (pos + 1) args))
        dropImp (PApp fc f args)
                 = PApp fc f (filter notConstr args)
        dropImp tm = tm

        notConstr (PConstraint {}) = False
        notConstr _ = True

    nodoc (n, (inj, _, _, o, t)) = (n, (inj, o, t))

    pibind [] x = x
    pibind ((n, ty): ns) x = PPi expl n NoFC ty (pibind ns (chkUniq ty x))

    -- To make sure the type constructor of the interface is in the appropriate
    -- uniqueness hierarchy
    chkUniq u@(PUniverse _ _) (PType _) = u
    chkUniq (PUniverse _ l) (PUniverse _ r) = PUniverse NoFC (min l r)
    chkUniq (PPi _ _ _ _ sc) t = chkUniq sc t
    chkUniq _ t = t

    -- TODO: probably should normalise
    checkDefaultSuperInterfaceImplementation :: PDecl -> Idris ()
    checkDefaultSuperInterfaceImplementation (PImplementation _ _ _ fc cs _ _ _ n _ ps _ _ _ _)
        = do when (not $ null cs) . tclift
                $ tfail (At fc (Msg "Default super interface implementations can't have constraints."))
             i <- getIState
             let t = PApp fc (PRef fc [] n) (map pexp ps)
             let isConstrained = any (== t) (map snd constraints)
             when (not isConstrained) . tclift
                $ tfail (At fc (Msg "Default implementations must be for a super interface constraint on the containing interface."))
             return ()

    checkConstraintName :: [Name] -> Name -> Idris ()
    checkConstraintName bound cname
        | cname `notElem` bound
            = tclift $ tfail (At fc (Msg $ "Name " ++ show cname ++
                         " is not bound in interface " ++ show tn
                         ++ " " ++ showSep " " (map show bound)))
        | otherwise = return ()

    impbind :: [(Name, PTerm)] -> PTerm -> PTerm
    impbind [] x = x
    impbind ((n, ty): ns) x = PPi impl n NoFC ty (impbind ns x)

    conbind :: [(Name, PTerm)] -> PTerm -> PTerm
    conbind ((c, ty) : ns) x = PPi constraint c NoFC ty (conbind ns x)
    conbind [] x = x

    getMName (PTy _ _ _ _ _ n nfc _) = nsroot n
    getMName (PData _ _ _ _ _ (PLaterdecl n nfc _)) = nsroot n

    getFullMName (PTy _ _ _ _ _ n nfc _) = n
    getFullMName (PData _ _ _ _ _ (PLaterdecl n nfc _)) = n

    tdecl impps allmeths (PTy doc _ syn _ o n nfc t)
           = do t' <- implicit' info syn (map (\(n, _, _) -> n) (impps ++ ps) ++ allmeths) n t
                logElab 1 $ "Method " ++ show n ++ " : " ++ showTmImpls t'
                return ( (n, (toExp (map (\(pn, _, _) -> pn) ps) Exp t')),
                         (n, (False, nfc, doc, o, (toExp (map (\(pn, _, _) -> pn) ps)
                                              (\ l s p r -> Imp l s p Nothing True r) t'))),
                         (n, (nfc, syn, o, t) ) )
    tdecl impps allmeths (PData doc _ syn _ _ (PLaterdecl n nfc t))
           = do let o = []
                t' <- implicit' info syn (map (\(n, _, _) -> n) ps ++ allmeths) n t
                logElab 2 $ "Data method " ++ show n ++ " : " ++ showTmImpls t'
                return ( (n, (toExp (map (\(pn, _, _) -> pn) ps) Exp t')),
                         (n, (True, nfc, doc, o, (toExp (map (\(pn, _, _) -> pn) ps)
                                              (\ l s p r -> Imp l s p Nothing True r) t'))),
                         (n, (nfc, syn, o, t) ) )
    tdecl impps allmeths (PData doc _ syn _ _ _)
         = ierror $ At fc (Msg "Data definitions not allowed in an interface declaration")
    tdecl _ _ _ = ierror $ At fc (Msg "Not allowed in an interface declaration")

    -- Create default definitions
    defdecl mtys c d@(PClauses fc opts n cs) =
        case lookup n mtys of
            Just (nfc, syn, o, ty) ->
              do let ty' = insertConstraint c (map fst mtys) ty
                 let ds = map (decorateid defaultdec)
                              [PTy emptyDocstring [] syn fc [] n nfc ty',
                               PClauses fc (o ++ opts) n cs]
                 logElab 1 (show ds)
                 return (n, ((defaultdec n, ds!!1), ds))
            _ -> ierror $ At fc (Msg (show n ++ " is not a method"))
    defdecl _ _ _ = ifail "Can't happen (defdecl)"

    defaultdec (UN n) = sUN ("default#" ++ str n)
    defaultdec (NS n ns) = NS (defaultdec n) ns

    tydecl (PTy{}) = True
    tydecl (PData _ _ _ _ _ _) = True
    tydecl _ = False
    impldecl (PImplementation{}) = True
    impldecl _ = False
    clause (PClauses{}) = True
    clause _ = False

    -- Generate a function for chasing a dictionary constraint
    cfun :: Name -> PTerm -> SyntaxInfo -> [a] -> (Name, PTerm) -> Idris (PDecl, PDecl)
    cfun cn c syn all (cnm, con)
        = do let cfn = SN (ParentN cn (txt (show con)))
             let mnames = take (length all) $ map (\x -> sMN x "meth") [0..]
             let capp = PApp fc (PRef fc [] cn) (map (pexp . PRef fc []) mnames)
             let lhs = PApp fc (PRef fc [] cfn) [pconst capp]
             let rhs = PResolveTC (fileFC "HACK")
             let ty = PPi constraint cnm NoFC c con
             logElab 2 ("Dictionary constraint: " ++ showTmImpls ty)
             logElab 2 (showTmImpls lhs ++ " = " ++ showTmImpls rhs)
             i <- getIState
             let conn = case con of
                            PRef _ _ n -> n
                            PApp _ (PRef _ _ n) _ -> n
             let conn' = case lookupCtxtName conn (idris_interfaces i) of
                                [(n, _)] -> n
                                _ -> conn
             addImplementation False True conn' cfn
             addIBC (IBCImplementation False True conn' cfn)
--              iputStrLn ("Added " ++ show (conn, cfn, ty))
             return (PTy emptyDocstring [] syn fc [] cfn NoFC ty,
                     PClauses fc [Inlinable, Dictionary] cfn [PClause fc cfn lhs [] rhs []])

    -- | Generate a top level function which looks up a method in a given
    -- dictionary (this is inlinable, always)
    tfun :: Name -- ^ The name of the interface
         -> PTerm -- ^ A constraint for the interface, to be inserted under the implicit bindings
         -> SyntaxInfo -> [Name] -- ^ All the method names
         -> (Name, (Bool, FC, Docstring (Either Err PTerm), FnOpts, PTerm))
            -- ^ The present declaration
         -> Idris (PDecl, PDecl)
    tfun cn c syn all (m, (isdata, mfc, doc, o, ty))
        = do let ty' = expandMethNS syn (insertConstraint c all ty)
             let mnames = take (length all) $ map (\x -> sMN x "meth") [0..]
             let capp = PApp fc (PRef fc [] cn) (map (pexp . PRef fc []) mnames)
             let margs = getMArgs ty
             let anames = map (\x -> sMN x "arg") [0..]
             let lhs = PApp fc (PRef fc [] m) (pconst capp : lhsArgs margs anames)
             let rhs = PApp fc (getMeth mnames all m) (rhsArgs margs anames)
             logElab 2 ("Top level type: " ++ showTmImpls ty')
             logElab 1 (show (m, ty', capp, margs))
             logElab 2 ("Definition: " ++ showTmImpls lhs ++ " = " ++ showTmImpls rhs)
             return (PTy doc [] syn fc o m mfc ty',
                     PClauses fc [Inlinable] m [PClause fc m lhs [] rhs []])

    updateIMethod :: [(Name, PTerm)] ->
                     (Name, (a, b, c, d, PTerm)) ->
                     (Name, (a, b, c, d, PTerm))
    updateIMethod ns tm@(n, (isf, mfc, doc, o, ty))
       | Just ty' <- lookup (nsroot n) ns = (n, (isf, mfc, doc, o, ty'))
       | otherwise = tm

    getMArgs (PPi (Imp _ _ _ _ _ _) n _ ty sc) = IA n : getMArgs sc
    getMArgs (PPi (Exp _ _ _ _) n _ ty sc) = EA n : getMArgs sc
    getMArgs (PPi (Constraint _ _ _) n _ ty sc) = CA : getMArgs sc
    getMArgs _ = []

    getMeth :: [Name] -> [Name] -> Name -> PTerm
    getMeth (m:ms) (a:as) x | x == a = PRef fc [] m
                            | otherwise = getMeth ms as x

    lhsArgs (EA _ : xs) (n : ns) = [] -- pexp (PRef fc n) : lhsArgs xs ns
    lhsArgs (IA n : xs) ns = pimp n (PRef fc [] n) False : lhsArgs xs ns
    lhsArgs (CA : xs) ns = lhsArgs xs ns
    lhsArgs [] _ = []

    rhsArgs (EA _ : xs) (n : ns) = [] -- pexp (PRef fc n) : rhsArgs xs ns
    rhsArgs (IA n : xs) ns = pexp (PRef fc [] n) : rhsArgs xs ns
    rhsArgs (CA : xs) ns = pconst (PResolveTC fc) : rhsArgs xs ns
    rhsArgs [] _ = []

    -- Add the top level constraint. Put it first - elaboration will resolve
    -- the order of the implicits if there are dependencies.
    -- Also ensure the dictionary is used for lookup of any methods that
    -- are used in the type
    insertConstraint :: PTerm -> [Name] -> PTerm -> PTerm
    insertConstraint c all sc
          = let dictN = sMN 0 "__interface" in
                PPi (constraint { pstatic = Static })
                    dictN NoFC c
                    (constrainMeths (map basename all)
                                    dictN sc)
     where
       -- After we insert the constraint into the lookup, we need to
       -- ensure that the same dictionary is used to resolve lookups
       -- to the other methods in the interface
       constrainMeths :: [Name] -> Name -> PTerm -> PTerm
       constrainMeths allM dictN tm = transform (addC allM dictN) tm

       addC allM dictN m@(PRef fc hls n)
          | n `elem` allM = PApp NoFC m [pconst (PRef NoFC hls dictN)]
          | otherwise = m
       addC _ _ tm = tm

    -- make arguments explicit and don't bind interface parameters
    toExp ns e (PPi (Imp l s p _ _ r) n fc ty sc)
        | n `elem` ns = toExp ns e sc
        | otherwise = PPi (e l s p r) n fc ty (toExp ns e sc)
    toExp ns e (PPi p n fc ty sc) = PPi p n fc ty (toExp ns e sc)
    toExp ns e sc = sc

-- | Get the method declaration name corresponding to a user-provided name
mdec :: Name -> Name
mdec (UN n) = SN (MethodN (UN n))
mdec (NS x n) = NS (mdec x) n
mdec x = x

-- | Get the docstring corresponding to a member, if one exists
memberDocs :: PDecl -> Maybe (Name, Docstring (Either Err PTerm))
memberDocs (PTy d _ _ _ _ n _ _) = Just (basename n, d)
memberDocs (PPostulate _ d _ _ _ _ n _) = Just (basename n, d)
memberDocs (PData d _ _ _ _ pdata) = Just (basename $ d_name pdata, d)
memberDocs (PRecord d _ _ _ n _ _ _ _ _ _ _ ) = Just (basename n, d)
memberDocs (PInterface d _ _ _ n _ _ _ _ _ _ _) = Just (basename n, d)
memberDocs _ = Nothing


-- | In a top level type for a method, expand all the method names' namespaces
-- so that we don't have to disambiguate later
expandMethNS :: SyntaxInfo
                -> PTerm -> PTerm
expandMethNS syn = mapPT expand
  where
    expand (PRef fc hls n) | n `elem` imp_methods syn = PRef fc hls $ expandNS syn n
    expand t = t

-- | Find the determining parameter locations
findDets :: Name -> [Name] -> Idris [Int]
findDets n ns =
    do i <- getIState
       return $ case lookupTyExact n (tt_ctxt i) of
            Just ty -> getDetPos 0 ns ty
            Nothing -> []
  where
    getDetPos i ns (Bind n (Pi _ _ _ _) sc)
       | n `elem` ns = i : getDetPos (i + 1) ns sc
       | otherwise = getDetPos (i + 1) ns sc
    getDetPos _ _ _ = []

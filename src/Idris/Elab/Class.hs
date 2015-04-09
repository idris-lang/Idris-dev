{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Class(elabClass) where

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

data MArgTy = IA Name | EA Name | CA deriving Show

elabClass :: ElabInfo -> SyntaxInfo -> Docstring (Either Err PTerm) ->
             FC -> [(Name, PTerm)] ->
             Name -> [(Name, PTerm)] -> [(Name, Docstring (Either Err PTerm))] -> 
             [Name] -> [PDecl] -> Idris ()
elabClass info syn_in doc fc constraints tn ps pDocs fds ds
    = do let cn = SN (InstanceCtorN tn) -- sUN ("instance" ++ show tn) -- MN 0 ("instance" ++ show tn)
         let tty = pibind ps PType
         let constraint = PApp fc (PRef fc tn)
                                  (map (pexp . PRef fc) (map fst ps))

         let syn = syn_in { using = addToUsing (using syn_in) ps }

         -- build data declaration
         let mdecls = filter tydecl ds -- method declarations
         let idecls = filter instdecl ds -- default superclass instance declarations
         mapM_ checkDefaultSuperclassInstance idecls
         let mnames = map getMName mdecls
         logLvl 1 $ "Building methods " ++ show mnames
         ims <- mapM (tdecl mnames) mdecls
         defs <- mapM (defdecl (map (\ (x,y,z) -> z) ims) constraint)
                      (filter clause ds)
         let (methods, imethods)
              = unzip (map (\ ( x,y,z) -> (x, y)) ims)
         let defaults = map (\ (x, (y, z)) -> (x,y)) defs
         -- build instance constructor type
         let cty = impbind ps $ conbind constraints
                      $ pibind (map (\ (n, ty) -> (nsroot n, ty)) methods)
                               constraint
         let cons = [(emptyDocstring, [], cn, cty, fc, [])]
         let ddecl = PDatadecl tn tty cons
         logLvl 5 $ "Class data " ++ show (showDImp verbosePPOption ddecl)
         -- Elaborate the data declaration
         elabData info (syn { no_imp = no_imp syn ++ mnames,
                              imp_methods = mnames }) doc pDocs fc [] ddecl
         dets <- findDets cn fds
         addClass tn (CI cn (map nodoc imethods) defaults idecls (map fst ps) [] dets)

         -- for each constraint, build a top level function to chase it
         cfns <- mapM (cfun cn constraint syn (map fst imethods)) constraints
         mapM_ (rec_elabDecl info EAll info) (concat cfns)

         -- for each method, build a top level function
         fns <- mapM (tfun cn constraint (syn { imp_methods = mnames })
                           (map fst imethods)) imethods
         logLvl 5 $ "Functions " ++ show fns
         -- Elaborate the the top level methods
         mapM_ (rec_elabDecl info EAll info) (concat fns)

         -- add the default definitions
         mapM_ (rec_elabDecl info EAll info) (concat (map (snd.snd) defs))
         addIBC (IBCClass tn)
  where
    nodoc (n, (_, o, t)) = (n, (o, t))
    pibind [] x = x
    pibind ((n, ty): ns) x = PPi expl n ty (pibind ns x)

    mdec :: Name -> Name
    mdec (UN n) = SN (MethodN (UN n))
    mdec (NS x n) = NS (mdec x) n
    mdec x = x

    -- TODO: probably should normalise
    checkDefaultSuperclassInstance :: PDecl -> Idris ()
    checkDefaultSuperclassInstance (PInstance _ _ _ fc cs n ps _ _ _)
        = do when (not $ null cs) . tclift
                $ tfail (At fc (Msg $ "Default superclass instances can't have constraints."))
             i <- getIState
             let t = PApp fc (PRef fc n) (map pexp ps)
             let isConstrained = any (== t) (map snd constraints)
             when (not isConstrained) . tclift
                $ tfail (At fc (Msg $ "Default instances must be for a superclass constraint on the containing class."))
             return ()

    impbind :: [(Name, PTerm)] -> PTerm -> PTerm
    impbind [] x = x
    impbind ((n, ty): ns) x = PPi impl n ty (impbind ns x)

    conbind :: [(Name, PTerm)] -> PTerm -> PTerm
    conbind ((c, ty) : ns) x = PPi constraint c ty (conbind ns x)
    conbind [] x = x

    getMName (PTy _ _ _ _ _ n _) = nsroot n
    tdecl allmeths (PTy doc _ syn _ o n t)
           = do t' <- implicit' info syn (map fst ps ++ allmeths) n t
                logLvl 2 $ "Method " ++ show n ++ " : " ++ showTmImpls t'
                return ( (n, (toExp (map fst ps) Exp t')),
                         (n, (doc, o, (toExp (map fst ps)
                                         (\ l s p -> Imp l s p Nothing) t'))),
                         (n, (syn, o, t) ) )
    tdecl _ _ = ifail "Not allowed in a class declaration"

    -- Create default definitions
    defdecl mtys c d@(PClauses fc opts n cs) =
        case lookup n mtys of
            Just (syn, o, ty) -> do let ty' = insertConstraint c ty
                                    let ds = map (decorateid defaultdec)
                                                 [PTy emptyDocstring [] syn fc [] n ty',
                                                  PClauses fc (o ++ opts) n cs]
                                    iLOG (show ds)
                                    return (n, ((defaultdec n, ds!!1), ds))
            _ -> ifail $ show n ++ " is not a method"
    defdecl _ _ _ = ifail "Can't happen (defdecl)"

    defaultdec (UN n) = sUN ("default#" ++ str n)
    defaultdec (NS n ns) = NS (defaultdec n) ns

    tydecl (PTy _ _ _ _ _ _ _) = True
    tydecl _ = False
    instdecl (PInstance _ _ _ _ _ _ _ _ _ _) = True
    instdecl _ = False
    clause (PClauses _ _ _ _) = True
    clause _ = False

    -- Generate a function for chasing a dictionary constraint
    cfun :: Name -> PTerm -> SyntaxInfo -> [a] -> (Name, PTerm) -> Idris [PDecl' PTerm]
    cfun cn c syn all (cnm, con)
        = do let cfn = sUN ('@':'@':show cn ++ "#" ++ show con)
                       -- SN (ParentN cn (show con))
             let mnames = take (length all) $ map (\x -> sMN x "meth") [0..]
             let capp = PApp fc (PRef fc cn) (map (pexp . PRef fc) mnames)
             let lhs = PApp fc (PRef fc cfn) [pconst capp]
             let rhs = PResolveTC (fileFC "HACK")
             let ty = PPi constraint cnm c con
             logLvl 2 ("Dictionary constraint: " ++ showTmImpls ty)
             logLvl 2 (showTmImpls lhs ++ " = " ++ showTmImpls rhs)
             i <- getIState
             let conn = case con of
                            PRef _ n -> n
                            PApp _ (PRef _ n) _ -> n
             let conn' = case lookupCtxtName conn (idris_classes i) of
                                [(n, _)] -> n
                                _ -> conn
             addInstance False conn' cfn
             addIBC (IBCInstance False conn' cfn)
--              iputStrLn ("Added " ++ show (conn, cfn, ty))
             return [PTy emptyDocstring [] syn fc [] cfn ty,
                     PClauses fc [Dictionary] cfn [PClause fc cfn lhs [] rhs []]]

    -- Generate a top level function which looks up a method in a given
    -- dictionary (this is inlinable, always)
    tfun cn c syn all (m, (doc, o, ty))
        = do let ty' = expandMethNS syn (insertConstraint c ty)
             let mnames = take (length all) $ map (\x -> sMN x "meth") [0..]
             let capp = PApp fc (PRef fc cn) (map (pexp . PRef fc) mnames)
             let margs = getMArgs ty
             let anames = map (\x -> sMN x "arg") [0..]
             let lhs = PApp fc (PRef fc m) (pconst capp : lhsArgs margs anames)
             let rhs = PApp fc (getMeth mnames all m) (rhsArgs margs anames)
             logLvl 2 ("Top level type: " ++ showTmImpls ty')
             iLOG (show (m, ty', capp, margs))
             logLvl 2 ("Definition: " ++ showTmImpls lhs ++ " = " ++ showTmImpls rhs)
             return [PTy doc [] syn fc o m ty',
                     PClauses fc [Inlinable] m [PClause fc m lhs [] rhs []]]

    getMArgs (PPi (Imp _ _ _ _) n ty sc) = IA n : getMArgs sc
    getMArgs (PPi (Exp _ _ _) n ty sc) = EA n : getMArgs sc
    getMArgs (PPi (Constraint _ _) n ty sc) = CA : getMArgs sc
    getMArgs _ = []

    getMeth (m:ms) (a:as) x | x == a = PRef fc m
                            | otherwise = getMeth ms as x

    lhsArgs (EA _ : xs) (n : ns) = [] -- pexp (PRef fc n) : lhsArgs xs ns
    lhsArgs (IA n : xs) ns = pimp n (PRef fc n) False : lhsArgs xs ns
    lhsArgs (CA : xs) ns = lhsArgs xs ns
    lhsArgs [] _ = []

    rhsArgs (EA _ : xs) (n : ns) = [] -- pexp (PRef fc n) : rhsArgs xs ns
    rhsArgs (IA n : xs) ns = pexp (PRef fc n) : rhsArgs xs ns
    rhsArgs (CA : xs) ns = pconst (PResolveTC fc) : rhsArgs xs ns
    rhsArgs [] _ = []

    insertConstraint c (PPi p@(Imp _ _ _ _) n ty sc)
                          = PPi p n ty (insertConstraint c sc)
    insertConstraint c sc = PPi (constraint { pstatic = Static })
                                  (sMN 0 "class") c sc

    -- make arguments explicit and don't bind class parameters
    toExp ns e (PPi (Imp l s p _) n ty sc)
        | n `elem` ns = toExp ns e sc
        | otherwise = PPi (e l s p) n ty (toExp ns e sc)
    toExp ns e (PPi p n ty sc) = PPi p n ty (toExp ns e sc)
    toExp ns e sc = sc

-- In a top level type for a method, expand all the method names namespaces
-- so that we don't have to disambiguate later
expandMethNS :: SyntaxInfo 
                -> PTerm -> PTerm
expandMethNS syn = mapPT expand
  where
    expand (PRef fc n) | n `elem` imp_methods syn = PRef fc $ expandNS syn n
    expand t = t

findDets :: Name -> [Name] -> Idris [Int]
findDets n ns = 
    do i <- getIState
       return $ case lookupTyExact n (tt_ctxt i) of
            Just ty -> getDetPos 0 ns ty
            Nothing -> []
  where
    getDetPos i ns (Bind n (Pi _ _ _) sc)
       | n `elem` ns = i : getDetPos (i + 1) ns sc
       | otherwise = getDetPos (i + 1) ns sc
    getDetPos _ _ _ = []



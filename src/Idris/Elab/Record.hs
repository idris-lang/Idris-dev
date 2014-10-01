{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Record(elabRecord) where

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

elabRecord :: ElabInfo -> SyntaxInfo -> Docstring (Maybe PTerm) -> FC -> Name ->
              PTerm -> DataOpts -> Docstring (Maybe PTerm) -> Name -> PTerm -> Idris ()
elabRecord info syn doc fc tyn ty opts cdoc cn cty_in
    = do elabData info syn doc [] fc opts (PDatadecl tyn ty [(cdoc, [], cn, cty_in, fc, [])])
         -- TODO think: something more in info?
         cty' <- implicit info syn cn cty_in
         i <- getIState

         -- get bound implicits and propagate to setters (in case they
         -- provide useful information for inference)
         let extraImpls = getBoundImpls cty'

         cty <- case lookupTy cn (tt_ctxt i) of
                    [t] -> return (delab i t)
                    _ -> ifail "Something went inexplicably wrong"
         cimp <- case lookupCtxt cn (idris_implicits i) of
                    [imps] -> return imps
         ppos <- case lookupCtxt tyn (idris_datatypes i) of
                    [ti] -> return $ param_pos ti
         let cty_imp = renameBs cimp cty
         let ptys = getProjs [] cty_imp
         let ptys_u = getProjs [] cty
         let recty = getRecTy cty_imp
         let recty_u = getRecTy cty

         let paramNames = getPNames recty ppos

         -- rename indices when we generate the getter/setter types, so
         -- that they don't clash with the names of the projections
         -- we're generating
         let index_names_in = getRecNameMap "_in" ppos recty
         let recty_in = substMatches index_names_in recty

         logLvl 3 $ show (recty, recty_u, ppos, paramNames, ptys)
         -- Substitute indices with projection functions, and parameters with
         -- the updated parameter name
         let substs = map (\ (n, _) -> 
                             if n `elem` paramNames
                                then (n, PRef fc (mkp n))
                                else (n, PApp fc (PRef fc n)
                                                [pexp (PRef fc rec)])) 
                          ptys 

         -- Generate projection functions
         proj_decls <- mapM (mkProj recty_in substs cimp) (zip ptys [0..])
         logLvl 3 $ show proj_decls
         let nonImp = mapMaybe isNonImp (zip cimp ptys_u)
         let implBinds = getImplB id cty'

         -- Generate update functions
         update_decls <- mapM (mkUpdate recty_u index_names_in extraImpls
                                   (getFieldNames cty')
                                   implBinds (length nonImp)) (zip nonImp [0..])
         mapM_ (rec_elabDecl info EAll info) (concat proj_decls)
         logLvl 3 $ show update_decls
         mapM_ (tryElabDecl info) (update_decls)
  where
--     syn = syn_in { syn_namespace = show (nsroot tyn) : syn_namespace syn_in }

    isNonImp (PExp _ _ _ _, a) = Just a
    isNonImp _ = Nothing

    getPNames (PApp _ _ as) ppos = getpn as ppos
      where
        getpn as [] = []
        getpn as (i:is) | length as > i,
                          PRef _ n <- getTm (as!!i) = n : getpn as is
                        | otherwise = getpn as is
    getPNames _ _ = []
   
    tryElabDecl info (fn, ty, val)
        = do i <- getIState
             idrisCatch (do rec_elabDecl info EAll info ty
                            rec_elabDecl info EAll info val)
                        (\v -> do iputStrLn $ show fc ++
                                      ":Warning - can't generate setter for " ++
                                      show fn ++ " (" ++ show ty ++ ")"
--                                       ++ "\n" ++ pshow i v
                                  putIState i)

    getBoundImpls (PPi (Imp _ _ _) n ty sc) = (n, ty) : getBoundImpls sc
    getBoundImpls _ = []

    getImplB k (PPi (Imp l s _) n Placeholder sc)
        = getImplB k sc
    getImplB k (PPi (Imp l s p) n ty sc)
        = getImplB (\x -> k (PPi (Imp l s p) n ty x)) sc
    getImplB k (PPi _ n ty sc)
        = getImplB k sc
    getImplB k _ = k

    renameBs (PImp _ _ _ _ _ : ps) (PPi p n ty s)
        = PPi p (mkImp n) ty (renameBs ps (substMatch n (PRef fc (mkImp n)) s))
    renameBs (_:ps) (PPi p n ty s) = PPi p n ty (renameBs ps s)
    renameBs _ t = t

    getProjs acc (PPi _ n ty s) = getProjs ((n, ty) : acc) s
    getProjs acc r = reverse acc

    getFieldNames (PPi (Exp _ _ _) n _ s) = n : getFieldNames s 
    getFieldNames (PPi _ _ _ s) = getFieldNames s
    getFieldNames _ = []

    getRecTy (PPi _ n ty s) = getRecTy s
    getRecTy t = t

    -- make sure we pick a consistent name for parameters; any name will do
    -- otherwise
    getRecNameMap x ppos (PApp fc t args) 
         = mapMaybe toMN (zip [0..] (map getTm args))
      where
        toMN (i, PRef fc n) 
             | i `elem` ppos = Just (n, PRef fc (mkp n))
             | otherwise = Just (n, PRef fc (sMN 0 (show n ++ x)))
        toMN _ = Nothing
    getRecNameMap x _ _ = []

    rec = sMN 0 "rec"

    -- only UNs propagate properly as parameters (bit of a hack then...)
    mkp (UN n) = sUN ("_p_" ++ str n)
    mkp (MN i n) = sMN i ("p_" ++ str n)
    mkp (NS n s) = NS (mkp n) s

    mkImp (UN n) = sUN ("implicit_" ++ str n)
    mkImp (MN i n) = sMN i ("implicit_" ++ str n)
    mkImp (NS n s) = NS (mkImp n) s

    mkType (UN n) = sUN ("set_" ++ str n)
    mkType (MN i n) = sMN i ("set_" ++ str n)
    mkType (NS n s) = NS (mkType n) s

    mkProj recty substs cimp ((pn_in, pty), pos)
        = do let pn = expandNS syn pn_in -- projection name
             -- use pn_in in the indices, consistently, to avoid clash
             let pfnTy = PTy emptyDocstring [] defaultSyntax fc [] pn
                            (PPi expl rec recty
                               (substMatches substs pty))
             let pls = repeat Placeholder
             let before = pos
             let after = length substs - (pos + 1)
             let args = take before pls ++ PRef fc (mkp pn_in) : take after pls
             let iargs = map implicitise (zip cimp args)
             let lhs = PApp fc (PRef fc pn)
                        [pexp (PApp fc (PRef fc cn) iargs)]
             let rhs = PRef fc (mkp pn_in)
             let pclause = PClause fc pn lhs [] rhs []
             return [pfnTy, PClauses fc [] pn [pclause]]

    implicitise (pa, t) = pa { getTm = t }

    -- If the 'pty' we're updating includes anything in 'substs', we're
    -- updating the type as well, so use recty', otherwise just use
    -- recty
    mkUpdate recty inames extras fnames k num ((pn, pty), pos)
       = do let setname = expandNS syn $ mkType pn
            let valname = sMN 0 "updateval"
            let pn_out = sMN 0 (show pn ++ "_out")
            let pn_in = sMN 0 (show pn ++ "_in")
            let recty_in = substMatches [(pn, PRef fc pn_in)] recty
            let recty_out = substMatches [(pn, PRef fc pn_out)] recty
            let pt = substMatches inames $ 
                       k (implBindUp extras inames (PPi expl pn_out pty
                           (PPi expl rec recty_in recty_out)))
            let pfnTy = PTy emptyDocstring [] defaultSyntax fc [] setname pt
--             let pls = map (\x -> PRef fc (sMN x ("field" ++ show x))) [0..num-1]
            let inames_imp = map (\ (x,_) -> (x, Placeholder)) inames
            let pls = map (\x -> substMatches inames_imp (PRef fc x)) fnames
            let lhsArgs = pls
            let rhsArgs = take pos pls ++ (PRef fc valname) :
                               drop (pos + 1) pls
            let before = pos
            let pclause = PClause fc setname (PApp fc (PRef fc setname)
                                              [pexp (PRef fc valname),
                                               pexp (PApp fc (PRef fc cn)
                                                        (map pexp lhsArgs))])
                                             []
                                             (PApp fc (PRef fc cn)
                                                      (map pexp rhsArgs)) []
            return (pn, pfnTy, PClauses fc [] setname [pclause])

    implBindUp [] is t = t
    implBindUp ((n, ty):ns) is t 
         = let n' = case lookup n is of
                         Just (PRef _ x) -> x
                         _ -> n in
               if n `elem` allNamesIn t 
                  then PPi impl n' ty (implBindUp ns is t)
                  else implBindUp ns is t


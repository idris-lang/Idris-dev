{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor,
             PatternGuards #-}

module Idris.ElabDecls where

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
import Idris.Elab.Type
import Idris.Elab.Clause
import Idris.Elab.Data
import Idris.Elab.Record
import Idris.Elab.Class
import Idris.Elab.Instance
import Idris.Elab.Provider
import Idris.Elab.Transform
import Idris.Elab.Value

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Execute
import Idris.Core.Typecheck
import Idris.Core.CaseTree

import Idris.Docstrings hiding (Unchecked)

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


-- Top level elaborator info, supporting recursive elaboration
recinfo :: ElabInfo
recinfo = EInfo [] emptyContext id Nothing Nothing elabDecl'

-- | Return the elaborated term which calls 'main'
elabMain :: Idris Term
elabMain = do (m, _) <- elabVal recinfo ERHS
                           (PApp fc (PRef fc (sUN "run__IO"))
                                [pexp $ PRef fc (sNS (sUN "main") ["Main"])])
              return m
  where fc = fileFC "toplevel"

-- | Elaborate primitives
elabPrims :: Idris ()
elabPrims = do mapM_ (elabDecl' EAll recinfo)
                     (map (\(opt, decl, docs, argdocs) -> PData docs argdocs defaultSyntax (fileFC "builtin") opt decl)
                        (zip4
                         [inferOpts,      eqOpts]
                         [inferDecl,      eqDecl]
                         [emptyDocstring, eqDoc]
                         [[],             eqParamDoc]))
               addNameHint eqTy (sUN "prf")
               mapM_ elabPrim primitives
               -- Special case prim__believe_me because it doesn't work on just constants
               elabBelieveMe
               -- Finally, syntactic equality
               elabSynEq
    where elabPrim :: Prim -> Idris ()
          elabPrim (Prim n ty i def sc tot)
              = do updateContext (addOperator n ty i (valuePrim def))
                   setTotality n tot
                   i <- getIState
                   putIState i { idris_scprims = (n, sc) : idris_scprims i }

          valuePrim :: ([Const] -> Maybe Const) -> [Value] -> Maybe Value
          valuePrim prim vals = fmap VConstant (mapM getConst vals >>= prim)

          getConst (VConstant c) = Just c
          getConst _             = Nothing


          p_believeMe [_,_,x] = Just x
          p_believeMe _ = Nothing
          believeTy = Bind (sUN "a") (Pi Nothing (TType (UVar (-2))) (TType (UVar (-1))))
                       (Bind (sUN "b") (Pi Nothing (TType (UVar (-2))) (TType (UVar (-1))))
                         (Bind (sUN "x") (Pi Nothing (V 1) (TType (UVar (-1)))) (V 1)))
          elabBelieveMe
             = do let prim__believe_me = sUN "prim__believe_me"
                  updateContext (addOperator prim__believe_me believeTy 3 p_believeMe)
                  setTotality prim__believe_me (Partial NotCovering)
                  i <- getIState
                  putIState i {
                      idris_scprims = (prim__believe_me, (3, LNoOp)) : idris_scprims i
                    }

          p_synEq [t,_,x,y]
               | x == y = Just (VApp (VApp vnJust VErased)
                                (VApp (VApp vnRefl t) x))
               | otherwise = Just (VApp vnNothing VErased)
          p_synEq args = Nothing

          nMaybe = P (TCon 0 2) (sNS (sUN "Maybe") ["Maybe", "Prelude"]) Erased
          vnJust = VP (DCon 1 2 False) (sNS (sUN "Just") ["Maybe", "Prelude"]) VErased
          vnNothing = VP (DCon 0 1 False) (sNS (sUN "Nothing") ["Maybe", "Prelude"]) VErased
          vnRefl = VP (DCon 0 2 False) eqCon VErased

          synEqTy = Bind (sUN "a") (Pi Nothing (TType (UVar (-3))) (TType (UVar (-2))))
                     (Bind (sUN "b") (Pi Nothing (TType (UVar (-3))) (TType (UVar (-2))))
                      (Bind (sUN "x") (Pi Nothing (V 1) (TType (UVar (-2))))
                       (Bind (sUN "y") (Pi Nothing (V 1) (TType (UVar (-2))))
                         (mkApp nMaybe [mkApp (P (TCon 0 4) eqTy Erased)
                                               [V 3, V 2, V 1, V 0]]))))
          elabSynEq
             = do let synEq = sUN "prim__syntactic_eq"

                  updateContext (addOperator synEq synEqTy 4 p_synEq)
                  setTotality synEq (Total [])
                  i <- getIState
                  putIState i {
                     idris_scprims = (synEq, (4, LNoOp)) : idris_scprims i
                    }


elabDecls :: ElabInfo -> [PDecl] -> Idris ()
elabDecls info ds = do mapM_ (elabDecl EAll info) ds

elabDecl :: ElabWhat -> ElabInfo -> PDecl -> Idris ()
elabDecl what info d
    = let info' = info { rec_elabDecl = elabDecl' } in
          idrisCatch (withErrorReflection $ elabDecl' what info' d) (setAndReport)

elabDecl' _ info (PFix _ _ _)
     = return () -- nothing to elaborate
elabDecl' _ info (PSyntax _ p)
     = return () -- nothing to elaborate
elabDecl' what info (PTy doc argdocs s f o n ty)
  | what /= EDefns
    = do iLOG $ "Elaborating type decl " ++ show n ++ show o
         elabType info s doc argdocs f o n ty
         return ()
elabDecl' what info (PPostulate b doc s f o n ty)
  | what /= EDefns
    = do iLOG $ "Elaborating postulate " ++ show n ++ show o
         if b 
            then elabExtern info s doc f o n ty
            else elabPostulate info s doc f o n ty
elabDecl' what info (PData doc argDocs s f co d)
  | what /= ETypes
    = do iLOG $ "Elaborating " ++ show (d_name d)
         elabData info s doc argDocs f co d
  | otherwise
    = do iLOG $ "Elaborating [type of] " ++ show (d_name d)
         elabData info s doc argDocs f co (PLaterdecl (d_name d) (d_tcon d))
elabDecl' what info d@(PClauses f o n ps)
  | what /= ETypes
    = do iLOG $ "Elaborating clause " ++ show n
         i <- getIState -- get the type options too
         let o' = case lookupCtxt n (idris_flags i) of
                    [fs] -> fs
                    [] -> []
         elabClauses info f (o ++ o') n ps
elabDecl' what info (PMutual f ps)
    = do case ps of
              [p] -> elabDecl what info p
              _ -> do mapM_ (elabDecl ETypes info) ps
                      mapM_ (elabDecl EDefns info) ps
         -- record mutually defined data definitions
         let datans = concatMap declared (filter isDataDecl ps)
         mapM_ (setMutData datans) datans
         iLOG $ "Rechecking for positivity " ++ show datans
         mapM_ (\x -> do setTotality x Unchecked) datans
         -- Do totality checking after entire mutual block
         i <- get
         mapM_ (\n -> do logLvl 5 $ "Simplifying " ++ show n
                         updateContext (simplifyCasedef n $ getErasureInfo i))
                 (map snd (idris_totcheck i))
         mapM_ buildSCG (idris_totcheck i)
         mapM_ checkDeclTotality (idris_totcheck i)
         clear_totcheck
  where isDataDecl (PData _ _ _ _ _ _) = True
        isDataDecl _ = False

        setMutData ns n
           = do i <- getIState
                case lookupCtxt n (idris_datatypes i) of
                   [x] -> do let x' = x { mutual_types = ns }
                             putIState $ i { idris_datatypes
                                                = addDef n x' (idris_datatypes i) }
                   _ -> return ()

elabDecl' what info (PParams f ns ps)
    = do i <- getIState
         iLOG $ "Expanding params block with " ++ show ns ++ " decls " ++
                show (concatMap tldeclared ps)
         let nblock = pblock i
         mapM_ (elabDecl' what info) nblock
  where
    pinfo = let ds = concatMap tldeclared ps
                newps = params info ++ ns
                dsParams = map (\n -> (n, map fst newps)) ds
                newb = addAlist dsParams (inblock info) in
                info { params = newps,
                       inblock = newb }
    pblock i = map (expandParamsD False i id ns
                      (concatMap tldeclared ps)) ps

elabDecl' what info (PNamespace n ps) = mapM_ (elabDecl' what ninfo) ps
  where
    ninfo = case namespace info of
                Nothing -> info { namespace = Just [n] }
                Just ns -> info { namespace = Just (n:ns) }
elabDecl' what info (PClass doc s f cs n ps pdocs fds ds)
  | what /= EDefns
    = do iLOG $ "Elaborating class " ++ show n
         elabClass info (s { syn_params = [] }) doc f cs n ps pdocs fds ds
elabDecl' what info (PInstance doc argDocs s f cs n ps t expn ds)
    = do iLOG $ "Elaborating instance " ++ show n
         elabInstance info s doc argDocs what f cs n ps t expn ds
elabDecl' what info (PRecord doc s f tyn ty opts cdoc cn cty)
  | what /= ETypes
    = do iLOG $ "Elaborating record " ++ show tyn
         elabRecord info s doc f tyn ty opts cdoc cn cty
  | otherwise
    = do iLOG $ "Elaborating [type of] " ++ show tyn
         elabData info s doc [] f [] (PLaterdecl tyn ty)
elabDecl' _ info (PDSL n dsl)
    = do i <- getIState
         putIState (i { idris_dsls = addDef n dsl (idris_dsls i) })
         addIBC (IBCDSL n)
elabDecl' what info (PDirective i)
  | what /= EDefns = i
elabDecl' what info (PProvider doc syn fc provWhat n)
  | what /= EDefns
    = do iLOG $ "Elaborating type provider " ++ show n
         elabProvider doc info syn fc provWhat n
elabDecl' what info (PTransform fc safety old new)
    = do elabTransform info fc safety old new
         return ()
elabDecl' _ _ _ = return () -- skipped this time

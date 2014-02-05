{-# LANGUAGE PatternGuards #-}

module Idris.Erasure
    ( buildDepMap
    , minimalUsage
    ) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.TT
import Idris.Core.Evaluate

import Debug.Trace
import System.IO.Unsafe

import Control.Arrow
import Control.Applicative
import Control.Monad.State
import Data.Maybe
import Data.List
import qualified Data.Set as S
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.Set (Set)
import Data.IntSet (IntSet)
import Data.Map (Map)
import Data.IntMap (IntMap)
import Data.Text (pack)

-- UseMap maps names to the set of used (reachable) argument positions.
type UseMap = Map Name IntSet

data Arg = Arg !Int | Result deriving (Eq, Ord)

instance Show Arg where
    show (Arg i) = show i
    show Result  = "*"

type Node = (Name, Arg)
type Deps = Map Cond (Set Node)

-- "Condition" is the conjunction
-- of elementary assumptions along the path from the root.
-- Elementary assumption (f, i) means that "function f uses the argument i".
type Cond = Set Node

-- Every variable draws in certain dependencies.
type Var = Set Node
type Vars = Map Name Var

-- Find the minimal consistent usage by forward chaining.
minimalUsage :: Deps -> (Deps, (Set Name, UseMap))
minimalUsage = second gather . forwardChain
  where
    gather :: Set (Name, Arg) -> (Set Name, UseMap)
    gather = foldr ins (S.empty, M.empty) . S.toList 
       where
        ins :: Node -> (Set Name, UseMap) -> (Set Name, UseMap)
        ins (n, Result) (ns, umap) = (S.insert n ns, umap)
        ins (n, Arg i ) (ns, umap) = (ns, M.insertWith IS.union n (IS.singleton i) umap)

forwardChain :: Deps -> (Deps, Set Node)
forwardChain deps
    | Just trivials <- M.lookup S.empty deps 
        = (trivials `S.union`) `second` forwardChain (remove trivials . M.delete S.empty $ deps)
    | otherwise = (deps, S.empty)
  where
    -- Remove the given nodes from the Deps entirely,
    -- possibly creating new empty Conds.
    remove :: Set Node -> Deps -> Deps
    remove ns = M.mapKeysWith S.union (S.\\ ns)

-- Build the dependency graph,
-- starting the depth-first search from a list of Names.
buildDepMap :: Ctxt ClassInfo -> Context -> [Name] -> Deps
buildDepMap ci ctx ns = addPostulates $ dfs S.empty M.empty ns
  where
    -- mark the result of Main.main as used with the empty assumption
    addPostulates :: Deps -> Deps
    addPostulates deps = foldr (\(ds, rs) -> M.insertWith S.union ds rs) deps postulates
      where
        -- mini-DSL for postulates
        (==>) ds rs = (S.fromList ds, S.fromList rs)
        (.:) ms n = NS (UN $ pack n) (map pack $ reverse ms)
        it n is = [(UN $ pack n, Arg i) | i <- is]
        mn n is = [(MN 0 $ pack n, Arg i) | i <- is]

        postulates = 
            [ [] ==> concat
                [ [(["Main"] .: "main",  Result)] -- These two, Main.main and run__IO, are always evaluated
                , [(UN (pack "run__IO"), Result)] -- but evade analysis since they come from the seed term.
                , it "prim__believe_me" [2]
                , it "prim__strCons"    [0,1]
                , it "prim__strHead"    [0]
                , it "prim__strTail"    [0]
                , it "prim_lenString"   [0]    -- not a typo, just a single underscore
                , it "prim__concat"     [0,1]
                , it "mkForeignPrim"    [2]
                , it "mkForeign"        [1]
                , it "prim__toStrBigInt"    [0]
                , it "prim__addBigInt"      [0,1]
                , it "prim__sextInt_BigInt" [0]
                , it "prim__zextInt_BigInt" [0]
                , it "prim__eqString"       [0,1]
                , it "prim__eqChar"         [0,1]
                , it "prim__eqBigInt"       [0,1]
                , mn "__MkPair" [0,1]
                ]  
            ]

    -- perform depth-first search
    -- to discover all the names used in the program
    -- and call getDeps for every name
    dfs :: Set Name -> Deps -> [Name] -> Deps
    dfs visited deps [] = deps
    dfs visited deps (n : ns)
        | n `S.member` visited = dfs visited deps ns
        | otherwise = dfs (S.insert n visited) (M.unionWith S.union deps' deps) (next ++ ns)
      where
        next = [n | n <- S.toList depn, n `S.notMember` visited]
        depn = S.delete n $ depNames deps'
        deps' = getDeps n

        -- extract all names that a function depends on
        -- from the Deps of the function
        depNames :: Deps -> Set Name
        depNames = S.unions . map names . M.toList
          where
            names (cs, ns) = S.map fst cs `S.union` S.map fst ns

    -- get Deps for a Name
    getDeps :: Name -> Deps
    getDeps n = case lookupDef n ctx of
        [def] -> getDepsDef n def
        []    -> error $ "erasure checker: unknown reference: " ++ show n
        _     -> error $ "erasure checker: ambiguous reference: " ++ show n

    getDepsDef :: Name -> Def -> Deps
    getDepsDef fn (Function ty t) = error "a function encountered"  -- TODO
    getDepsDef fn (TyDecl   ty t) = M.empty
    getDepsDef fn (Operator ty n' f) = M.empty
    getDepsDef fn (CaseOp ci ty tys def tot cdefs)
        = getDepsSC fn etaVars (etaMap `M.union` varMap) sc
      where
        -- we must eta-expand the definition with fresh variables
        -- to capture these dependencies as well
        etaIdx = [length vars .. length tys - 1]
        etaVars = [eta i | i <- etaIdx]
        etaMap = M.fromList [(eta i, S.singleton (fn, Arg i)) | i <- etaIdx]
        eta i = MN i (pack "eta")

        -- the variables that arose as function arguments only depend on (n, i)
        varMap = M.fromList [(v, S.singleton (fn, Arg i)) | (v,i) <- zip vars [0..]]
        (vars, sc) = cases_runtime cdefs
            -- we use cases_runtime in order to have case-blocks
            -- resolved to top-level functions before our analysis

    etaExpand :: [Name] -> Term -> Term
    etaExpand []       t = t
    etaExpand (n : ns) t = etaExpand ns (App t (P Ref n Erased))

    getDepsSC :: Name -> [Name] -> Vars -> SC -> Deps
    getDepsSC fn es vs (STerm t)
        | show fn == "SN.I-Char instance of NS.Prelude.Classes.UN:\"Ord\""
        , ("ORDINST", fn, t) `traceShow` True
        , "===" `traceShow` True
        , unsafePerformIO (mapM_ print . M.toList $ getDepsTerm vs [] (S.singleton (fn, Result)) (etaExpand es t)) `traceShow` True
        , "===" `traceShow` False
        = undefined
    getDepsSC fn es vs  ImpossibleCase     = M.empty
    getDepsSC fn es vs (UnmatchedCase msg) = M.empty
    getDepsSC fn es vs (ProjCase t alt)    = error "ProjCase not supported"
    getDepsSC fn es vs (STerm    t)        = getDepsTerm vs [] (S.singleton (fn, Result)) (etaExpand es t)
    getDepsSC fn es vs (Case     n alts)
        -- we case-split on this variable, which necessarily marks it as used
        -- hence we add a new dependency whose only preconditions are that the result
        -- of this function is used at all
        = M.insertWith S.union (S.singleton (fn, Result)) casedVar -- add this dep to all deps
            $ unionMap (getDepsAlt fn es vs casedVar) alts  -- coming from the whole subtree
      where
        -- TODO: use effect instead of casedVar to mark the ctor tag
        -- effect    = S.insert (typeName, Result) casedVar  -- mark the tag of the type name as used
        casedVar  = fromMaybe (error $ "nonpatvar in case: " ++ show n) (M.lookup n vs)

    getDepsAlt :: Name -> [Name] -> Vars -> Var -> CaseAlt -> Deps
    getDepsAlt fn es vs var (FnCase n ns sc) = error "an FnCase encountered"  -- TODO: what's this?
    getDepsAlt fn es vs var (ConstCase c sc) = getDepsSC fn es vs sc
    getDepsAlt fn es vs var (DefaultCase sc) = getDepsSC fn es vs sc
    getDepsAlt fn es vs var (SucCase   n sc)
        = getDepsSC fn es (M.insert n var vs) sc -- we're not inserting the S-dependency here because it's special-cased
    getDepsAlt fn es vs var (ConCase n cnt ns sc)
        = getDepsSC fn es (vs' `M.union` vs) sc  -- left-biased union
      where
        -- Here we insert dependencies that arose from pattern matching on a constructor.
        -- n = ctor name, j = ctor arg#, i = fun arg# of the cased var, cs = ctors of the cased var
        vs' = M.fromList [(v, S.insert (n, Arg j) var) | (v,j) <- zip ns [0..]]

    -- Named variables -> DeBruijn variables -> Conds/guards -> Term -> Deps
    getDepsTerm :: Vars -> [Cond -> Deps] -> Cond -> Term -> Deps

    -- named variables introduce dependencies as described in `vs'
    getDepsTerm vs bs cd (P _ n _)
        -- local variables
        | Just var <- M.lookup n vs
        = M.singleton cd var

        -- sanity check: machine-generated names shouldn't occur at top-level
        | MN _ _ <- n
        , show n `notElem` specialMNs
        = error $ "erasure analysis: variable " ++ show n ++ " unbound in " ++ show (S.toList cd)

        -- assumed to be a global reference
        | otherwise = M.singleton cd (S.singleton (n, Result))
      where
        specialMNs = words "{__Unit0}"
    
    -- dependencies of de bruijn variables are described in `bs'
    getDepsTerm vs bs cd (V i) = (bs !! i) cd

    getDepsTerm vs bs cd (Bind n bdr t)
        -- here we just push IM.empty on the de bruijn stack
        -- the args will be marked as used at the usage site
        | Lam ty <- bdr = getDepsTerm vs (const M.empty : bs) cd t
        | Pi  ty <- bdr = getDepsTerm vs (const M.empty : bs) cd t

        -- let-bound variables can get partially evaluated
        -- it is sufficient just to plug the Cond in when the bound names are used
        |  Let ty t <- bdr = getDepsTerm vs (var t : bs) cd t
        | NLet ty t <- bdr = getDepsTerm vs (var t : bs) cd t
      where
        var t cd = getDepsTerm vs bs cd t

    -- applications may add items to Cond
    getDepsTerm vs bs cd app@(App _ _)
        | (fun, args) <- unApply app = case fun of
            -- constructors
            P (TCon _ _) n _ -> unconditionalDeps args  -- does not depend on anything
            P (DCon _ _) n _ -> node n args             -- depends on whether (n,#) is used

            -- a bound variable might draw in additional dependencies,
            -- think: f x = x 0  <-- here, `x' _is_ used
            P _ n _
                | Just var <- M.lookup n vs
                    -> var `ins` unconditionalDeps args
                | otherwise
                    -> node n args  -- depends on whether the referred thing uses its argument

            -- we interpret applied lambdas as lets in order to reuse code here
            Bind n (Lam ty) t -> getDepsTerm vs bs cd (lamToLet [] app)

            -- and we interpret applied lets as lambdas
            Bind n ( Let ty t') t -> getDepsTerm vs bs cd (App (Bind n (Lam ty) t) t')
            Bind n (NLet ty t') t -> getDepsTerm vs bs cd (App (Bind n (Lam ty) t) t')

            -- TODO: figure out what to do with methods
            -- the following code marks them as completely used
            Proj (P Ref n@(SN (InstanceN className parms)) _) i
                | [CI ctorName ms ds dscs ps is] <- lookupCtxt className ci
                    -> S.fromList [(ctorName, Arg i), (n, Result)]
                         `ins` unconditionalDeps args

            Proj t i
                -> error $ "cannot analyse projection !" ++ show i ++ " of " ++ show t

            _ -> error $ "cannot analyse application of " ++ show fun ++ " to " ++ show args
      where
        ins = M.insertWith S.union cd
        node n = ins (S.singleton (n, Result)) . unionMap (getDepsArgs n) . zip [0..]
        getDepsArgs n (i, t) = getDepsTerm vs bs (S.insert (n, Arg i) cd) t
        unconditionalDeps args = unionMap (getDepsTerm vs bs cd) args

    -- projections (= methods)
    getDepsTerm vs bs cd (Proj t i) = getDepsTerm vs bs cd t  -- TODO?

    -- the easy cases
    getDepsTerm vs bs cd (Constant _) = M.empty
    getDepsTerm vs bs cd (TType    _) = M.empty
    getDepsTerm vs bs cd  Erased      = M.empty
    getDepsTerm vs bs cd  Impossible  = M.empty

    getDepsTerm vs bs cd t = error $ "cannot get deps of: " ++ show t

    -- convert applications of lambdas to lets
    -- Note that this transformation preserves de bruijn numbering
    lamToLet :: [Term] -> Term -> Term
    lamToLet    xs  (App f x)           = lamToLet (x:xs) f
    lamToLet (x:xs) (Bind n (Lam ty) t) = Bind n (Let ty x) (lamToLet xs t)
    lamToLet (x:xs)  t                  = App (lamToLet xs t) x
    lamToLet    []   t                  = t

    unions :: [Deps] -> Deps
    unions = M.unionsWith S.union

    unionMap :: (a -> Deps) -> [a] -> Deps
    unionMap f = unions . map f

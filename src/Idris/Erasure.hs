{-# LANGUAGE PatternGuards #-}

module Idris.Erasure
    ( findUnusedArgs
    , buildDepMap
    , minimalUsage
    ) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.TT
import Idris.Core.Evaluate

import Debug.Trace

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

-- UseMap maps names to the set of used (reachable) argument positions.
type UseMap = Map Name IntSet

-- DepMap maps functions (only functions) to their Deps.
type DepMap = Map Name Deps

type Node = (Name, Int)
type FlatMap = Map Node (Set (Ctors, Cond))

-- Deps of a function is a map from argument index
-- to all usages of the argument, including conditions
-- and which constructor fields the particular usage touched.
type Deps = IntMap (Set (Ctors, Cond))

-- "Condition" is the conjunction
-- of elementary assumptions along the path from the root.
-- Elementary assumption (f, i) means that "function f uses the argument i".
type Cond = Set (Name, Int)

-- "Ctors" is the set of pairs (ctor_name, arg_no) saying
-- which constructor fields have been accessed to obtain the variable.
type Ctors = Set (Name, Int)

-- Variables used in terms.
type Var = Cond -> Deps
type Vars = Map Name Var

-- Variables passing the pattern-matches before being used in terms.
type PatVar = Ctors -> Var
type PatVars = Map Name PatVar

-- Find the minimal consistent usage by forward chaining.
minimalUsage :: DepMap -> UseMap
minimalUsage dmap = gather reachable
  where
    flatten :: DepMap -> FlatMap
    flatten dmap = M.fromList $ concat [[((n,i), ccs) | (i, ccs) <- IM.toList deps] | (n, deps) <- M.toList dmap]

    gather :: Ord a => Set (a, Int) -> Map a IntSet
    gather = foldr (\(n,i) -> M.insertWith IS.union n (IS.singleton i)) M.empty . S.toList 

    reachable :: Set Node
    reachable = forwardChain $ flatten dmap

    -- TODO: final pass to find out the constructors
    -- (cannot be done on the fly because new reasons can be discovered after the rule has been triggered)

forwardChain :: FlatMap -> Set Node
forwardChain dmap 
    | S.null trivials = S.empty 
    | otherwise = trivials `S.union` forwardChain (remove trivials dmap)
  where
    -- Remove the given nodes from the FlatMap entirely, including from Conds,
    -- possibly creating new empty Conds.
    remove :: Set Node -> FlatMap -> FlatMap
    remove ns = M.mapMaybeWithKey rm
      where
        rm :: Node -> Set (Ctors, Cond) -> Maybe (Set (Ctors, Cond))
        rm n ccs | n `S.member` ns = Nothing
        rm n ccs = Just $ S.map (second (S.\\ ns)) ccs

    trivials :: Set Node
    trivials = S.fromList . map fst . filter isTrivial . M.toList $ dmap

    -- A node is trivially reachable if it has at least one trivial (empty) Cond.
    isTrivial :: (Node, Set (Ctors, Cond)) -> Bool
    isTrivial (node, alts) = not . S.null $ trivialConds
      where
        trivialConds :: Set (Ctors, Cond)
        trivialConds = S.filter (S.null . snd) alts

-- Build the dependency graph,
-- starting the depth-first search from a list of Names.
buildDepMap :: Context -> [Name] -> DepMap
buildDepMap ctx ns = dfs M.empty ns
  where
    -- perform depth-first search
    -- to discover all the names used in the program
    -- and call getDeps for every name
    dfs :: DepMap -> [Name] -> DepMap
    dfs dmap [] = dmap
    dfs dmap (n : ns)
        | n `M.member` dmap = dfs dmap ns
        | otherwise         = dfs (M.insert n deps dmap) ns
      where
        next = [n | n <- S.toList depn, n `M.notMember` dmap]
        depn = S.delete n (depNames deps)
        deps = getDeps n

    -- extract all names that a function depends on
    -- from the Deps of the function
    depNames :: Deps -> Set Name
    depNames = S.unions . map (S.unions . map f . S.toList) . IM.elems
      where
        f :: (Ctors, Cond) -> Set Name
        f (ctors, cond) = S.map fst cond  -- let's ignore ctors for now

    -- get Deps for a Name
    getDeps :: Name -> Deps
    getDeps n = case lookupDef n ctx of
        [def] -> getDepsDef def
        []    -> error $ "erasure checker: unknown name: " ++ show n
        _     -> error $ "erasure checker: ambiguous name: " ++ show n

    getDepsDef :: Def -> Deps
    getDepsDef (Function ty t) = error "a function encountered"  -- TODO
    getDepsDef (TyDecl   ty t) = IM.empty
    getDepsDef (Operator ty n f) = IM.empty
    getDepsDef (CaseOp ci ty tys def tot cdefs)
        = getDepsSC varMap sc
      where
        pvar i cs cd = IM.singleton i (S.singleton (cs, cd))
        varMap = M.fromList [(v, pvar i) | (v,i) <- zip vars [0..]]
        (vars, sc) = cases_compiletime cdefs  -- TODO: or cases_runtime?

    getDepsSC :: PatVars -> SC -> Deps
    getDepsSC vs  ImpossibleCase     = IM.empty
    getDepsSC vs (UnmatchedCase msg) = IM.empty
    getDepsSC vs (ProjCase t alt)    = error "ProjCase not supported"
    getDepsSC vs (STerm    t)        = getDepsTerm (M.map ($ S.empty) vs) [] S.empty t
    getDepsSC vs (Case     n alts)   = unionMap (getDepsAlt vs pvar) alts
      where
        pvar  = fromMaybe (error $ "nonpatvar in case: " ++ show n) (M.lookup n vs)

    getDepsAlt :: PatVars -> PatVar -> CaseAlt -> Deps
    getDepsAlt vs pv (FnCase n ns sc) = error "an FnCase encountered"  -- TODO: what's this?
    getDepsAlt vs pv (ConstCase c sc) = getDepsSC vs sc
    getDepsAlt vs pv (SucCase   n sc) = getDepsSC vs sc  -- deps for S can be hardcoded if needed
    getDepsAlt vs pv (DefaultCase sc) = getDepsSC vs sc
    getDepsAlt vs pv (ConCase n cnt ns sc)
        = getDepsSC (vs' `M.union` vs) sc  -- left-biased union
      where
        -- n = ctor name, j = ctor arg#, i = fun arg# of the cased var, cs = ctors of the cased var
        vs' = M.fromList [(v, pv . S.insert (n,j)) | (v,j) <- zip ns [0..]]

    -- Named variables -> DeBruijn variables -> Conds/guards -> Term -> Deps
    getDepsTerm :: Vars -> [Var] -> Cond -> Term -> Deps

    -- named variables introduce dependencies as described in `vs'
    getDepsTerm vs bs cd (P _ n _)
        | Just var <- M.lookup n vs = var cd
        | otherwise = IM.empty

    -- dependencies of de bruijn variables are described in `bs'
    getDepsTerm vs bs cd (V i) = (bs !! i) cd

    getDepsTerm vs bs cd (Bind n bdr t)
        -- here we just push IM.empty on the de bruijn stack
        -- the args will be marked as used at the usage site
        | Lam ty <- bdr = getDepsTerm vs (const IM.empty : bs) cd t
        | Pi  ty <- bdr = getDepsTerm vs (const IM.empty : bs) cd t

        -- let-bound variables can get partially evaluated
        -- it is sufficient just to plug the Cond in when the bound names are used
        |  Let ty v <- bdr = getDepsTerm (M.insert n (var v) vs) (var v : bs) cd t
        | NLet ty v <- bdr = getDepsTerm (M.insert n (var v) vs) (var v : bs) cd t
      where
        var v cd = getDepsTerm vs bs cd v

    -- applications may add items to Cond
    getDepsTerm vs bs cd app@(App _ _)
        | (fun, args) <- unApply app = case fun of
            -- these depend on whether the referred thing uses the argument
            P  Ref       n _ -> called n args
            P (DCon _ _) n _ -> called n args

            -- these do not
            P (TCon _ _) n _ -> unionMap (getDepsTerm vs bs cd) args
            P  Bound     n _ -> unionMap (getDepsTerm vs bs cd) args
      where
        called n args = unionMap (\(i,t) -> getDepsTerm vs bs (S.insert (n,i) cd) t) (zip [0..] args)

    -- the easy cases
    getDepsTerm vs bs cd (Constant _) = IM.empty
    getDepsTerm vs bs cd Erased       = IM.empty
    getDepsTerm vs bs cd Impossible   = IM.empty
    getDepsTerm vs bs cd (TType _)    = IM.empty

    unions :: [Deps] -> Deps
    unions = IM.unionsWith S.union

    unionMap :: (a -> Deps) -> [a] -> Deps
    unionMap f = unions . map f

findUnusedArgs :: [Name] -> Idris ()
findUnusedArgs names = do
    cg <- idris_callgraph <$> getIState
    mapM_ (process cg) names
  where
    process :: Ctxt CGInfo -> Name -> Idris ()
    process cg n = case lookupCtxt n cg of
        [x] -> do
            let unused = traceUnused cg n x 
            logLvl 1 $ show n ++ " unused: " ++ show unused
            addToCG n $ x{ unusedpos = unused }
        _ -> return ()

    traceUnused :: Ctxt CGInfo -> Name -> CGInfo -> [Int]
    traceUnused cg n (CGInfo args calls _ usedns _)
        = findIndices (not . (`elem` fused)) args
      where
        fargs   = concatMap (getFargpos calls) (zip args [0..])
        recused = [n | (n, i, (g,j)) <- fargs, used cg [(n,i)] g j]
        fused   = nub $ usedns ++ recused
        
    used :: Ctxt CGInfo -> [(Name, Int)] -> Name -> Int -> Bool
    used cg path g j
        | (g, j) `elem` path = False -- cycle, never used on the way

        | [CGInfo args calls _ usedns _] <- lookupCtxt g cg
        , j < length args  -- not overapplied
        = let directuse = args!!j `elem` usedns
              garg      = getFargpos calls (args!!j, j)
              recused   = map getUsed garg
          in directuse || or recused
          -- used on any route from here, or not used recursively

        | otherwise = True
      where
        getUsed (argn, j, (g', j')) = used cg ((g,j):path) g' j'

    getFargpos :: [(Name, [[Name]])] -> (Name, Int) -> [(Name, Int, (Name, Int))]
    getFargpos calls (n, i) = concatMap (getCallArgpos n i) calls
      where
        getCallArgpos :: Name -> Int -> (Name, [[Name]]) -> [(Name, Int, (Name, Int))]
        getCallArgpos n i (g, args) = mapMaybe (getOne g) (zip [0..] args)
        
        getOne :: Name -> (Int, [Name]) -> Maybe (Name, Int, (Name, Int))
        getOne g (j, xs)
            | n `elem` xs = Just (n, i, (g, j))
            | otherwise   = Nothing


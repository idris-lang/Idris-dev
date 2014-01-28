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
minimalUsage :: Deps -> UseMap
minimalUsage = gather . forwardChain
  where
    gather :: Set (Name, Arg) -> UseMap
    gather = foldr ins M.empty . S.toList 
       where
        ins :: Node -> UseMap -> UseMap
        ins (n, Result) = id
        ins (n, Arg i ) = M.insertWith IS.union n (IS.singleton i)

forwardChain :: Deps -> Set Node
forwardChain deps
    | Just trivials <- M.lookup S.empty deps 
        = trivials `S.union` forwardChain (remove trivials . M.delete S.empty $ deps)
    | otherwise = S.empty
  where
    -- Remove the given nodes from the Deps entirely,
    -- possibly creating new empty Conds.
    remove :: Set Node -> Deps -> Deps
    remove ns = M.mapKeysWith S.union (S.\\ ns)

-- Build the dependency graph,
-- starting the depth-first search from a list of Names.
buildDepMap :: Context -> [Name] -> Deps
buildDepMap ctx ns = addPostulates $ dfs S.empty M.empty ns
  where
    -- mark the result of Main.main as used with the empty assumption
    addPostulates :: Deps -> Deps
    addPostulates deps = foldr (\(ds, rs) -> M.insertWith S.union ds rs) deps postulates
      where
        -- mini-DSL for postulates
        (==>) ds rs = (S.fromList ds, S.fromList rs)
        (.:) ms n = NS (UN $ pack n) (map pack ms)
        name = UN . pack

        postulates = 
            [ [] ==>
                [ (["Main"] .: "main", Result) -- These two, Main.main and run__IO, are always evaluated
                , (name "run__IO", Result)     -- but evade analysis since they come from the seed term.
                , (name "prim__believe_me", Arg 2)
                , (name "prim__strCons", Arg 0)
                , (name "prim__strCons", Arg 1)
                , (name "prim__strHead", Arg 0)
                , (name "prim__strTail", Arg 0)
                , (name "prim__concat", Arg 0)
                , (name "prim__concat", Arg 1)
                , (name "mkForeignPrim", Arg 2)
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
        []    -> error $ "erasure checker: unknown name: " ++ show n
        _     -> error $ "erasure checker: ambiguous name: " ++ show n

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
        (vars, sc) = cases_compiletime cdefs  -- TODO: or cases_runtime?

    etaExpand :: [Name] -> Term -> Term
    etaExpand []       t = t
    etaExpand (n : ns) t = App (etaExpand ns t) (P Bound n Erased)

    getDepsSC :: Name -> [Name] -> Vars -> SC -> Deps
    getDepsSC fn es vs  ImpossibleCase     = M.empty
    getDepsSC fn es vs (UnmatchedCase msg) = M.empty
    getDepsSC fn es vs (ProjCase t alt)    = error "ProjCase not supported"
    getDepsSC fn es vs (STerm    t)        = getDepsTerm vs [] (S.singleton (fn, Result)) (etaExpand es t)
    getDepsSC fn es vs (Case     n alts)   = unionMap (getDepsAlt fn es vs var) alts
      where
        var  = fromMaybe (error $ "nonpatvar in case: " ++ show n) (M.lookup n vs)

    getDepsAlt :: Name -> [Name] -> Vars -> Var -> CaseAlt -> Deps
    getDepsAlt fn es vs var (FnCase n ns sc) = error "an FnCase encountered"  -- TODO: what's this?
    getDepsAlt fn es vs var (ConstCase c sc) = getDepsSC fn es vs sc
    getDepsAlt fn es vs var (SucCase   n sc) = getDepsSC fn es vs sc  -- deps for S can be hardcoded if needed
    getDepsAlt fn es vs var (DefaultCase sc) = getDepsSC fn es vs sc
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
        | Just var <- M.lookup n vs = M.singleton cd var  -- this condition gives rise to these dependencies
        | otherwise = M.empty

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
            -- these depend on whether the referred thing uses the argument
            P  Ref       n _ -> node n args
            P (DCon _ _) n _ -> node n args

            -- this does not
            P (TCon _ _) n _ -> unionMap (getDepsTerm vs bs cd) args

            -- a bound variable might draw in additional dependencies,
            -- think: f x = x 0  <-- here, `x' _is_ used
            P Bound n _ -> var n `ins` unionMap (getDepsTerm vs bs cd) args

            -- we interpret applied lambdas as lets in order to reuse code here
            Bind n (Lam ty) t -> getDepsTerm vs bs cd (lamToLet [] app)

            -- and we interpret applied lets as lambdas
            Bind n ( Let ty t') t -> getDepsTerm vs bs cd (App (Bind n (Lam ty) t) t')
            Bind n (NLet ty t') t -> getDepsTerm vs bs cd (App (Bind n (Lam ty) t) t')

            _ -> error $ "cannot analyse application of: " ++ show fun
      where
        ins = M.insertWith S.union cd
        var n = fromMaybe (error $ "non-existent bound variable: " ++ show n) (M.lookup n vs)
        node n = ins (S.singleton (n, Result)) . unionMap (getDepsArgs n) . zip [0..]
        getDepsArgs n (i, t) = getDepsTerm vs bs (S.insert (n, Arg i) cd) t

    -- the easy cases
    getDepsTerm vs bs cd (Constant _) = M.empty
    getDepsTerm vs bs cd (TType    _) = M.empty
    getDepsTerm vs bs cd  Erased      = M.empty
    getDepsTerm vs bs cd  Impossible  = M.empty

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

findUnusedArgs :: [Name] -> Idris ()
findUnusedArgs names = do
    cg <- idris_callgraph <$> getIState
    mapM_ (process cg) names
  where
    process :: Ctxt CGInfo -> Name -> Idris ()
    process cg n = case lookupCtxt n cg of
        [x] -> do
            let used = traceUsed cg n x 
            logLvl 1 $ show n ++ " used: " ++ show used
            addToCG n $ x{ usedpos = used }
        _ -> return ()

    traceUsed :: Ctxt CGInfo -> Name -> CGInfo -> [Int]
    traceUsed cg n (CGInfo args calls _ usedns _)
        = findIndices (`elem` fused) args
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


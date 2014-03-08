{-# LANGUAGE PatternGuards #-}

module Idris.Erasure (performUsageAnalysis) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Primitives
import Idris.Error

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
import qualified Data.Text as T

-- UseMap maps names to the set of used (reachable) argument positions.
type UseMap = Map Name (IntMap (Set Reason))

data Arg = Arg Int | Result deriving (Eq, Ord)

instance Show Arg where
    show (Arg i) = show i
    show Result  = "*"

type Node = (Name, Arg)
type Deps = Map Cond DepSet
type Reason = (Name, Int)  -- function name, argument index

-- Nodes along with sets of reasons for every one.
type DepSet = Map Node (Set Reason)

-- "Condition" is the conjunction
-- of elementary assumptions along the path from the root.
-- Elementary assumption (f, i) means that "function f uses the argument i".
type Cond = Set Node

-- Variables carry certain information with them.
data VarInfo = VI
    { viDeps   :: DepSet      -- dependencies drawn in by the variable
    , viFunArg :: Maybe Int   -- which function argument this variable came from (defined only for patvars)
    , viMethod :: Maybe Name  -- name of the method represented by the var, if any
    }
    deriving Show

type Vars = Map Name VarInfo

-- Perform usage analysis, write the relevant information in the internal
-- structures, returning the list of reachable names.
performUsageAnalysis :: Idris [Name]
performUsageAnalysis = do
    ctx <- tt_ctxt <$> getIState

    case lookupCtxt mainName (definitions ctx) of
      [] -> return []  -- no main -> not compiling -> reachability irrelevant
      _  -> do
        ci  <- idris_classes <$> getIState
        cg  <- idris_callgraph <$> getIState
        opt <- idris_optimisation <$> getIState

        -- Build the dependency graph.
        let depMap = buildDepMap ci ctx mainName

        -- Search for reachable nodes in the graph.
        let (residDeps, (reachableNames, minUse)) = minimalUsage depMap
            usage = M.toList minUse

        -- Print some debug info.
        logLvl 5 $ "Original deps:\n" ++ unlines (map fmtItem . M.toList $ depMap)
        logLvl 3 $ "Reachable names:\n" ++ unlines (map (indent . show) . S.toList $ reachableNames)
        logLvl 4 $ "Minimal usage:\n" ++ fmtUseMap usage
        logLvl 5 $ "Residual deps:\n" ++ unlines (map fmtItem . M.toList $ residDeps)

        -- Check that everything reachable is accessible.
        checkEnabled <- (NoWarnReach `notElem`) . opt_cmdline . idris_options <$> getIState
        when checkEnabled $
            mapM_ (checkAccessibility opt) usage

        -- Store the usage info in the internal state.
        mapM_ (storeUsage cg) usage

        return $ S.toList reachableNames
  where
    mainName = sNS (sUN "main") ["Main"]
    indent = ("  " ++)

    fmtItem :: (Cond, DepSet) -> String
    fmtItem (cond, deps) = indent $ show (S.toList cond) ++ " -> " ++ show (M.toList deps)

    fmtUseMap :: [(Name, IntMap (Set Reason))] -> String
    fmtUseMap = unlines . map (\(n,is) -> indent $ show n ++ " -> " ++ fmtIxs is)

    fmtIxs :: IntMap (Set Reason) -> String
    fmtIxs = intercalate ", " . map fmtArg . IM.toList
      where
        fmtArg (i, rs)
            | S.null rs = show i
            | otherwise = show i ++ " from " ++ intercalate ", " (map show $ S.toList rs)

    storeUsage :: Ctxt CGInfo -> (Name, IntMap (Set Reason)) -> Idris ()
    storeUsage cg (n, args)
        | [x] <- lookupCtxt n cg
        = addToCG n x{ usedpos = flat }        -- functions

        | otherwise
        = addToCG n (CGInfo [] [] [] [] flat)  -- data ctors
      where
        flat = [(i, S.toList rs) | (i,rs) <- IM.toList args]

    checkAccessibility :: Ctxt OptInfo -> (Name, IntMap (Set Reason)) -> Idris ()
    checkAccessibility opt (n, reachable)
        | [Optimise col nt forc rec inaccessible dt] <- lookupCtxt n opt
        , eargs@(_:_) <- [fmt n (S.toList rs) | (i,n) <- inaccessible, rs <- maybeToList $ IM.lookup i reachable]
        = warn $ show n ++ ": inaccessible arguments reachable:\n  " ++ intercalate "\n  " eargs

        | otherwise = return ()
      where
        fmt n [] = show n ++ " (no more information available)"
        fmt n rs = show n ++ " from " ++ intercalate ", " [show rn ++ " arg# " ++ show ri | (rn,ri) <- rs]
        warn = logLvl 0

-- Find the minimal consistent usage by forward chaining.
minimalUsage :: Deps -> (Deps, (Set Name, UseMap))
minimalUsage = second gather . forwardChain
  where
    gather :: DepSet -> (Set Name, UseMap)
    gather = foldr ins (S.empty, M.empty) . M.toList
       where
        ins :: (Node, Set Reason) -> (Set Name, UseMap) -> (Set Name, UseMap)
        ins ((n, Result), rs) (ns, umap) = (S.insert n ns, umap)
        ins ((n, Arg i ), rs) (ns, umap) = (ns, M.insertWith (IM.unionWith S.union) n (IM.singleton i rs) umap)

forwardChain :: Deps -> (Deps, DepSet)
forwardChain deps
    | Just trivials <- M.lookup S.empty deps 
        = (M.unionWith S.union trivials)
            `second` forwardChain (remove trivials . M.delete S.empty $ deps)
    | otherwise = (deps, M.empty)
  where
    -- Remove the given nodes from the Deps entirely,
    -- possibly creating new empty Conds.
    remove :: DepSet -> Deps -> Deps
    remove ds = M.mapKeysWith (M.unionWith S.union) (S.\\ M.keysSet ds)

-- Build the dependency graph,
-- starting the depth-first search from a list of Names.
buildDepMap :: Ctxt ClassInfo -> Context -> Name -> Deps
buildDepMap ci ctx mainName = addPostulates $ dfs S.empty M.empty [mainName]
  where
    -- mark the result of Main.main as used with the empty assumption
    addPostulates :: Deps -> Deps
    addPostulates deps = foldr (\(ds, rs) -> M.insertWith (M.unionWith S.union) ds rs) deps postulates
      where
        -- mini-DSL for postulates
        (==>) ds rs = (S.fromList ds, M.fromList [(r, S.empty) | r <- rs])
        it n is = [(sUN n, Arg i) | i <- is]
        mn n is = [(MN 0 $ pack n, Arg i) | i <- is]

        -- believe_me is special because it does not use all its arguments
        specialPrims = S.fromList [sUN "prim__believe_me"]
        usedNames = allNames deps S.\\ specialPrims
        usedPrims = [(p_name p, p_arity p) | p <- primitives, p_name p `S.member` usedNames]

        postulates = 
            [ [] ==> concat
                -- These two, Main.main and run__IO, are always evaluated
                -- but they elude analysis since they come from the seed term.
                [ [(sUN "main" `sNS` ["Main"],  Result)] 
                , [(sUN "run__IO", Result), (sUN "run__IO", Arg 0)]

                -- MkIO is read by run__IO,
                -- but this cannot be observed in the source code of programs.
                , it "MkIO"         [1]
                , it "prim__IO"     [1]

                -- these have been discovered as builtins but are not listed
                -- among Idris.Primitives.primitives
                , mn "__MkPair"     [0,1]
                , it "prim_fork"    [0]

                -- believe_me is a primitive but it only uses its third argument
                -- it is special-cased in usedNames above
                , it "prim__believe_me" [2]
    
                -- in general, all other primitives use all their arguments
                , [(n, Arg i) | (n,arity) <- usedPrims, i <- [0..arity-1]]

                -- mkForeign* functions are special-cased below
                ]
            ]

    -- perform depth-first search
    -- to discover all the names used in the program
    -- and call getDeps for every name
    dfs :: Set Name -> Deps -> [Name] -> Deps
    dfs visited deps [] = deps
    dfs visited deps (n : ns)
        | n `S.member` visited = dfs visited deps ns
        | otherwise = dfs (S.insert n visited) (M.unionWith (M.unionWith S.union) deps' deps) (next ++ ns)
      where
        next = [n | n <- S.toList depn, n `S.notMember` visited]
        depn = S.delete n $ allNames deps'
        deps' = getDeps n

    -- extract all names that a function depends on
    -- from the Deps of the function
    allNames :: Deps -> Set Name
    allNames = S.unions . map names . M.toList
        where
        names (cs, ns) = S.map fst cs `S.union` S.map fst (M.keysSet ns)

    -- get Deps for a Name
    getDeps :: Name -> Deps
    getDeps (SN (WhereN i (SN (InstanceCtorN classN)) (MN i' field)))
        = M.empty  -- these deps are created when applying instance ctors
    getDeps n = case lookupDef n ctx of
        [def] -> getDepsDef n def
        []    -> error $ "erasure checker: unknown reference: " ++ show n
        _     -> error $ "erasure checker: ambiguous reference: " ++ show n

    getDepsDef :: Name -> Def -> Deps
    getDepsDef fn (Function ty t) = error "a function encountered"  -- TODO
    getDepsDef fn (TyDecl   ty t) = M.empty
    getDepsDef fn (Operator ty n' f) = M.empty  -- TODO: what's this?
    getDepsDef fn (CaseOp ci ty tys def tot cdefs)
        = getDepsSC fn etaVars (etaMap `M.union` varMap) sc
      where
        -- we must eta-expand the definition with fresh variables
        -- to capture these dependencies as well
        etaIdx = [length vars .. length tys - 1]
        etaVars = [eta i | i <- etaIdx]
        etaMap = M.fromList [varPair (eta i) i | i <- etaIdx]
        eta i = MN i (pack "eta")

        -- the variables that arose as function arguments only depend on (n, i)
        varMap = M.fromList [varPair v i | (v,i) <- zip vars [0..]]

        varPair n argNo = (n, VI
            { viDeps   = M.singleton (fn, Arg argNo) S.empty
            , viFunArg = Just argNo
            , viMethod = Nothing
            })

        (vars, sc) = cases_runtime cdefs
            -- we use cases_runtime in order to have case-blocks
            -- resolved to top-level functions before our analysis

    etaExpand :: [Name] -> Term -> Term
    etaExpand []       t = t
    etaExpand (n : ns) t = etaExpand ns (App t (P Ref n Erased))

    getDepsSC :: Name -> [Name] -> Vars -> SC -> Deps
    getDepsSC fn es vs  ImpossibleCase     = M.empty
    getDepsSC fn es vs (UnmatchedCase msg) = M.empty
    getDepsSC fn es vs (ProjCase t alt)    = error "ProjCase not supported"
    getDepsSC fn es vs (STerm    t)        = getDepsTerm vs [] (S.singleton (fn, Result)) (etaExpand es t)
    getDepsSC fn es vs (Case n alts)
        -- we case-split on this variable, which marks it as used
        -- (unless there is exactly one case branch)
        -- hence we add a new dependency, whose only precondition is
        -- that the result of this function is used at all
        = addTagDep $ unionMap (getDepsAlt fn es vs casedVar) alts  -- coming from the whole subtree
      where
        
        addTagDep = case alts of
            [_] -> id  -- single branch, tag not used
            _   -> M.insertWith (M.unionWith S.union) (S.singleton (fn, Result)) (viDeps casedVar)
        casedVar  = fromMaybe (error $ "nonpatvar in case: " ++ show n) (M.lookup n vs)

    getDepsAlt :: Name -> [Name] -> Vars -> VarInfo -> CaseAlt -> Deps
    getDepsAlt fn es vs var (FnCase n ns sc) = error "an FnCase encountered"  -- TODO: what's this?
    getDepsAlt fn es vs var (ConstCase c sc) = getDepsSC fn es vs sc
    getDepsAlt fn es vs var (DefaultCase sc) = getDepsSC fn es vs sc
    getDepsAlt fn es vs var (SucCase   n sc)
        = getDepsSC fn es (M.insert n var vs) sc -- we're not inserting the S-dependency here because it's special-cased

    -- data constructors
    getDepsAlt fn es vs var (ConCase n cnt ns sc)
        = getDepsSC fn es (vs' `M.union` vs) sc  -- left-biased union
      where
        -- Here we insert dependencies that arose from pattern matching on a constructor.
        -- n = ctor name, j = ctor arg#, i = fun arg# of the cased var, cs = ctors of the cased var
        vs' = M.fromList [(v, VI
            { viDeps   = M.insertWith S.union (n, Arg j) (S.singleton (fn, varIdx)) (viDeps var)
            , viFunArg = viFunArg var
            , viMethod = m
            })
          | (v, j, m) <- zip3 ns [0..] methodNames]
        
        -- this is safe because it's certainly a patvar
        varIdx = fromJust (viFunArg var)

        -- figure out method names, if "n" is an instance ctor
        methodNames :: [Maybe Name]
        methodNames = case n of
            SN (InstanceCtorN className)
                | Just cinfo <- lookupCtxtExact className ci
                -> let methNames = map fst $ class_methods cinfo
                    in replicate (length ns - length methNames) Nothing  -- initial type args to the instance ctor
                        ++ map Just methNames                            -- methods proper

                | otherwise
                -> error $ "could not find class for the instance ctor " ++ show n

            _ -> repeat Nothing

    -- Named variables -> DeBruijn variables -> Conds/guards -> Term -> Deps
    getDepsTerm :: Vars -> [Cond -> Deps] -> Cond -> Term -> Deps

    -- named variables introduce dependencies as described in `vs'
    getDepsTerm vs bs cd (P _ n _)
        -- local variables
        | Just var <- M.lookup n vs
        = M.singleton cd (viDeps var)

        -- sanity check: machine-generated names shouldn't occur at top-level
        | MN _ _ <- n
        , n `notElem` specialMNs
        = error $ "erasure analysis: variable " ++ show n ++ " unbound in " ++ show (S.toList cd)

        -- assumed to be a global reference
        | otherwise = M.singleton cd (M.singleton (n, Result) S.empty)
      where
        specialMNs = map (sMN 0 . ("__" ++)) $ words "Unit True False II"
    
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

            -- mkForeign* calls must be special-cased because they are variadic
            -- All arguments must be marked as used, except for the first one,
            -- which is the (Foreign a) spec that defines the type
            -- and is not needed at runtime.
            P _ (UN n) _
                | n `elem` map T.pack ["mkForeign", "mkForeignPrim", "mkLazyForeignPrim"]
                -> unconditionalDeps (drop 1 args)

            -- a bound variable might draw in additional dependencies,
            -- think: f x = x 0  <-- here, `x' _is_ used
            P _ n _
                -- local name that refers to a method
                | Just var  <- M.lookup n vs
                , Just meth <- viMethod var
                    -> node meth args  -- use the method instead

                -- local name
                | Just var <- M.lookup n vs
                    -- unconditional use
                    -> viDeps var `ins` unconditionalDeps args

                -- global name
                | otherwise
                    -- depends on whether the referred thing uses its argument
                    -> node n args

            -- TODO: could we somehow infer how bound variables use their arguments?
            V i -> M.unionWith (M.unionWith S.union) ((bs !! i) cd) (unconditionalDeps args)

            -- we interpret applied lambdas as lets in order to reuse code here
            Bind n (Lam ty) t -> getDepsTerm vs bs cd (lamToLet [] app)

            -- and we interpret applied lets as lambdas
            Bind n ( Let ty t') t -> getDepsTerm vs bs cd (App (Bind n (Lam ty) t) t')
            Bind n (NLet ty t') t -> getDepsTerm vs bs cd (App (Bind n (Lam ty) t) t')

            Proj t i
                -> error $ "cannot[0] analyse projection !" ++ show i ++ " of " ++ show t

            Erased -> M.empty

            _ -> error $ "cannot analyse application of " ++ show fun ++ " to " ++ show args
      where
        ins = M.insertWith (M.unionWith S.union) cd
        unconditionalDeps args = unionMap (getDepsTerm vs bs cd) args

        node :: Name -> [Term] -> Deps
        node n = ins (M.singleton (n, Result) S.empty) . unionMap (getDepsArgs n) . zip indices
          where
            indices = map Just [0 .. getArity n - 1] ++ repeat Nothing
            getDepsArgs n (Just i,  t) = getDepsTerm vs bs (S.insert (n, Arg i) cd) t  -- conditional
            getDepsArgs n (Nothing, t) = getDepsTerm vs bs cd t                        -- unconditional

    -- projections
    getDepsTerm vs bs cd (Proj t (-1)) = getDepsTerm vs bs cd t  -- naturals, (S n) -> n
    getDepsTerm vs bs cd (Proj t i) = error $ "cannot[1] analyse projection !" ++ show i ++ " of " ++ show t

    -- the easy cases
    getDepsTerm vs bs cd (Constant _) = M.empty
    getDepsTerm vs bs cd (TType    _) = M.empty
    getDepsTerm vs bs cd  Erased      = M.empty
    getDepsTerm vs bs cd  Impossible  = M.empty

    getDepsTerm vs bs cd t = error $ "cannot get deps of: " ++ show t

    -- Get the number of arguments that might be considered for erasure.
    getArity :: Name -> Int
    getArity n = case lookupDef n ctx of
        [CaseOp ci ty tys def tot cdefs] -> length tys
        [TyDecl (DCon tag arity) _]      -> arity
        [TyDecl (Ref) ty]                -> length $ getArgTys ty
        [Operator ty arity op]           -> arity
        [] -> error $ "Erasure/getArity: definition not found for " ++ show n
        df -> error $ "Erasure/getArity: unrecognised entity '"
                        ++ show n ++ "' with definition: "  ++ show df

    -- convert applications of lambdas to lets
    -- Note that this transformation preserves de bruijn numbering
    lamToLet :: [Term] -> Term -> Term
    lamToLet    xs  (App f x)           = lamToLet (x:xs) f
    lamToLet (x:xs) (Bind n (Lam ty) t) = Bind n (Let ty x) (lamToLet xs t)
    lamToLet (x:xs)  t                  = App (lamToLet xs t) x
    lamToLet    []   t                  = t

    mkField :: Name -> Int -> Name
    mkField ctorName fieldNo = SN (WhereN fieldNo ctorName $ sMN fieldNo "field")

    union :: Deps -> Deps -> Deps
    union = M.unionWith (M.unionWith S.union)

    unions :: [Deps] -> Deps
    unions = M.unionsWith (M.unionWith S.union)

    unionMap :: (a -> Deps) -> [a] -> Deps
    unionMap f = M.unionsWith (M.unionWith S.union) . map f

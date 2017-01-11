{-|
Module      : Idris.Erasure
Description : Utilities to erase irrelevant stuff.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}

module Idris.Erasure (performUsageAnalysis, mkFieldName) where

import Idris.AbsSyntax
import Idris.ASTUtils
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Error
import Idris.Primitives

import Prelude hiding (id, (.))

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Monad.State
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (pack)
import qualified Data.Text as T
import Debug.Trace
import System.IO.Unsafe

-- | UseMap maps names to the set of used (reachable) argument
-- positions.
type UseMap = Map Name (IntMap (Set Reason))

data Arg = Arg Int | Result deriving (Eq, Ord)

instance Show Arg where
    show (Arg i) = show i
    show Result  = "*"

type Node = (Name, Arg)
type Deps = Map Cond DepSet
type Reason = (Name, Int)  -- function name, argument index

-- | Nodes along with sets of reasons for every one.
type DepSet = Map Node (Set Reason)

-- | "Condition" is the conjunction of elementary assumptions along
-- the path from the root.  Elementary assumption (f, i) means that
-- "function f uses the argument i".
type Cond = Set Node

-- | Variables carry certain information with them.
data VarInfo = VI
    { viDeps   :: DepSet      -- ^ dependencies drawn in by the variable
    , viFunArg :: Maybe Int   -- ^ which function argument this variable came from (defined only for patvars)
    , viMethod :: Maybe Name  -- ^ name of the metamethod represented by the var, if any
    }
    deriving Show

type Vars = Map Name VarInfo

-- | Perform usage analysis, write the relevant information in the
-- internal structures, returning the list of reachable names.
performUsageAnalysis :: [Name] -> Idris [Name]
performUsageAnalysis startNames = do
    ctx <- tt_ctxt <$> getIState
    case startNames of
      [] -> return []  -- no main -> not compiling -> reachability irrelevant
      main  -> do
        ci  <- idris_interfaces <$> getIState
        cg  <- idris_callgraph <$> getIState
        opt <- idris_optimisation <$> getIState
        used <- idris_erasureUsed <$> getIState
        externs <- idris_externs <$> getIState

        -- Build the dependency graph.
        let depMap = buildDepMap ci used (S.toList externs) ctx main

        -- Search for reachable nodes in the graph.
        let (residDeps, (reachableNames, minUse)) = minimalUsage depMap
            usage = M.toList minUse

        -- Print some debug info.
        logErasure 5 $ "Original deps:\n" ++ unlines (map fmtItem . M.toList $ depMap)
        logErasure 3 $ "Reachable names:\n" ++ unlines (map (indent . show) . S.toList $ reachableNames)
        logErasure 4 $ "Minimal usage:\n" ++ fmtUseMap usage
        logErasure 5 $ "Residual deps:\n" ++ unlines (map fmtItem . M.toList $ residDeps)

        -- Check that everything reachable is accessible.
        checkEnabled <- (WarnReach `elem`) . opt_cmdline . idris_options <$> getIState
        when checkEnabled $
            mapM_ (checkAccessibility opt) usage

        -- Check that no postulates are reachable.
        reachablePostulates <- S.intersection reachableNames . idris_postulates <$> getIState
        when (not . S.null $ reachablePostulates)
            $ ifail ("reachable postulates:\n" ++ intercalate "\n" ["  " ++ show n | n <- S.toList reachablePostulates])

        -- Store the usage info in the internal state.
        mapM_ storeUsage usage

        return $ S.toList reachableNames
  where
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

    storeUsage :: (Name, IntMap (Set Reason)) -> Idris ()
    storeUsage (n, args) = fputState (cg_usedpos . ist_callgraph n) flat
      where
        flat = [(i, S.toList rs) | (i,rs) <- IM.toList args]

    checkAccessibility :: Ctxt OptInfo -> (Name, IntMap (Set Reason)) -> Idris ()
    checkAccessibility opt (n, reachable)
        | Just (Optimise inaccessible dt force) <- lookupCtxtExact n opt
        , eargs@(_:_) <- [fmt n (S.toList rs) | (i,n) <- inaccessible, rs <- maybeToList $ IM.lookup i reachable]
        = warn $ show n ++ ": inaccessible arguments reachable:\n  " ++ intercalate "\n  " eargs

        | otherwise = return ()
      where
        fmt n [] = show n ++ " (no more information available)"
        fmt n rs = show n ++ " from " ++ intercalate ", " [show rn ++ " arg# " ++ show ri | (rn,ri) <- rs]
        warn = logErasure 0

-- | Find the minimal consistent usage by forward chaining.
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

-- | Build the dependency graph, starting the depth-first search from
-- a list of Names.
buildDepMap :: Ctxt InterfaceInfo -> [(Name, Int)] -> [(Name, Int)] ->
               Context -> [Name] -> Deps
buildDepMap ci used externs ctx startNames
    = addPostulates used $ dfs S.empty M.empty startNames
  where
    -- mark the result of Main.main as used with the empty assumption
    addPostulates :: [(Name, Int)] -> Deps -> Deps
    addPostulates used deps = foldr (\(ds, rs) -> M.insertWith (M.unionWith S.union) ds rs) deps (postulates used)
      where
        -- mini-DSL for postulates
        (==>) ds rs = (S.fromList ds, M.fromList [(r, S.empty) | r <- rs])
        it n is = [(sUN n, Arg i) | i <- is]
        mn n is = [(MN 0 $ pack n, Arg i) | i <- is]

        -- believe_me is special because it does not use all its arguments
        specialPrims = S.fromList [sUN "prim__believe_me"]
        usedNames = allNames deps S.\\ specialPrims
        usedPrims = [(p_name p, p_arity p) | p <- primitives, p_name p `S.member` usedNames]

        postulates used =
            [ [] ==> concat
                -- Main.main ( + export lists) and run__IO, are always evaluated
                -- but they elude analysis since they come from the seed term.
                [(map (\n -> (n, Result)) startNames)
                ,[(sUN "run__IO", Result), (sUN "run__IO", Arg 1)]
                ,[(sUN "call__IO", Result), (sUN "call__IO", Arg 2)]

                -- Explicit usage declarations from a %used pragma
                , map (\(n, i) -> (n, Arg i)) used

                -- MkIO is read by run__IO,
                -- but this cannot be observed in the source code of programs.
                , it "MkIO"         [2]
                , it "prim__IO"     [1]

                -- Foreign calls are built with pairs, but mkForeign doesn't
                -- have an implementation so analysis won't see them
                , [(pairCon, Arg 2),
                   (pairCon, Arg 3)] -- Used in foreign calls

                -- these have been discovered as builtins but are not listed
                -- among Idris.Primitives.primitives
                --, mn "__MkPair"     [2,3]
                , it "prim_fork"    [0]
                , it "unsafePerformPrimIO"  [1]

                -- believe_me is a primitive but it only uses its third argument
                -- it is special-cased in usedNames above
                , it "prim__believe_me" [2]

                -- in general, all other primitives use all their arguments
                , [(n, Arg i) | (n,arity) <- usedPrims, i <- [0..arity-1]]

                -- %externs are assumed to use all their arguments
                , [(n, Arg i) | (n,arity) <- externs, i <- [0..arity-1]]

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
    getDeps (SN (WhereN i (SN (ImplementationCtorN interfaceN)) (MN i' field)))
        = M.empty  -- these deps are created when applying implementation ctors
    getDeps n = case lookupDefExact n ctx of
        Just def -> getDepsDef n def
        Nothing  -> error $ "erasure checker: unknown reference: " ++ show n

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
    etaExpand (n : ns) t = etaExpand ns (App Complete t (P Ref n Erased))

    getDepsSC :: Name -> [Name] -> Vars -> SC -> Deps
    getDepsSC fn es vs  ImpossibleCase     = M.empty
    getDepsSC fn es vs (UnmatchedCase msg) = M.empty

    -- for the purposes of erasure, we can disregard the projection
    getDepsSC fn es vs (ProjCase (Proj t i) alts) = getDepsSC fn es vs (ProjCase t alts)  -- step
    getDepsSC fn es vs (ProjCase (P  _ n _) alts) = getDepsSC fn es vs (Case Shared n alts)  -- base

    -- other ProjCase's are not supported
    getDepsSC fn es vs (ProjCase t alts)   = error $ "ProjCase not supported:\n" ++ show (ProjCase t alts)

    getDepsSC fn es vs (STerm    t)        = getDepsTerm vs [] (S.singleton (fn, Result)) (etaExpand es t)
    getDepsSC fn es vs (Case sh n alts)
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
    getDepsAlt fn es vs var (FnCase n ns sc) = M.empty -- can't use FnCase at runtime
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
            , viMethod = meth j
            })
          | (v, j) <- zip ns [0..]]

        -- this is safe because it's certainly a patvar
        varIdx = fromJust (viFunArg var)

        -- generate metamethod names, "n" is the implementation ctor
        meth :: Int -> Maybe Name
        meth | SN (ImplementationCtorN interfaceName) <- n = \j -> Just (mkFieldName n j)
             | otherwise = \j -> Nothing

    -- Named variables -> DeBruijn variables -> Conds/guards -> Term -> Deps
    getDepsTerm :: Vars -> [(Name, Cond -> Deps)] -> Cond -> Term -> Deps

    -- named variables introduce dependencies as described in `vs'
    getDepsTerm vs bs cd (P _ n _)
        -- de bruijns (lambda-bound, let-bound vars)
        | Just deps <- lookup n bs
        = deps cd

        -- ctor-bound/arg-bound variables
        | Just var <- M.lookup n vs
        = M.singleton cd (viDeps var)

        -- sanity check: machine-generated names shouldn't occur at top-level
        | MN _ _ <- n
        = error $ "erasure analysis: variable " ++ show n ++ " unbound in " ++ show (S.toList cd)

        -- assumed to be a global reference
        | otherwise = M.singleton cd (M.singleton (n, Result) S.empty)

    -- dependencies of de bruijn variables are described in `bs'
    getDepsTerm vs bs cd (V i) = snd (bs !! i) cd

    getDepsTerm vs bs cd (Bind n bdr body)
        -- here we just push IM.empty on the de bruijn stack
        -- the args will be marked as used at the usage site
        | Lam _ ty <- bdr = getDepsTerm vs ((n, const M.empty) : bs) cd body
        | Pi _ _ ty _ <- bdr = getDepsTerm vs ((n, const M.empty) : bs) cd body

        -- let-bound variables can get partially evaluated
        -- it is sufficient just to plug the Cond in when the bound names are used
        |  Let ty t <- bdr = var t cd `union` getDepsTerm vs ((n, const M.empty) : bs) cd body
        | NLet ty t <- bdr = var t cd `union` getDepsTerm vs ((n, const M.empty) : bs) cd body
      where
        var t cd = getDepsTerm vs bs cd t

    -- applications may add items to Cond
    getDepsTerm vs bs cd app@(App _ _ _)
        | (fun, args) <- unApply app = case fun of
            -- implementation constructors -> create metamethod deps
            P (DCon _ _ _) ctorName@(SN (ImplementationCtorN interfaceName)) _
                -> conditionalDeps ctorName args  -- regular data ctor stuff
                    `union` unionMap (methodDeps ctorName) (zip [0..] args)  -- method-specific stuff

            -- ordinary constructors
            P (TCon _ _) n _ -> unconditionalDeps args  -- does not depend on anything
            P (DCon _ _ _) n _ -> conditionalDeps n args  -- depends on whether (n,#) is used

            -- mkForeign* calls must be special-cased because they are variadic
            -- All arguments must be marked as used, except for the first four,
            -- which define the call type and are not needed at runtime.
            P _ (UN n) _
                | n == T.pack "mkForeignPrim"
                -> unconditionalDeps $ drop 4 args

            -- a bound variable might draw in additional dependencies,
            -- think: f x = x 0  <-- here, `x' _is_ used
            P _ n _
                -- debruijn-bound name
                | Just deps <- lookup n bs
                    -> deps cd `union` unconditionalDeps args

                -- local name that refers to a method
                | Just var  <- M.lookup n vs
                , Just meth <- viMethod var
                    -> viDeps var `ins` conditionalDeps meth args  -- use the method instead

                -- local name
                | Just var <- M.lookup n vs
                    -- unconditional use
                    -> viDeps var `ins` unconditionalDeps args

                -- global name
                | otherwise
                    -- depends on whether the referred thing uses its argument
                    -> conditionalDeps n args

            -- TODO: could we somehow infer how bound variables use their arguments?
            V i -> snd (bs !! i) cd `union` unconditionalDeps args

            -- we interpret applied lambdas as lets in order to reuse code here
            Bind n (Lam _ ty) t -> getDepsTerm vs bs cd (lamToLet app)

            -- and we interpret applied lets as lambdas
            Bind n ( Let ty t') t -> getDepsTerm vs bs cd (App Complete (Bind n (Lam RigW ty) t) t')
            Bind n (NLet ty t') t -> getDepsTerm vs bs cd (App Complete (Bind n (Lam RigW ty) t) t')

            Proj t i
                -> error $ "cannot[0] analyse projection !" ++ show i ++ " of " ++ show t

            Erased -> M.empty

            _ -> error $ "cannot analyse application of " ++ show fun ++ " to " ++ show args
      where
        union = M.unionWith $ M.unionWith S.union
        ins = M.insertWith (M.unionWith S.union) cd

        unconditionalDeps :: [Term] -> Deps
        unconditionalDeps = unionMap (getDepsTerm vs bs cd)

        conditionalDeps :: Name -> [Term] -> Deps
        conditionalDeps n
            = ins (M.singleton (n, Result) S.empty) . unionMap (getDepsArgs n) . zip indices
          where
            indices = map Just [0 .. getArity n - 1] ++ repeat Nothing
            getDepsArgs n (Just i,  t) = getDepsTerm vs bs (S.insert (n, Arg i) cd) t  -- conditional
            getDepsArgs n (Nothing, t) = getDepsTerm vs bs cd t                        -- unconditional

        methodDeps :: Name -> (Int, Term) -> Deps
        methodDeps ctorName (methNo, t)
            = getDepsTerm (vars `M.union` vs) (bruijns ++ bs) cond body
          where
            vars = M.fromList [(v, VI
                { viDeps   = deps i
                , viFunArg = Just i
                , viMethod = Nothing
                }) | (v, i) <- zip args [0..]]
            deps i   = M.singleton (metameth, Arg i) S.empty
            bruijns  = reverse [(n, \cd -> M.singleton cd (deps i)) | (i, n) <- zip [0..] args]
            cond     = S.singleton (metameth, Result)
            metameth = mkFieldName ctorName methNo
            (args, body) = unfoldLams t

    -- projections
    getDepsTerm vs bs cd (Proj t (-1)) = getDepsTerm vs bs cd t  -- naturals, (S n) -> n
    getDepsTerm vs bs cd (Proj t i) = error $ "cannot[1] analyse projection !" ++ show i ++ " of " ++ show t

    -- the easy cases
    getDepsTerm vs bs cd (Constant _) = M.empty
    getDepsTerm vs bs cd (TType    _) = M.empty
    getDepsTerm vs bs cd (UType    _) = M.empty
    getDepsTerm vs bs cd  Erased      = M.empty
    getDepsTerm vs bs cd  Impossible  = M.empty

    getDepsTerm vs bs cd t = error $ "cannot get deps of: " ++ show t

    -- Get the number of arguments that might be considered for erasure.
    getArity :: Name -> Int
    getArity (SN (WhereN i' ctorName (MN i field)))
        | Just (TyDecl (DCon _ _ _) ty) <- lookupDefExact ctorName ctx
        = let argTys = map snd $ getArgTys ty
            in if i <= length argTys
                then length $ getArgTys (argTys !! i)
                else error $ "invalid field number " ++ show i ++ " for " ++ show ctorName

        | otherwise = error $ "unknown implementation constructor: " ++ show ctorName

    getArity n = case lookupDefExact n ctx of
        Just (CaseOp ci ty tys def tot cdefs) -> length tys
        Just (TyDecl (DCon tag arity _) _)    -> arity
        Just (TyDecl (Ref) ty)                -> length $ getArgTys ty
        Just (Operator ty arity op)           -> arity
        Just df -> error $ "Erasure/getArity: unrecognised entity '"
                             ++ show n ++ "' with definition: "  ++ show df
        Nothing -> error $ "Erasure/getArity: definition not found for " ++ show n

    -- convert applications of lambdas to lets
    -- note that this transformation preserves de bruijn numbering
    lamToLet :: Term -> Term
    lamToLet tm = lamToLet' args f
      where
        (f, args) = unApply tm

    lamToLet' :: [Term] -> Term -> Term
    lamToLet' (v:vs) (Bind n (Lam _ ty) tm) = Bind n (Let ty v) $ lamToLet' vs tm
    lamToLet'    []  tm = tm
    lamToLet'    vs  tm = error $
        "Erasure.hs:lamToLet': unexpected input: "
            ++ "vs = " ++ show vs ++ ", tm = " ++ show tm

    -- split "\x_i -> T(x_i)" into [x_i] and T
    unfoldLams :: Term -> ([Name], Term)
    unfoldLams (Bind n (Lam _ ty) t) = let (ns,t') = unfoldLams t in (n:ns, t')
    unfoldLams t = ([], t)

    union :: Deps -> Deps -> Deps
    union = M.unionWith (M.unionWith S.union)

    unions :: [Deps] -> Deps
    unions = M.unionsWith (M.unionWith S.union)

    unionMap :: (a -> Deps) -> [a] -> Deps
    unionMap f = M.unionsWith (M.unionWith S.union) . map f

-- | Make a field name out of a data constructor name and field number.
mkFieldName :: Name -> Int -> Name
mkFieldName ctorName fieldNo = SN (WhereN fieldNo ctorName $ sMN fieldNo "field")

{-|
Module      : Idris.TypeSearch
Description : A Hoogle for Idris.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ScopedTypeVariables #-}

module Idris.TypeSearch (
    searchByType
  , searchPred
  , defaultScoreFunction
  ) where

import Idris.AbsSyntax (addImpl, addUsingConstraints, getIState, implicit,
                        logLvl, putIState)
import Idris.AbsSyntaxTree (IState(idris_docstrings, idris_interfaces, idris_outputmode, tt_ctxt),
                            Idris, InterfaceInfo, OutputMode(..), PTerm,
                            defaultSyntax, eqTy, implicitAllowed,
                            interface_implementations, toplevel)
import Idris.Core.Evaluate (Context(definitions), Def(CaseOp, Function, TyDecl),
                            normaliseC)
import Idris.Core.TT hiding (score)
import Idris.Core.Unify (match_unify)
import Idris.Delaborate (delabTy)
import Idris.Docstrings (noDocs, overview)
import Idris.Elab.Type (elabType)
import Idris.IBC
import Idris.Output (iPrintResult, iRenderError, iRenderOutput, iRenderResult,
                     iputStrLn, prettyDocumentedIst)

import Util.Pretty (Doc, annotate, char, text, vsep, (<>))

import Prelude hiding (pred)

import Control.Applicative (Applicative(..), (<$>), (<*>), (<|>))
import Control.Arrow (first, second, (&&&), (***))
import Control.Monad (guard, when)
import Data.List (find, partition, (\\))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe, maybeToList)
import Data.Monoid (Monoid(mappend, mempty))
import Data.Ord (comparing)
import qualified Data.PriorityQueue.FingerTree as Q
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Text as T (isPrefixOf, pack)
import Data.Traversable (traverse)

searchByType :: [String] -> PTerm -> Idris ()
searchByType pkgs pterm = do
  i <- getIState -- save original
  when (not (null pkgs)) $
     iputStrLn $ "Searching packages: " ++ showSep ", " pkgs

  mapM_ loadPkgIndex pkgs
  pterm' <- addUsingConstraints syn emptyFC pterm
  pterm'' <- implicit toplevel syn name pterm'
  let pterm'''  = addImpl [] i pterm''
  ty <- elabType toplevel syn (fst noDocs) (snd noDocs) emptyFC [] name NoFC pterm'
  let names = searchUsing searchPred i ty
  let names' = take numLimit names
  let docs =
       [ let docInfo = (n, delabTy i n, fmap (overview . fst) (lookupCtxtExact n (idris_docstrings i))) in
         displayScore theScore <> char ' ' <> prettyDocumentedIst i docInfo
                | (n, theScore) <- names']
  if (not (null docs))
     then case idris_outputmode i of
               RawOutput _  -> do mapM_ iRenderOutput docs
                                  iPrintResult ""
               IdeMode _ _ -> iRenderResult (vsep docs)
     else iRenderError $ text "No results found"
  putIState i -- don't actually make any changes
  where
    numLimit = 50
    syn = defaultSyntax { implicitAllowed = True } -- syntax
    name = sMN 0 "searchType" -- name

-- | Conduct a type-directed search using a given match predicate
searchUsing :: (IState -> Type -> [(Name, Type)] -> [(Name, a)])
  -> IState -> Type -> [(Name, a)]
searchUsing pred istate ty = pred istate nty . concat . M.elems $
  M.mapWithKey (\key -> M.toAscList . M.mapMaybe (f key)) (definitions ctxt)
  where
  nty = normaliseC ctxt [] ty
  ctxt = tt_ctxt istate
  f k x = do
    guard $ not (special k)
    type2 <- typeFromDef x
    return $ normaliseC ctxt [] type2
  special :: Name -> Bool
  special (NS n _) = special n
  special (SN _) = True
  special (UN n) =    T.pack "default#" `T.isPrefixOf` n
                   || n `elem` map T.pack ["believe_me", "really_believe_me"]
  special _ = False

-- | Our default search predicate.
searchPred :: IState -> Type -> [(Name, Type)] -> [(Name, Score)]
searchPred istate ty1 = matcher where
  maxScore = 100
  matcher = matchTypesBulk istate maxScore ty1


typeFromDef :: (Def, r, i, b, c, d) -> Maybe Type
typeFromDef (def, _, _, _, _, _) = get def where
  get :: Def -> Maybe Type
  get (Function ty _) = Just ty
  get (TyDecl _ ty) = Just ty
 -- get (Operator ty _ _) = Just ty
  get (CaseOp _ ty _ _ _ _)  = Just ty
  get _ = Nothing

-- Replace all occurences of `Delayed s t` with `t` in a type
unLazy :: Type -> Type
unLazy typ = case typ of
  App _ (App _ (P _ lazy _) _) ty | lazy == sUN "Delayed" -> unLazy ty
  Bind name binder ty -> Bind name (fmap unLazy binder) (unLazy ty)
  App s t1 t2 -> App s (unLazy t1) (unLazy t2)
  Proj ty i -> Proj (unLazy ty) i
  _ -> typ

-- | reverse the edges for a directed acyclic graph
reverseDag :: Ord k => [((k, a), Set k)] -> [((k, a), Set k)]
reverseDag xs = map f xs where
  f ((k, v), _) = ((k, v), S.fromList . map (fst . fst) $ filter (S.member k . snd) xs)

-- run vToP first!
-- | Compute a directed acyclic graph corresponding to the
-- arguments of a function.
-- returns [(the name and type of the bound variable
--          the names in the type of the bound variable)]
computeDagP :: Ord n
  => (TT n -> Bool) -- ^ filter to remove some arguments
  -> TT n
  -> ([((n, TT n), Set n)], [(n, TT n)], TT n)
computeDagP removePred t = (reverse (map f arguments), reverse theRemovedArgs , retTy) where
  f (n, ty) = ((n, ty), M.keysSet (usedVars ty))

  (arguments, theRemovedArgs, retTy) = go [] [] t

  -- NOTE : args are in reverse order
  go args removedArgs (Bind n (Pi _ _ ty _) sc) = let arg = (n, ty) in
    if removePred ty
      then go args (arg : removedArgs) sc
      else go (arg : args) removedArgs sc
  go args removedArgs sc = (args, removedArgs, sc)

-- | Collect the names and types of all the free variables
-- The Boolean indicates those variables which are determined due to injectivity
-- I have not given nearly enough thought to know whether this is correct
usedVars :: Ord n => TT n -> Map n (TT n, Bool)
usedVars = f True where
  f b (P Bound n t) = M.singleton n (t, b) `M.union` f b t
  f b (Bind n binder t2) = (M.delete n (f b t2) `M.union`) $ case binder of
    Let t v ->   f b t `M.union` f b v
    Guess t v -> f b t `M.union` f b v
    bind -> f b (binderTy bind)
  f b (App _ t1 t2) = f b t1 `M.union` f (b && isInjective t1) t2
  f b (Proj t _) = f b t
  f _ (V _) = error "unexpected! run vToP first"
  f _ _ = M.empty

-- | Remove a node from a directed acyclic graph
deleteFromDag :: Ord n => n -> [((n, TT n), (a, Set n))] -> [((n, TT n), (a, Set n))]
deleteFromDag name [] = []
deleteFromDag name (((name2, ty), (ix, set)) : xs) = (if name == name2
  then id
  else (((name2, ty) , (ix, S.delete name set)) :) ) (deleteFromDag name xs)

deleteFromArgList :: Ord n => n -> [(n, TT n)] -> [(n, TT n)]
deleteFromArgList n = filter ((/= n) . fst)

-- | Asymmetric modifications to keep track of
data AsymMods = Mods
  { argApp         :: !Int
  , interfaceApp   :: !Int
  , interfaceIntro :: !Int
  } deriving (Eq, Show)


-- | Homogenous tuples
data Sided a = Sided
  { left  :: !a
  , right :: !a
  } deriving (Eq, Show)

sided :: (a -> a -> b) -> Sided a -> b
sided f (Sided l r) = f l r

-- | Could be a functor instance, but let's avoid name overloading
both :: (a -> b) -> Sided a -> Sided b
both f (Sided l r) = Sided (f l) (f r)

-- | Keeps a record of the modifications made to match one type
-- signature with another
data Score = Score
  { transposition :: !Int -- ^ transposition of arguments
  , equalityFlips :: !Int -- ^ application of symmetry of equality
  , asymMods      :: !(Sided AsymMods) -- ^ "directional" modifications
  } deriving (Eq, Show)

displayScore :: Score -> Doc OutputAnnotation
displayScore score = case both noMods (asymMods score) of
  Sided True  True  -> annotated EQ "=" -- types are isomorphic
  Sided True  False -> annotated LT "<" -- found type is more general than searched type
  Sided False True  -> annotated GT ">" -- searched type is more general than found type
  Sided False False -> text "_"
  where
  annotated ordr = annotate (AnnSearchResult ordr) . text
  noMods (Mods app tcApp tcIntro) = app + tcApp + tcIntro == 0

-- | This allows the search to stop expanding on a certain state if its
-- score is already too high. Returns 'True' if the algorithm should keep
-- exploring from this state, and 'False' otherwise.
scoreCriterion :: Score -> Bool
scoreCriterion (Score _ _ amods) = not
  (  sided (&&) (both ((> 0) . argApp) amods)
  || sided (+) (both argApp amods) > 4
  || sided (||) (both (\(Mods _ tcApp tcIntro) -> tcApp > 3 || tcIntro > 3) amods)
  )

-- | Convert a 'Score' to an 'Int' to provide an order for search results.
-- Lower scores are better.
defaultScoreFunction :: Score -> Int
defaultScoreFunction (Score trans eqFlip amods) =
  trans + eqFlip + linearPenalty + upAndDowncastPenalty
  where
  -- prefer finding a more general type to a less general type
  linearPenalty = (\(Sided l r) -> 3 * l + r)
    (both (\(Mods app tcApp tcIntro) -> 3 * app + 4 * tcApp + 2 * tcIntro) amods)
  -- it's very bad to have *both* upcasting and downcasting
  upAndDowncastPenalty = 100 *
    sided (*) (both (\(Mods app tcApp tcIntro) -> 2 * app + tcApp + tcIntro) amods)

instance Ord Score where
  compare = comparing defaultScoreFunction


instance Monoid a => Monoid (Sided a) where
  mempty = Sided mempty mempty
  (Sided l1 r1) `mappend` (Sided l2 r2) = Sided (l1 `mappend` l2) (r1 `mappend` r2)

instance Monoid AsymMods where
  mempty = Mods 0 0 0
  (Mods a b c) `mappend` (Mods a' b' c') = Mods (a + a') (b + b') (c + c')

instance Monoid Score where
  mempty = Score 0 0 mempty
  (Score t e mods) `mappend` (Score t' e' mods') = Score (t + t') (e + e') (mods `mappend` mods')

-- | A directed acyclic graph representing the arguments to a function
-- The 'Int' represents the position of the argument (1st argument, 2nd, etc.)
type ArgsDAG = [((Name, Type), (Int, Set Name))]

-- | A list of interface constraints
type Interfaces = [(Name, Type)]

-- | The state corresponding to an attempted match of two types.
data State = State
  { holes             :: ![(Name, Type)] -- ^ names which have yet to be resolved
  , argsAndInterfaces :: !(Sided (ArgsDAG, Interfaces))
     -- ^ arguments and interface constraints for each type which have yet to be resolved
  , score             :: !Score -- ^ the score so far
  , usedNames         :: ![Name] -- ^ all names that have been used
  } deriving Show

modifyTypes :: (Type -> Type) -> (ArgsDAG, Interfaces) -> (ArgsDAG, Interfaces)
modifyTypes f = modifyDag *** modifyList
  where
  modifyDag = map (first (second f))
  modifyList = map (second f)

findNameInArgsDAG :: Name -> ArgsDAG -> Maybe (Type, Maybe Int)
findNameInArgsDAG name = fmap ((snd . fst) &&& (Just . fst . snd)) . find ((name ==) . fst . fst)

findName :: Name -> (ArgsDAG, Interfaces) -> Maybe (Type, Maybe Int)
findName n (args, interfaces) = findNameInArgsDAG n args <|> ((,) <$> lookup n interfaces <*> Nothing)

deleteName :: Name -> (ArgsDAG, Interfaces) -> (ArgsDAG, Interfaces)
deleteName n (args, interfaces) = (deleteFromDag n args, filter ((/= n) . fst) interfaces)

tcToMaybe :: TC a -> Maybe a
tcToMaybe (OK x) = Just x
tcToMaybe (Error _) = Nothing

inArgTys :: (Type -> Type) -> ArgsDAG -> ArgsDAG
inArgTys = map . first . second


interfaceUnify :: Ctxt InterfaceInfo -> Context -> Type -> Type -> Maybe [(Name, Type)]
interfaceUnify interfaceInfo ctxt ty tyTry = do
  res <- tcToMaybe $ match_unify ctxt [] (ty, Nothing) (retTy, Nothing) [] theHoles []
  guard $ null (theHoles \\ map fst res)
  let argTys' = map (second $ foldr (.) id [ subst n t | (n, t) <- res ]) tcArgs
  return argTys'
  where
  tyTry' = vToP tyTry
  theHoles = map fst nonTcArgs
  retTy = getRetTy tyTry'
  (tcArgs, nonTcArgs) = partition (isInterfaceArg interfaceInfo . snd) $ getArgTys tyTry'

isInterfaceArg :: Ctxt InterfaceInfo -> Type -> Bool
isInterfaceArg interfaceInfo ty = not (null (getInterfaceName clss >>= flip lookupCtxt interfaceInfo)) where
  (clss, args) = unApply ty
  getInterfaceName (P (TCon _ _) interfaceName _) = [interfaceName]
  getInterfaceName _ = []


-- | Compute the power set
subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (x : xs) = let ss = subsets xs in map (x :) ss ++ ss


-- not recursive (i.e., doesn't flip iterated identities) at the moment
-- recalls the number of flips that have been made
flipEqualities :: Type -> [(Int, Type)]
flipEqualities t = case t of
  eq1@(App _ (App _ (App _ (App _ eq@(P _ eqty _) tyL) tyR) valL) valR) | eqty == eqTy ->
    [(0, eq1), (1, app (app (app (app eq tyR) tyL) valR) valL)]
  Bind n binder sc -> (\bind' (j, sc') -> (fst (binderTy bind') + j, Bind n (fmap snd bind') sc'))
    <$> traverse flipEqualities binder <*> flipEqualities sc
  App _ f x -> (\(i, f') (j, x') -> (i + j, app f' x'))
    <$> flipEqualities f <*> flipEqualities x
  t' -> [(0, t')]
 where app = App Complete

--DONT run vToP first!
-- | Try to match two types together in a unification-like procedure.
-- Returns a list of types and their minimum scores, sorted in order
-- of increasing score.
matchTypesBulk :: forall info. IState -> Int -> Type -> [(info, Type)] -> [(info, Score)]
matchTypesBulk istate maxScore type1 types = getAllResults startQueueOfQueues where
  getStartQueues :: (info, Type) -> Maybe (Score, (info, Q.PQueue Score State))
  getStartQueues nty@(info, type2) = case mapMaybe startStates ty2s of
    [] -> Nothing
    xs -> Just (minimum (map fst xs), (info, Q.fromList xs))
    where
    ty2s = (\(i, dag) (j, retTy) -> (i + j, dag, retTy))
      <$> flipEqualitiesDag dag2 <*> flipEqualities retTy2
    flipEqualitiesDag dag = case dag of
      [] -> [(0, [])]
      ((n, ty), (pos, deps)) : xs ->
         (\(i, ty') (j, xs') -> (i + j , ((n, ty'), (pos, deps)) : xs'))
           <$> flipEqualities ty <*> flipEqualitiesDag xs
    startStates (numEqFlips, sndDag, sndRetTy) = do
      state <- unifyQueue (State startingHoles
                (Sided (dag1, interfaceArgs1) (sndDag, interfaceArgs2))
                (mempty { equalityFlips = numEqFlips }) usedns) [(retTy1, sndRetTy)]
      return (score state, state)


    (dag2, interfaceArgs2, retTy2) = makeDag (uniqueBinders (map fst argNames1) type2)
    argNames2 = map fst dag2
    usedns = map fst startingHoles
    startingHoles = argNames1 ++ argNames2

    startingTypes = [(retTy1, retTy2)]


  startQueueOfQueues :: Q.PQueue Score (info, Q.PQueue Score State)
  startQueueOfQueues = Q.fromList $ mapMaybe getStartQueues types

  getAllResults :: Q.PQueue Score (info, Q.PQueue Score State) -> [(info, Score)]
  getAllResults q = case Q.minViewWithKey q of
    Nothing -> []
    Just ((nextScore, (info, stateQ)), q') ->
      if defaultScoreFunction nextScore <= maxScore
        then case nextStepsQueue stateQ of
          Nothing -> getAllResults q'
          Just (Left stateQ') -> case Q.minViewWithKey stateQ' of
             Nothing -> getAllResults q'
             Just ((newQscore,_), _) -> getAllResults (Q.add newQscore (info, stateQ') q')
          Just (Right theScore) -> (info, theScore) : getAllResults q'
        else []


  ctxt = tt_ctxt istate
  interfaceInfo = idris_interfaces istate

  (dag1, interfaceArgs1, retTy1) = makeDag type1
  argNames1 = map fst dag1
  makeDag :: Type -> (ArgsDAG, Interfaces, Type)
  makeDag = first3 (zipWith (\i (ty, deps) -> (ty, (i, deps))) [0..] . reverseDag) .
    computeDagP (isInterfaceArg interfaceInfo) . vToP . unLazy
  first3 f (a,b,c) = (f a, b, c)

  -- update our state with the unification resolutions
  resolveUnis :: [(Name, Type)] -> State -> Maybe (State, [(Type, Type)])
  resolveUnis [] state = Just (state, [])
  resolveUnis ((name, term@(P Bound name2 _)) : xs)
    state | isJust findArgs = do
    ((ty1, ix1), (ty2, ix2)) <- findArgs

    (state'', queue) <- resolveUnis xs state'
    let transScore = fromMaybe 0 (abs <$> ((-) <$> ix1 <*> ix2))
    return (inScore (\s -> s { transposition = transposition s + transScore }) state'', (ty1, ty2) : queue)
    where
    unresolved = argsAndInterfaces state
    inScore f stat = stat { score = f (score stat) }
    findArgs = ((,) <$> findName name  (left unresolved) <*> findName name2 (right unresolved)) <|>
               ((,) <$> findName name2 (left unresolved) <*> findName name  (right unresolved))
    matchnames = [name, name2]
    deleteArgs = deleteName name . deleteName name2
    state' = state { holes = filter (not . (`elem` matchnames) . fst) (holes state)
                   , argsAndInterfaces = both (modifyTypes (subst name term) . deleteArgs) unresolved}

  resolveUnis ((name, term) : xs)
    state@(State hs unresolved _ _) = case both (findName name) unresolved of
      Sided Nothing  Nothing  -> Nothing
      Sided (Just _) (Just _) -> error "Idris internal error: TypeSearch.resolveUnis"
      oneOfEach -> first (addScore (both scoreFor oneOfEach)) <$> nextStep
    where
    scoreFor (Just _) = mempty { argApp = 1 }
    scoreFor Nothing  = mempty { argApp = otherApplied }
    -- find variables which are determined uniquely by the type
    -- due to injectivity
    matchedVarMap = usedVars term
    bothT f (x, y) = (f x, f y)
    (injUsedVars, notInjUsedVars) = bothT M.keys . M.partition id . M.filterWithKey (\k _-> k `elem` map fst hs) $ M.map snd matchedVarMap
    varsInTy = injUsedVars ++ notInjUsedVars
    toDelete = name : varsInTy
    deleteMany = foldr (.) id (map deleteName toDelete)

    otherApplied = length notInjUsedVars

    addScore additions theState = theState { score = let s = score theState in
      s { asymMods = asymMods s `mappend` additions } }
    state' = state { holes = filter (not . (`elem` toDelete) . fst) hs
                   , argsAndInterfaces = both (modifyTypes (subst name term) . deleteMany) (argsAndInterfaces state) }
    nextStep = resolveUnis xs state'


  -- | resolve a queue of unification constraints
  unifyQueue :: State -> [(Type, Type)] -> Maybe State
  unifyQueue state [] = return state
  unifyQueue state ((ty1, ty2) : queue) = do
    --trace ("go: \n" ++ show state) True `seq` return ()
    res <- tcToMaybe $ match_unify ctxt [ (n, RigW, Pi RigW Nothing ty (TType (UVar [] 0))) | (n, ty) <- holes state]
                                   (ty1, Nothing)
                                   (ty2, Nothing) [] (map fst $ holes state) []
    (state', queueAdditions) <- resolveUnis res state
    guard $ scoreCriterion (score state')
    unifyQueue state' (queue ++ queueAdditions)

  possInterfaceImplementations :: [Name] -> Type -> [Type]
  possInterfaceImplementations usedns ty = do
    interfaceName <- getInterfaceName clss
    interfaceDef <- lookupCtxt interfaceName interfaceInfo
    n <- interface_implementations interfaceDef
    def <- lookupCtxt (fst n) (definitions ctxt)
    nty <- normaliseC ctxt [] <$> (case typeFromDef def of Just x -> [x]; Nothing -> [])
    let ty' = vToP (uniqueBinders usedns nty)
    return ty'
    where
    (clss, _) = unApply ty
    getInterfaceName (P (TCon _ _) interfaceName _) = [interfaceName]
    getInterfaceName _ = []

  -- 'Just' if the computation hasn't totally failed yet, 'Nothing' if it has
  -- 'Left' if we haven't found a terminal state, 'Right' if we have
  nextStepsQueue :: Q.PQueue Score State -> Maybe (Either (Q.PQueue Score State) Score)
  nextStepsQueue queue = do
    ((nextScore, next), rest) <- Q.minViewWithKey queue
    Just $ if isFinal next
      then Right nextScore
      else let additions = if scoreCriterion nextScore
                 then Q.fromList [ (score state, state) | state <- nextSteps next ]
                 else Q.empty in
           Left (Q.union rest additions)
    where
    isFinal (State [] (Sided ([], []) ([], [])) _ _) = True
    isFinal _ = False

  -- | Find all possible matches starting from a given state.
  -- We go in stages rather than concatenating all three results in hopes of narrowing
  -- the search tree. Once we advance in a phase, there should be no going back.
  nextSteps :: State -> [State]

  -- Stage 3 - match interfaces
  nextSteps (State [] unresolved@(Sided ([], c1) ([], c2)) scoreAcc usedns) =
    if null results3 then results4 else results3
    where
    -- try to match an interface argument from the left with an interface argument from the right
    results3 =
         catMaybes [ unifyQueue (State []
         (Sided ([], deleteFromArgList n1 c1)
                ([], map (second subst2for1) (deleteFromArgList n2 c2)))
         scoreAcc usedns) [(ty1, ty2)]
     | (n1, ty1) <- c1, (n2, ty2) <- c2, let subst2for1 = psubst n2 (P Bound n1 ty1)]

    -- try to hunt match an interface constraint by replacing it with an implementation
    results4 = [ State [] (both (\(cs, _, _) -> ([], cs)) sds)
               (scoreAcc `mappend` Score 0 0 (both (\(_, amods, _) -> amods) sds))
               (usedns ++ sided (++) (both (\(_, _, hs) -> hs) sds))
               | sds <- allMods ]
      where
      allMods = parallel defMod mods
      mods :: Sided [( Interfaces, AsymMods, [Name] )]
      mods = both (implementationMods . snd) unresolved
      defMod :: Sided (Interfaces, AsymMods, [Name])
      defMod = both (\(_, cs) -> (cs, mempty , [])) unresolved
      parallel :: Sided a -> Sided [a] -> [Sided a]
      parallel (Sided l r) (Sided ls rs) = map (flip Sided r) ls ++ map (Sided l) rs
      implementationMods :: Interfaces -> [( Interfaces , AsymMods, [Name] )]
      implementationMods interfaces = [ ( newInterfaceArgs, mempty { interfaceApp = 1 }, newHoles )
                                      | (_, ty) <- interfaces
                                      , impl <- possInterfaceImplementations usedns ty
                                      , newInterfaceArgs <- maybeToList $ interfaceUnify interfaceInfo ctxt ty impl
                                      , let newHoles = map fst newInterfaceArgs ]


  -- Stage 1 - match arguments
  nextSteps (State hs (Sided (dagL, c1) (dagR, c2)) scoreAcc usedns) = results where

    results = concatMap takeSomeInterfaces results1

    -- we only try to match arguments whose names don't appear in the types
    -- of any other arguments
    canBeFirst :: ArgsDAG -> [(Name, Type)]
    canBeFirst = map fst . filter (S.null . snd . snd)

    -- try to match an argument from the left with an argument from the right
    results1 = catMaybes [ unifyQueue (State (filter (not . (`elem` [n1,n2]) . fst) hs)
         (Sided (deleteFromDag n1 dagL, c1)
                (inArgTys subst2for1 $ deleteFromDag n2 dagR, map (second subst2for1) c2))
          scoreAcc usedns) [(ty1, ty2)]
     | (n1, ty1) <- canBeFirst dagL, (n2, ty2) <- canBeFirst dagR
     , let subst2for1 = psubst n2 (P Bound n1 ty1)]



  -- Stage 2 - simply introduce a subset of the interfaces
  -- we've finished, so take some interfaces
  takeSomeInterfaces (State [] unresolved@(Sided ([], _) ([], _)) scoreAcc usedns) =
    map statesFromMods . prod $ both (interfaceMods . snd) unresolved
    where
    swap (Sided l r) = Sided r l
    statesFromMods :: Sided (Interfaces, AsymMods) -> State
    statesFromMods sides = let interfaces = both (\(c, _) -> ([], c)) sides
                               mods    = swap (both snd sides) in
      State [] interfaces (scoreAcc `mappend` (mempty { asymMods = mods })) usedns
    interfaceMods :: Interfaces -> [(Interfaces, AsymMods)]
    interfaceMods cs = let lcs = length cs in
      [ (cs', mempty { interfaceIntro = lcs - length cs' }) | cs' <- subsets cs ]
    prod :: Sided [a] -> [Sided a]
    prod (Sided ls rs) = [Sided l r | l <- ls, r <- rs]
  -- still have arguments to match, so just be the identity
  takeSomeInterfaces s = [s]

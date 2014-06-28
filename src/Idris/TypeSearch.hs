{-# LANGUAGE ScopedTypeVariables #-}

module Idris.TypeSearch (
  searchByType, searchPred, defaultScoreFunction
) where

import Control.Applicative ((<$>), (<*>), (<|>))
import Control.Arrow (first, second, (&&&))
import Control.Monad (forM_, guard)

import Data.List (find, delete, deleteBy, minimumBy, partition, sortBy, (\\))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromMaybe, isJust, maybeToList, mapMaybe)
import Data.Monoid (Monoid (mempty, mappend))
import Data.Ord (comparing)
import qualified Data.PriorityQueue.FingerTree as Q
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Text as T (pack, isPrefixOf)

import Idris.AbsSyntax (addUsingConstraints, addImpl, getContext, getIState, putIState, implicit)
import Idris.AbsSyntaxTree (class_instances, ClassInfo, defaultSyntax, Idris, 
  IState (idris_classes, idris_docstrings, tt_ctxt),
  implicitAllowed, prettyDocumentedIst, prettyIst, PTerm, toplevel)
import Idris.Core.Evaluate (Context (definitions), Def (Function, TyDecl, CaseOp), normaliseC)
import Idris.Core.TT hiding (score)
import Idris.Core.Unify (match_unify)
import Idris.Delaborate (delabTy)
import Idris.Docstrings (noDocs, overview)
import Idris.ElabDecls (elabType')
import Idris.Output (ihRenderResult)

import System.IO (Handle)

import Util.Pretty (text, char, (<>), Doc)

searchByType :: Handle -> PTerm -> Idris ()
searchByType h pterm = do
  pterm' <- addUsingConstraints syn emptyFC pterm
  pterm'' <- implicit toplevel syn n pterm'
  i <- getIState
  let pterm'''  = addImpl i pterm''
  ty <- elabType' False toplevel syn (fst noDocs) (snd noDocs) emptyFC [] n pterm'
  putIState i -- don't actually make any changes
  let names = searchUsing searchPred i ty
  let names' = take numLimit $ names
  let docs =
       [ let docInfo = (n, delabTy i n, fmap (overview . fst) (lookupCtxtExact n (idris_docstrings i))) in
         displayScore score <> char ' ' <> prettyDocumentedIst i docInfo
                | (n, score) <- names']
  mapM_ (ihRenderResult h) docs
  where 
    numLimit = 50
    syn = defaultSyntax { implicitAllowed = True } -- syntax
    n = sMN 0 "searchType" -- name
  
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
  special (NS n ns) = special n
  special (SN _) = True
  special (UN n) = T.pack "default#" `T.isPrefixOf` n
  special _ = False

-- Our default search predicate.
searchPred :: IState -> Type -> [(Name, Type)] -> [(Name, Score)]
searchPred istate ty1 = matcher where
  maxScore = 100
  matcher = matchTypesBulk istate maxScore ty1


typeFromDef :: (Def, b, c, d) -> Maybe Type
typeFromDef (def, _, _, _) = get def where
  get :: Def -> Maybe Type
  get (Function ty tm) = Just ty
  get (TyDecl _ ty) = Just ty
 -- get (Operator ty _ _) = Just ty
  get (CaseOp _ ty _ _ _ _)  = Just ty
  get _ = Nothing


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
computeDagP removePred t = (reverse (map f args), reverse removedArgs , retTy) where
  f (n, t) = ((n, t), M.keysSet (usedVars False t))

  (numArgs, args, removedArgs, retTy) = go 0 [] [] t

  -- NOTE : args are in reverse order
  go k args removedArgs (Bind n (Pi t) sc) = let arg = (n, t) in
    if removePred t
      then go k        args (arg : removedArgs) sc
      else go (succ k) (arg : args) removedArgs sc
  go k args removedArgs retTy = (k, args, removedArgs, retTy)

-- | Collect the names and types of all the free variables
usedVars :: Ord n 
  => Bool -- ^ only collect variables which must be determined due to injectivity
  -> TT n -> Map n (TT n)
usedVars inj = f where
  f (P Bound n t) = M.singleton n t `M.union` f t
  f (Bind n binder t2) = (M.delete n (f t2) `M.union`) $ case binder of
    Let t v ->   f t `M.union` f v
    Guess t v -> f t `M.union` f v
    b -> f (binderTy b)
  f (App t1 t2) = f t1 `M.union` (if not inj || isInjective t1 then f t2 else M.empty)
  f (Proj t _) = f t
  f (V j) = error "unexpected! run vToP first"
  f _ = M.empty

-- | Remove a node from a directed acyclic graph
deleteFromDag :: Ord n => n -> [((n, TT n), (a, Set n))] -> [((n, TT n), (a, Set n))]
deleteFromDag name [] = []
deleteFromDag name (((name2, ty), (ix, set)) : xs) = (if name == name2
  then id
  else (((name2, ty) , (ix, S.delete name set)) :) ) (deleteFromDag name xs)

deleteFromArgList :: Ord n => n -> [(n, TT n)] -> [(n, TT n)]
deleteFromArgList n = filter ((/= n) . fst)

data Score = Score
  { transposition       :: !Int
  , leftApplied         :: !Int
  , rightApplied        :: !Int
  , leftTypeClassApp    :: !Int
  , rightTypeClassApp   :: !Int
  , leftTypeClassIntro  :: !Int
  , rightTypeClassIntro :: !Int } deriving (Eq, Show)

displayScore :: Score -> Doc a
displayScore (Score trans lapp rapp lclassapp rclassapp lclassintro rclassintro) = text $ case (lt, gt) of
  (True , True ) -> "=" -- types are isomorphic
  (True , False) -> "<" -- found type is more general than searched type
  (False, True ) -> ">" -- searched type is more general than found type
  (False, False) -> "_"
  where lt = lapp + lclassapp + lclassintro == 0
        gt = rapp + rclassapp + rclassintro == 0


scoreCriterion :: Score -> Bool
scoreCriterion (Score a b c d e f g) = not
  ( (b > 0 && c > 0) || (b + c) > 4 || any (> 3) [d,e,f,g])

defaultScoreFunction :: Score -> Int
defaultScoreFunction (Score a b c d e f g) = a + 9*b + 3*c + 12*d + 4*e + 6*f + 2*g + 100*(2*b + d + f)*(2*c + e + g)
  -- it's very bad to have *both* upcasting and downcasting

instance Monoid Score where
  mempty = Score 0 0 0 0 0 0 0
  (Score a b c d e f g) `mappend` (Score a' b' c' d' e' f' g') =
    Score (a + a') (b + b') (c + c') (d + d') (e + e') (f + f') (g + g')

-- | A directed acyclic graph representing the arguments to a function
-- The 'Int' represents the position of the argument (1st argument, 2nd, etc.)
type ArgsDAG = [((Name, Type), (Int, Set Name))]

-- | The state corresponding to an attempted match of two types.
data State = State
  { holes     :: ![(Name, Type)] -- ^ names which have yet to be resolved
  , args1     :: !ArgsDAG -- ^ arguments for the left  type which have yet to be resolved
  , args2     :: !ArgsDAG -- ^ arguments for the right type which have yet to be resolved
  , classes1  :: ![(Name, Type)] -- ^ typeclass arguments for the left  type which haven't been resolved
  , classes2  :: ![(Name, Type)] -- ^ typeclass arguments for the right type which haven't been resolved
  , score     :: !Score -- ^ the score so far
  , usedNames :: ![Name] -- ^ all names that have been used
  } deriving Show

modifyTypes :: (Type -> Type) -> State -> State
modifyTypes f (State h a1 a2 c1 c2 s un) = 
  State h (modifyDag a1) (modifyDag a2) 
          (modifyList c1) (modifyList c2)
          s un
  where
  modifyDag = map (first (second f))
  modifyList = map (second f)

findNameInArgsDAG :: Name -> ArgsDAG -> Maybe (Type, Maybe Int)
findNameInArgsDAG name xs = fmap ((snd . fst) &&& (Just . fst . snd)) . find ((name ==) . fst . fst) $ xs

findLeft, findRight :: Name -> State -> Maybe (Type, Maybe Int)
findLeft  n (State _ a1 a2 c1 c2 _ _) = findNameInArgsDAG n a1 <|> ((,) <$> lookup n c1 <*> Nothing)
findRight n (State _ a1 a2 c1 c2 _ _) = findNameInArgsDAG n a2 <|> ((,) <$> lookup n c2 <*> Nothing)

deleteLeft, deleteRight :: Name -> State -> State
deleteLeft  n state = state { args1 = deleteFromDag n (args1 state) , classes1 = filter ((/= n) . fst) (classes1 state) }
deleteRight n state = state { args2 = deleteFromDag n (args2 state) , classes2 = filter ((/= n) . fst) (classes2 state) }


tcToMaybe :: TC' e a -> Maybe a
tcToMaybe (OK x) = Just x
tcToMaybe (Error _) = Nothing

inArgTys :: (Type -> Type) -> ArgsDAG -> ArgsDAG
inArgTys = map . first . second


typeclassUnify :: Ctxt ClassInfo -> Context -> Type -> Type -> Maybe [(Name, Type)]
typeclassUnify classInfo ctxt ty tyTry = do
  res <- tcToMaybe $ match_unify ctxt [] ty retTy [] holes []
  guard $ null (holes \\ map fst res)
  let argTys' = map (second $ foldr (.) id [ subst n t | (n, t) <- res ]) tcArgs
  return argTys'
  where
  tyTry' = vToP tyTry
  holes = map fst nonTcArgs
  retTy = getRetTy tyTry'
  (tcArgs, nonTcArgs) = partition (isTypeClassArg classInfo . snd) $ getArgTys tyTry'

isTypeClassArg :: Ctxt ClassInfo -> Type -> Bool
isTypeClassArg classInfo ty = not (null (getClassName clss >>= flip lookupCtxt classInfo)) where
  (clss, args) = unApply ty
  getClassName (P (TCon _ _) className _) = [className]
  getClassName _ = []


instance Ord Score where
  compare = comparing defaultScoreFunction

-- | Compute the power set
subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (x : xs) = let ss = subsets xs in map (x :) ss ++ ss


--DONT run vToP first!
-- | Try to match two types together in a unification-like procedure.
-- Returns a list of types and their minimum scores, sorted in order
-- of increasing score.
matchTypesBulk :: forall info. IState -> Int -> Type -> [(info, Type)] -> [(info, Score)]
matchTypesBulk istate maxScore type1 types = getAllResults startQueueOfQueues where
  getStartQueue :: (info, Type) -> Maybe (Score, (info, Q.PQueue Score State))
  getStartQueue nty@(info, type2) = do
    state <- unifyQueue (State startingHoles dag1 dag2 
              typeClassArgs1 typeClassArgs2
              mempty usedNames) startingTypes
    let sc = score state
    return $ (sc, (info, Q.singleton sc state))
    where
    (dag2, typeClassArgs2, retTy2) = makeDag (uniqueBinders (map fst argNames1) type2)
    argNames2 = map fst dag2
    usedNames = map fst (argNames1 ++ argNames2)
    startingHoles = argNames1 ++ argNames2

    startingTypes = (retTy1, retTy2) : [] 


  startQueueOfQueues :: Q.PQueue Score (info, Q.PQueue Score State)
  startQueueOfQueues = Q.fromList $ mapMaybe getStartQueue types

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
          Just (Right score) -> (info, score) : getAllResults q'
        else []


  ctxt = tt_ctxt istate
  classInfo = idris_classes istate

  (dag1, typeClassArgs1, retTy1) = makeDag type1
  argNames1 = map fst dag1
  makeDag :: Type -> (ArgsDAG, [(Name, Type)], Type)
  makeDag = first3 (zipWith (\i (ty, deps) -> (ty, (i, deps))) [0..] . reverseDag) . 
    computeDagP (isTypeClassArg classInfo) . vToP
  first3 f (a,b,c) = (f a, b, c)
  
  -- update our state with the unification resolutions
  resolveUnis :: [(Name, Type)] -> State -> Maybe (State, [(Type, Type)])
  resolveUnis [] state = Just (state, [])
  resolveUnis ((name, term@(P Bound name2 _)) : xs) 
    state@(State holes args1 args2 _ _ _ _) | isJust findArgs = do
    ((ty1, ix1), (ty2, ix2)) <- findArgs

    (state'', queue) <- resolveUnis xs state'
    let transScore = fromMaybe 0 (abs <$> ((-) <$> ix1 <*> ix2))
    return $ (inScore (\s -> s { transposition = transposition s + transScore }) state'', (ty1, ty2) : queue)
    where
    mgetType name xs = fmap ((snd . fst) &&& (fst . snd)) . find ((name ==) . fst . fst) $ xs
    inScore f state = state { score = f (score state) }
    findArgs = ((,) <$> findLeft name state <*> findRight name2 state) <|>
               ((,) <$> findLeft name2 state <*> findRight name state)
    matchnames = [name, name2]
    holes' = filter (not . (`elem` matchnames) . fst) holes
    deleteArgs = deleteLeft name . deleteLeft name2 . deleteRight name . deleteRight name2
    state' = modifyTypes (subst name term) $ deleteArgs
              (state { holes = holes'})

  resolveUnis ((name, term) : xs)
    state@(State holes args1 args2 _ _ _ _) = case (findLeft name state, findRight name state) of
      (Just (_,ix), Nothing) -> first (inScore (\score -> score { leftApplied = succ (leftApplied score) })) <$> nextStep
      (Nothing, Just (_, ix)) -> first (inScore (\score -> score { rightApplied = succ (rightApplied score) })) <$> nextStep
      (Nothing, Nothing) -> nextStep
      _ -> error ("Idris internal error: TypeSearch.resolveUnis")
    where
    -- find variables which are determined uniquely by the type
    -- due to injectivity
    varsInTy = M.keys $ usedVars True term
    toDelete = name : varsInTy
    deleteMany = foldr (.) id $ [ deleteLeft t . deleteRight t | t <- toDelete ]

    inScore f state = state { score = f (score state) }
    state' = modifyTypes (subst name term) . deleteMany $ 
               state { holes = filter (not . (`elem` toDelete) . fst) holes }
    nextStep = resolveUnis xs state'


  -- | resolve a queue of unification constraints
  unifyQueue :: State -> [(Type, Type)] -> Maybe State
  unifyQueue state [] = return state
  unifyQueue state ((ty1, ty2) : queue) = do
    --trace ("go: \n" ++ show state) True `seq` return ()
    res <- tcToMaybe $ match_unify ctxt [ (n, Pi ty) | (n, ty) <- holes state] ty1 ty2 [] (map fst $ holes state) []
    (state', queueAdditions) <- resolveUnis res state
    guard $ scoreCriterion (score state')
    unifyQueue state' (queue ++ queueAdditions)

  possClassInstances :: [Name] -> Type -> [Type]
  possClassInstances usedNames ty = do
    className <- getClassName clss
    classDef <- lookupCtxt className classInfo
    n <- class_instances classDef
    def <- lookupCtxt n (definitions ctxt)
    ty <- normaliseC ctxt [] <$> (case typeFromDef def of Just x -> [x]; Nothing -> [])
    let ty' = vToP (uniqueBinders usedNames ty)
    return ty'
    where
    (clss, _) = unApply ty
    getClassName (P (TCon _ _) className _) = [className]
    getClassName _ = []

  -- Just if the computation hasn't totally failed yet, Nothing if it has
  -- Left if we haven't found a terminal state, Right if we have
  nextStepsQueue :: Q.PQueue Score State -> Maybe (Either (Q.PQueue Score State) Score)
  nextStepsQueue queue = do
    ((nextScore, next), rest) <- Q.minViewWithKey queue
    if isFinal next 
      then Just $ Right nextScore
      else let additions = if scoreCriterion nextScore
                 then Q.fromList [ (score state, state) | state <- nextSteps next ]
                 else Q.empty in
           Just $ Left (Q.union rest additions)
    where
    isFinal (State [] [] [] [] [] score _) = True
    isFinal _ = False

  -- | Find all possible matches starting from a given state.
  -- We go in stages rather than concatenating all three results in hopes of narrowing
  -- the search tree. Once we advance in a phase, there should be no going back.
  nextSteps :: State -> [State]

  -- Stage 3 - match typeclasses
  nextSteps (State [] [] [] c1 c2 scoreAcc usedNames) = 
    if null results3 then results4 else results3
    where
    -- try to match a typeclass argument from the left with a typeclass argument from the right
    results3 =
         catMaybes [ unifyQueue (State [] [] []
         (deleteFromArgList n1 c1) (map (second subst2for1) (deleteFromArgList n2 c2)) scoreAcc usedNames) [(ty1, ty2)] 
     | (n1, ty1) <- c1, (n2, ty2) <- c2, let subst2for1 = psubst n2 (P Bound n1 ty1)]

    -- try to hunt match a typeclass constraint by replacing it with an instance
    results4 = results4A ++ results4B
    typeClassArgs classes = [ ((n, ty), inst) | (n, ty) <- classes, inst <- possClassInstances usedNames ty ]
    results4A = [ State [] [] []
                  (deleteFromArgList n c1 ++ newClassArgs) c2
                  (scoreAcc `mappend` (mempty { leftTypeClassApp = 1 }))
                  (usedNames ++ newHoles)
                | ((n, ty), inst) <- typeClassArgs c1
                , newClassArgs <- maybeToList $ typeclassUnify classInfo ctxt ty inst
                , let newHoles = map fst newClassArgs ]
    results4B = [ State [] [] []
                  c1 (deleteFromArgList n c2 ++ newClassArgs)
                  (scoreAcc `mappend` (mempty { rightTypeClassApp = 1 }))
                  (usedNames ++ newHoles)
                | ((n, ty), inst) <- typeClassArgs c2
                , newClassArgs <- maybeToList $ typeclassUnify classInfo ctxt ty inst
                , let newHoles = map fst newClassArgs ]


  -- Stage 1 - match arguments
  nextSteps (State holes dag1 dag2 c1 c2 scoreAcc usedNames) = results where

    results = concatMap takeSomeClasses results1

    -- we only try to match arguments whose names don't appear in the types
    -- of any other arguments
    canBeFirst :: ArgsDAG -> [(Name, Type)]
    canBeFirst = map fst . filter (S.null . snd . snd)

    -- try to match an argument from the left with an argument from the right
    results1 = catMaybes [ unifyQueue (State (filter (not . (`elem` [n1,n2]) . fst) holes) (deleteFromDag n1 dag1)
         ((inArgTys subst2for1) $ deleteFromDag n2 dag2) c1 (map (second subst2for1) c2) scoreAcc usedNames) [(ty1, ty2)] 
     | (n1, ty1) <- canBeFirst dag1, (n2, ty2) <- canBeFirst dag2, let subst2for1 = psubst n2 (P Bound n1 ty1)]


    -- Stage 2 - simply introduce a subset of the typeclasses
    -- we've finished, so take some classes
    takeSomeClasses (State [] [] [] c1 c2 scoreAcc usedNames) = 
      let lc1 = length c1; lc2 = length c2 in
       [ State [] [] [] c1' c2' (scoreAcc `mappend` 
           mempty { rightTypeClassIntro = lc1 - length c1',
                    leftTypeClassIntro  = lc2 - length c2' }) usedNames
       | c1' <- subsets c1, c2' <- subsets c2 ]
    -- still have arguments to match, so just be the identity
    takeSomeClasses s = [s]

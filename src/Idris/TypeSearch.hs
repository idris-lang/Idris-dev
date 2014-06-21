module Idris.TypeSearch (
  searchByType, searchPred, defaultScoreFunction
) where

import Control.Applicative ((<$>), (<*>), (<|>))
import Control.Arrow (first, second, (&&&))
import Control.Monad (forM_, guard)

import Data.Function (on)
import Data.List (find, minimumBy, partition, sortBy, (\\))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Monoid (Monoid (mempty, mappend))
import Data.Set (Set)
import qualified Data.Set as S

import Idris.AbsSyntax (addUsingConstraints, addImpl, getContext, getIState, putIState, implicit)
import Idris.AbsSyntaxTree (class_instances, defaultSyntax, Idris, 
  IState (idris_classes, idris_docstrings, tt_ctxt),
  implicitAllowed, prettyDocumentedIst, prettyIst, PTerm, toplevel)
import Idris.Core.Evaluate (Context (definitions), Def (Function, TyDecl, CaseOp), normaliseC)
import Idris.Core.TT hiding (score)
import Idris.Core.Unify (match_unify)
import Idris.Delaborate (delab, delabTy)
import Idris.Docstrings (noDocs, overview)
import Idris.ElabDecls (elabType')
import Idris.Output (ihRenderResult, ihPrintResult, ihPrintFunTypes)

import System.IO (Handle)

import Util.Pretty (text, vsep, char, (<>), Doc)

searchByType :: Handle -> PTerm -> Idris ()
searchByType h pterm = do
  pterm' <- addUsingConstraints syn emptyFC pterm
  pterm'' <- implicit toplevel syn n pterm'
  i <- getIState
  let pterm'''  = addImpl i pterm''
  ty <- elabType' False toplevel syn (fst noDocs) (snd noDocs) emptyFC [] n pterm'
  putIState i -- don't actually make any changes
  let names = searchUsing searchPred i ty
  let names' = take numLimit . takeWhile ((< scoreLimit) . getScore) $ 
         sortBy (compare `on` getScore) names
  let docs =
       [ let docInfo = (n, delabTy i n, fmap (overview . fst) (lookupCtxtExact n (idris_docstrings i))) in
         displayScore score <> char ' ' <> prettyDocumentedIst i docInfo
                | (n, (_,score)) <- names']
  ihRenderResult h $ vsep docs
  where 
    getScore = defaultScoreFunction . snd . snd
    numLimit = 50
    scoreLimit = 100
    syn = defaultSyntax { implicitAllowed = True } -- syntax
    n = sMN 0 "searchType" -- name
  
-- | Conduct a type-directed search using a given match predicate
searchUsing :: (IState -> Type -> Type -> Maybe a) -> IState -> Type -> [(Name, (Type, a))]
searchUsing pred istate ty = 
  concat . M.elems $ M.mapWithKey (\key -> M.toAscList . M.mapMaybe (f key)) (definitions ctxt)
  where
  ctxt = tt_ctxt istate
  f k x = do
    guard $ not (special k)
    y <- get (fst4 x)
    let ny = normaliseC ctxt [] y
    val <- pred istate nty ny
    return (y, val)
  nty = normaliseC ctxt [] ty
  fst4 :: (a,b,c,d) -> a
  fst4 (w,x,y,z) = w
  get :: Def -> Maybe Type
  get (Function ty tm) = Just ty
  get (TyDecl _ ty) = Just ty
 -- get (Operator ty _ _) = Just ty
  get (CaseOp _ ty _ _ _ _)  = Just ty
  get _ = Nothing
  special :: Name -> Bool
  special (SN _) = True
  special _ = False

-- Our default search predicate.
searchPred :: IState -> Type -> Type -> Maybe Score
searchPred istate ty1 = \ty2 -> case matcher ty2 of
  xs -> guard (not (null xs)) >> return (minimumBy (compare `on` defaultScoreFunction) xs)
  where
  matcher = unifyWithHoles istate ty1


typeFromDef :: (Def, b, c, d) -> Maybe Type
typeFromDef (def, _, _, _) = get def where
  get :: Def -> Maybe Type
  get (Function ty tm) = Just ty
  get (TyDecl _ ty) = Just ty
 -- get (Operator ty _ _) = Just ty
  get (CaseOp _ ty _ _ _ _)  = Just ty
  get _ = Nothing

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
  f (n, t) = ((n, t), M.keysSet (usedVars t))

  (numArgs, args, removedArgs, retTy) = go 0 [] [] t

  -- NOTE : args are in reverse order
  go k args removedArgs (Bind n (Pi t) sc) = let arg = (n, t) in
    if removePred t
      then go k        args (arg : removedArgs) sc
      else go (succ k) (arg : args) removedArgs sc
  go k args removedArgs retTy = (k, args, removedArgs, retTy)

-- | Collect the names and types of all the free variables
usedVars :: Ord n => TT n -> Map n (TT n)
usedVars (V j) = error "unexpected! run vToP first"
usedVars (P Bound n t) = M.singleton n t `M.union` usedVars t
usedVars (Bind n binder t2) = (M.delete n (usedVars t2) `M.union`) $ case binder of
  Let t v ->   usedVars t `M.union` usedVars v
  Guess t v -> usedVars t `M.union` usedVars v
  b -> usedVars (binderTy b)
usedVars (App t1 t2) = usedVars t1 `M.union` usedVars t2
usedVars (Proj t _) = usedVars t
usedVars _ = M.empty

deleteFromDag :: Ord n => n -> [((n, TT n), (a, Set n))] -> [((n, TT n), (a, Set n))]
deleteFromDag name [] = []
deleteFromDag name (((name2, ty), (ix, set)) : xs) = (if name == name2
  then id
  else (((name2, ty) , (ix, S.delete name set)) :) ) (deleteFromDag name xs)

deleteFromArgList :: Ord n => n -> [(n, TT n)] -> [(n, TT n)]
deleteFromArgList n = filter ((/= n) . fst)

data Score = Score
  { transposition :: Int
  , leftApplied   :: Int
  , rightApplied  :: Int
  , leftTypeClass :: Int
  , rightTypeClass :: Int } deriving (Eq, Show)

displayScore :: Score -> Doc a
displayScore (Score trans lapp rapp lclass rclass) = text $ case (lt, gt) of
  (True , True ) -> "=" -- types are isomorphic
  (True , False) -> "<" -- found type is more general than searched type
  (False, True ) -> ">" -- searched type is more general than found type
  (False, False) -> " "
  where lt = lapp + lclass == 0
        gt = rapp + rclass == 0


scoreCriterion :: Score -> Bool
scoreCriterion (Score a b c d e) = not
  ( (b > 0 && c > 0) || (b + c) > 4 || d > 3 || e > 3 )

defaultScoreFunction :: Score -> Int
defaultScoreFunction (Score a b c d e) = a + 9*b + 3*c + 12*d + 4*e + 100*(2*b + d)*(2*c + e)
  -- it's very bad to have *both* upcasting and downcasting

instance Monoid Score where
  mempty = Score 0 0 0 0 0
  (Score a b c d e) `mappend` (Score a' b' c' d' e') = Score (a + a') (b + b') (c + c') (d + d') (e + e')

-- | A directed acyclic graph representing the arguments to a function
-- The 'Int' represents the position of the argument (1st argument, 2nd, etc.)
type ArgsDAG = [((Name, Type), (Int, Set Name))]

-- | The state corresponding to an attempted match of two types.
data State = State
  { holes :: ![Name] -- ^ names which have yet to be resolved
  , args1 :: !ArgsDAG -- ^ arguments for the left  type which have yet to be resolved
  , args2 :: !ArgsDAG -- ^ arguments for the right type which have yet to be resolved
  , classes1 :: ![(Name, Type)] -- ^ typeclass arguments for the left  type which haven't been resolved
  , classes2 :: ![(Name, Type)] -- & typeclass arguments for the right type which haven't been resolved
  , score :: !Score -- ^ the score so far
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


--DONT run vToP first!
-- | Try to match two types together in a unification-like procedure.
-- Returns a list of possible scores representing ways in which the two
-- types can be matched.
unifyWithHoles :: IState -> Type -> Type -> [Score]
unifyWithHoles istate type1 = \type2 -> let
  (dag2, typeClassArgs2, retTy2) = makeDag (uniqueBinders argNames1 type2)
  argNames2 = map (fst . fst) dag2
  startingHoles = argNames1 ++ argNames2

  startingTypes = (retTy1, retTy2) : [] 
  in case unifyQueue (State startingHoles dag1 dag2 
              typeClassArgs1 typeClassArgs2
              mempty startingHoles) startingTypes
     of Nothing    -> []
        Just state -> possibleMatches state
  where
  ctxt = tt_ctxt istate
  classInfo = idris_classes istate

  isTypeClassArg :: Type -> Bool
  isTypeClassArg ty = not (null (getClassName clss >>= flip lookupCtxt classInfo)) where
    (clss, args) = unApply ty
    getClassName (P (TCon _ _) className _) = [className]
    getClassName _ = []

  (dag1, typeClassArgs1, retTy1) = makeDag type1
  argNames1 = map (fst . fst) dag1
  makeDag :: Type -> (ArgsDAG, [(Name, Type)], Type)
  makeDag = first3 (zipWith (\i (ty, deps) -> (ty, (i, deps))) [0..] . reverseDag) . computeDagP isTypeClassArg . vToP
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
    holes' = holes \\ matchnames
    deleteArgs = deleteLeft name . deleteLeft name2 . deleteRight name . deleteRight name2
    state' = modifyTypes (subst name term) $ deleteArgs
              (state { holes = holes'})

  resolveUnis ((name, term) : xs)
    state@(State holes args1 args2 _ _ _ _) = case (findLeft name state, findRight name state) of
        (Just (_,ix), Nothing) -> first (inScore (\score -> score { leftApplied = succ (leftApplied score) })) <$> nextStep
        (Nothing, Just (_, ix)) -> first (inScore (\score -> score { rightApplied = succ (rightApplied score) })) <$> nextStep
        (Nothing, Nothing) -> nextStep
        _ -> error ("Shouldn't happen. Watch the alpha conversion!\n" ++ show args1 ++ "\n\n" ++ show args2)
    where
    inScore f state = state { score = f (score state) }
    state' = modifyTypes (subst name term) . deleteLeft name . deleteRight name $ 
               state { holes = holes \\ [name]}
    nextStep = resolveUnis xs state'


  -- | resolve a queue of unification constraints
  unifyQueue :: State -> [(Type, Type)] -> Maybe State
  unifyQueue state [] = return state
  unifyQueue state ((ty1, ty2) : queue) = do
    res <- tcToMaybe $ match_unify ctxt [] ty1 ty2 [] (holes state) []
    (state', queueAdditions) <- resolveUnis res state
    guard $ scoreCriterion (score state')
    unifyQueue state' (queue ++ queueAdditions)

  possClassInstances :: [Name] -> Type -> [([(Name, Type)], Type)]
  possClassInstances usedNames ty = do
    className <- getClassName clss
    classDef <- lookupCtxt className classInfo
    n <- class_instances classDef
    def <- lookupCtxt n (definitions ctxt)
    ty <- normaliseC ctxt [] <$> (case typeFromDef def of Just x -> [x]; Nothing -> [])
    let ty' = vToP (uniqueBinders usedNames ty)
    return (getArgTys ty', getRetTy ty')
    where
    (clss, args) = unApply ty
    getClassName (P (TCon _ _) className _) = [className]
    getClassName _ = []

  -- | Find all possible matches starting from a given state.
  possibleMatches :: State -> [Score]
  possibleMatches (State [] [] [] [] [] scoreAcc _) = [scoreAcc]
  possibleMatches (State holes dag1 dag2 c1 c2 scoreAcc usedNames) = 
    concat [ possibleMatches state | state <- results, scoreCriterion (score state) ] where

    -- we only try to match arguments whose names don't appear in the types
    -- of any other arguments
    canBeFirst :: ArgsDAG -> [(Name, Type)]
    canBeFirst = map fst . filter (S.null . snd . snd)

    -- this is done rather than concatenating all three results in hopes of narrowing
    -- the search tree
    results = fromMaybe [] $ find (not . null) [results1, results2, results3]

    -- try to match an argument from the left with an argument from the right
    results1 = catMaybes [ unifyQueue (State (holes \\ [n1, n2]) (deleteFromDag n1 dag1)
         ((inArgTys subst2for1) $ deleteFromDag n2 dag2) c1 (map (second subst2for1) c2) scoreAcc usedNames) [(ty1, ty2)] 
     | (n1, ty1) <- canBeFirst dag1, (n2, ty2) <- canBeFirst dag2, let subst2for1 = psubst n2 (P Bound n1 ty1)]

    -- try to match a typeclass argument from the left with a typeclass argument from the right
    results2 = catMaybes [ unifyQueue (State (holes \\ [n1, n2]) dag1 (inArgTys subst2for1 dag2)
         (deleteFromArgList n1 c1) (map (second subst2for1) (deleteFromArgList n2 c2)) scoreAcc usedNames) [(ty1, ty2)] 
     | (n1, ty1) <- c1, (n2, ty2) <- c2, let subst2for1 = psubst n2 (P Bound n1 ty1)]

    -- try to hunt match a typeclass constraint by replacing it with an instance
    results3 = if null dag1 || null dag2 then catMaybes (results3A ++ results3B) else []
    typeClassArgs classes = [ ((n, ty), inst) | (n, ty) <- classes, inst <- possClassInstances usedNames ty ]
    noDeps (n, ty) = ((n, ty), (0, S.empty))
    results3A = [ unifyQueue
                 (State ((holes \\ [n]) ++ newHoles) (dag1 ++ map noDeps newNonClassArgs) dag2
                   (deleteFromArgList n c1 ++ newClassArgs) c2
                   (scoreAcc `mappend` (mempty { leftTypeClass = 1 }))
                   (usedNames ++ newHoles)
                 )
                 [(ty, inst)]
               | ((n, ty), (newArgs, inst)) <- typeClassArgs c1, let newHoles = map fst newArgs
                , let (newClassArgs, newNonClassArgs) = partition (isTypeClassArg . snd) newArgs ]
    results3B = [ unifyQueue
                 (State ((holes \\ [n]) ++ newHoles) dag1 (dag2 ++ map noDeps newNonClassArgs)
                   c1 (deleteFromArgList n c2 ++ newClassArgs)
                   (scoreAcc `mappend` (mempty { rightTypeClass = 1 }))
                   (usedNames ++ newHoles)
                 )
                 [(ty, inst)]
               | ((n, ty), (newArgs, inst)) <- typeClassArgs c2, let newHoles = map fst newArgs
                 , let (newClassArgs, newNonClassArgs) = partition (isTypeClassArg . snd) newArgs ]


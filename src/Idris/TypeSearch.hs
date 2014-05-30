module Idris.TypeSearch (
  searchByType, searchPred, defaultScoreFunction
) where

import Control.Applicative ((<$>), (<*>), (<|>))
import Control.Arrow (first, second, (&&&))
import Control.Monad (forM_, guard)

import Data.Function (on)
import Data.List (find, sortBy, (\\))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Data.Monoid (Monoid (mempty, mappend))
import Data.Set (Set)
import qualified Data.Set as S

import Idris.AbsSyntax (addUsingConstraints, addImpl, getContext, getIState, putIState, implicit)
import Idris.AbsSyntaxTree (class_instances, defaultSyntax, Idris, 
  IState (idris_classes, tt_ctxt),
  implicitAllowed, prettyIst, PTerm, toplevel)
import Idris.Core.Evaluate (Context (definitions), Def (Function, TyDecl, CaseOp), normaliseC)
import Idris.Core.TT
import Idris.Core.Unify (match_unify)
import Idris.Delaborate (delab, delabTy)
import Idris.Docstrings (noDocs)
import Idris.ElabDecls (elabType')
import Idris.Output (ihRenderResult, ihPrintResult, ihPrintFunTypes)

import System.IO (Handle)


searchByType :: (Ord a, Show a) => Handle -> (IState -> Type -> Type -> Maybe a) -> a -> PTerm -> Idris ()
searchByType h pred scoreLimit pterm = do
  pterm' <- addUsingConstraints syn emptyFC pterm
  pterm'' <- implicit toplevel syn n pterm'
  i <- getIState
  let pterm'''  = addImpl i pterm''
  ty <- elabType' False toplevel syn (fst noDocs) (snd noDocs) emptyFC [] n pterm'
  putIState i -- don't actually make any changes
  ihRenderResult h (prettyIst i pterm)
  let names = searchUsing pred i ty
  let names' = take numLimit . takeWhile ((< scoreLimit) . snd . snd) $ 
         sortBy (compare `on` (snd . snd)) names
  forM_ names' $ \(name, (typ, val)) -> do
    ihPrintFunTypes h [] name [(name, delabTy i name)]
    ihPrintResult h ("\tScore: " ++ show val ++ "\n")
  where 
    numLimit = 50
    syn = defaultSyntax { implicitAllowed = True } -- syntax
    n = sMN 0 "searchType" -- name


searchUsing :: (IState -> Type -> Type -> Maybe a) -> IState -> Type -> [(Name, (Type, a))]
searchUsing pred istate ty = 
  concat . M.elems $ M.mapWithKey (\key -> M.toAscList . M.mapMaybe (f key)) (definitions ctxt)
  where
  ctxt = tt_ctxt istate
  f k x = do
    guard $ not (special k)
    y <- get (fst4 x)
    let ny = normaliseC ctxt [] y
  --  traceShow k False `seq` return ()
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


tcToMaybe :: TC' e a -> Maybe a
tcToMaybe (OK x) = Just x
tcToMaybe (Error _) = Nothing



searchPred :: (Score -> Int) -> IState -> Type -> Type -> Maybe Int
searchPred scoref istate ty1 = \ty2 -> case matcher ty2 of
  Nothing -> Nothing
  Just xs -> guard (not (null xs)) >> return (minimum (map scoref xs))
  where
  matcher = unifyWithHoles True istate ty1




reverseDag :: Ord k => [((k, a), Set k)] -> [((k, a), Set k)]
reverseDag xs = map f xs where
  f ((k, v), _) = ((k, v), S.fromList . map (fst . fst) $ filter (S.member k . snd) xs)

-- run vToP first!
-- returns [(the name and type of the bound variable
--          the names in the type of the bound variable)]
computeDagP :: Ord n => TT n -> ([((n, TT n), Set n)], TT n)
computeDagP t = (reverse (map f args), retTy) where

  f (n, t) = ((n, t), M.keysSet (usedVars t))

  (numArgs, args, retTy) = go 0 [] t

  -- NOTE : args are in reverse order
  go k args (Bind n (Pi t) sc) = go (succ k) ( (n, t) : args ) sc
  go k args retTy = (k, args, retTy)


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


data Score = Score
  { transposition :: Int
  , leftApplied   :: Int
  , rightApplied  :: Int
  , leftTypeClass :: Int
  , rightTypeClass :: Int } deriving (Eq, Show)


scoreCriterion :: Score -> Bool
scoreCriterion (Score a b c d e) = True {- not
  ( (b > 0 && c > 0) || (b + c) > 2 ) -}

defaultScoreFunction :: Score -> Int
defaultScoreFunction (Score a b c d e) = a + 9*b + 3*c + 12*d + 4*e + 100*(2*b + d)*(2*c + e)
  -- it's very bad to have *both* upcasting and downcasting

instance Monoid Score where
  mempty = Score 0 0 0 0 0
  (Score a b c d e) `mappend` (Score a' b' c' d' e') = Score (a + a') (b + b') (c + c') (d + d') (e + e')


type ArgsDAG = [((Name, Type), (Int, Set Name))]
type ResType = ( [Name] , ArgsDAG , ArgsDAG )

data State = State
  { holes :: ![Name]
  , args1 :: !ArgsDAG
  , args2 :: !ArgsDAG
  , score :: !Score
  }


--DONT run vToP first!
unifyWithHoles :: Bool -> IState -> Type -> Type -> Maybe [Score]
unifyWithHoles debugParam istate type1 = \type2 -> let
  (dag2, retTy2) = makeDag (uniqueBinders argNames1 type2)
  argNames2 = map (fst . fst) dag2
  startingHoles = argNames1 ++ argNames2

  startingTypes = (retTy1, retTy2) : [] 
  in do 
  state <- go (State startingHoles dag1 dag2 mempty) startingTypes
  return $ processDags state
  where
  ctxt = tt_ctxt istate
  classInfo = idris_classes istate
  (dag1, retTy1) = makeDag type1
  argNames1 = map (fst . fst) dag1
  makeDag = first (zipWith (\i (ty, deps) -> (ty, (i, deps))) [0..] . reverseDag) . computeDagP . vToP

  matchf :: (Name, Term) -> Maybe (Name, Name)
  matchf (name, P Bound name2 _) = Just (name, name2)
  matchf _ = Nothing
  
  -- update our state with the unification resolutions
  updateDags :: [(Name, Type)] -> ResType -> Maybe (ResType, [(Type, Type)], Score)
  updateDags [] res = Just (res, [], mempty)
  updateDags ((name, term@(P Bound name2 _)) : xs) (holes, args1, args2) | isJust findArgs = do
    ((ty1, ix1), (ty2, ix2)) <- findArgs

    (res, queue, score) <- updateDags xs (holes', args1'', args2'')
    --traceShow (ty1, ty2) False `seq` return ()
    return $ (res, (ty1, ty2) : queue , score { transposition = transposition score + abs (ix2 - ix1) })
    where
    findArgs = ((,) <$> mgetType name args1 <*> mgetType name2 args2) <|>
               ((,) <$> mgetType name2 args1 <*> mgetType name args2)
    matchnames = [name, name2]
    holes' = holes \\ matchnames
    substf = deleteFromDag name . deleteFromDag name2
    args1' = substf args1
    args2' = substf args2
    args1'' = map (first . second $ subst name term) args1'
    args2'' = map (first . second $ subst name term) args2'
    mgetType name xs = fmap ((snd . fst) &&& (fst . snd)) . find ((name ==) . fst . fst) $ xs

  updateDags ((name, term) : xs) (holes, args1, args2) = case (mgetType name args1, mgetType name args2) of
        (Just (_,ix), Nothing) -> thrd (\score -> score { leftApplied = succ (leftApplied score) }) <$> nextStep
        (Nothing, Just (_, ix)) -> thrd (\score -> score { rightApplied = succ (rightApplied score) }) <$> nextStep
        (Nothing, Nothing) -> nextStep
        _ -> error ("Shouldn't happen. Watch the alpha conversion!\n" ++ show args1 ++ "\n\n" ++ show args2)
    where
    varsInTy = map fst $ M.toList (usedVars term)
    deleteMany = foldr (.) id $ map deleteFromDag (name : varsInTy)
    thrd f (a,b,c) = (a,b,f c)
    nextStep = updateDags xs (holes \\ [name], updatef args1, updatef args2 )
    updatef = map (first . second $ subst name term) . deleteMany
    mgetType name xs = fmap ((snd . fst) &&& (fst . snd)) . find ((name ==) . fst . fst) $ xs


  go :: State -> [(Type, Type)] -> Maybe State
  --go (State holes args1 args2 score) queue | trace ("go\n\t" ++ show holes ++ "\n\t" ++ show args1 ++ "\n\t" ++ show args2 ++ "\n\t" ++ show queue) False = undefined
  go state [] = return state
  go (State holes args1 args2 score) ((ty1, ty2) : queue) = do
    res <- tcToMaybe $ match_unify ctxt [] ty1 ty2 [] holes []
    --trace ("UnifyResult: " ++ show (ty1, ty2, res, errors)) False `seq` return ()
    --guard (null errors)
    ((holes', args1', args2'), queueAdditions, scoreAdditions) <- updateDags res (holes, args1, args2)
    let newScore = score `mappend` scoreAdditions
    guard $ scoreCriterion newScore
    go (State holes' args1' args2' newScore) (queue ++ queueAdditions)


  processDags :: State -> [Score]
  processDags (State [] [] [] scoreAcc) = [scoreAcc]
  --processDags (State holes (_:_) [] scoreAcc) = []
  --processDags (State holes [] (_:_) scoreAcc) = []
  processDags (State holes dag1 dag2 scoreAcc) = concat [ processDags state | state <- allResults ] where

    results = catMaybes [ go (State (holes \\ (map nameOf [ty1, ty2])) (deleteFromDag (nameOf ty1) dag1)
         (inArgTys (psubst (nameOf ty2) (P Bound (nameOf ty1) (typeOf ty1))) $ deleteFromDag (nameOf ty2) dag2) scoreAcc) [(typeOf ty1, typeOf ty2)] 
     | ty1 <- canBeFirst dag1, ty2 <- canBeFirst dag2 {-, exactTypeEquality ctxt (typeOf ty1) (typeOf ty2) -} ]

    results2 = [ State (holes \\ [nameOf ty]) 
               (deleteFromDag (nameOf ty) dag1) dag2
               (scoreAcc `mappend` (mempty { leftTypeClass = 1 }))
               | ty <- typeClassArgs1 ]

    typeClassArgs1 = filter (isSaturatedClass . typeOf) dag1
    typeClassArgs2 = filter (isSaturatedClass . typeOf) dag2


    results3 = [ State (holes \\ [nameOf ty]) 
               dag1 (deleteFromDag (nameOf ty) dag2)
               (scoreAcc `mappend` (mempty { rightTypeClass = 1 }))
               | ty <- typeClassArgs2 ]

    allResults :: [State]
    allResults = {- (if not (null typeClasses) then (traceShow typeClasses False `seq` id) else id ) -}
                 (results ++ results2 ++ results3)
      where
      typeClasses = filter (isSaturatedClass . typeOf) (dag1 ++ dag2)
               

    -- check if the canBeFirst thing is losing any possibilities


    inArgTys = map . first . second
    typeOf ((name, ty), set) = ty
    nameOf ((name, ty), set) = name

    -- XXX : debug stuff
    canBeFirst = if debugParam then filter (S.null . snd . snd) else id
    holes = map (fst . fst) dag1 ++ map (fst . fst) dag2

    deleteIdx _ [] = []
    deleteIdx idx l@(x@(i,_,_) : xs) = if i == idx then xs else x : deleteIdx idx xs

  isSaturatedClass :: Type -> Bool
  isSaturatedClass ty = fromMaybe False $ do
    className <- getClassName clss
    let possInstances = concatMap class_instances $ lookupCtxt className classInfo 
    return $ (SN (sInstanceN className (map argToName args))) `elem` possInstances
    where
    (clss, args) = unApply ty
    getClassName (P (TCon _ _) className _) = Just className
    getClassName _ = Nothing
    argToName arg = show (delab istate arg)


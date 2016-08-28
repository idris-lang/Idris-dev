{-|
Module      : Idris.Elab.Utils
Description : Elaborator utilities.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Utils where

import Idris.AbsSyntax
import Idris.Error
import Idris.DeepSeq
import Idris.Delaborate
import Idris.Docstrings
import Idris.Output

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Typecheck

import Util.Pretty

import Control.Applicative hiding (Const)
import Control.Monad.State
import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Traversable as Traversable

import Debug.Trace

import qualified Data.Map as Map

recheckC = recheckC_borrowing False True []

recheckC_borrowing uniq_check addConstrs bs tcns fc mkerr env t
    = do -- t' <- applyOpts (forget t) (doesn't work, or speed things up...)
         
         ctxt <- getContext
         t' <- case safeForget t of
                    Just ft -> return ft
                    Nothing -> tclift $ tfail $ mkerr (At fc (IncompleteTerm t))
         (tm, ty, cs) <- tclift $ case recheck_borrowing uniq_check bs tcns ctxt env t' t of
                                   Error e -> tfail (At fc (mkerr e))
                                   OK x -> return x
         logElab 6 $ "CONSTRAINTS ADDED: " ++ show (tm, ty, cs)
         tit <- typeInType
         when (not tit && addConstrs) $ 
                           do addConstraints fc cs
                              mapM_ (\c -> addIBC (IBCConstraint fc c)) (snd cs)
         mapM_ (checkDeprecated fc) (allTTNames tm)
         mapM_ (checkDeprecated fc) (allTTNames ty)
         mapM_ (checkFragile fc) (allTTNames tm)
         mapM_ (checkFragile fc) (allTTNames ty)

         return (tm, ty)

checkDeprecated :: FC -> Name -> Idris ()
checkDeprecated fc n
    = do r <- getDeprecated n
         case r of
              Nothing -> return ()
              Just r -> do iWarn fc $ text "Use of deprecated name " <> annName n
                                 <> case r of
                                         "" -> Util.Pretty.empty
                                         _ -> line <> text r


checkFragile :: FC -> Name -> Idris ()
checkFragile fc n = do
  r <- getFragile n
  case r of
    Nothing -> return ()
    Just r  -> do
      iWarn fc $ text "Use of a fragile construct "
                     <> annName n
                     <> case r of
                          "" -> Util.Pretty.empty
                          _  -> line <> text r


iderr :: Name -> Err -> Err
iderr _ e = e

checkDef :: ElabInfo -> FC -> (Name -> Err -> Err) -> Bool ->
            [(Name, (Int, Maybe Name, Type, [Name]))] ->
            Idris [(Name, (Int, Maybe Name, Type, [Name]))]
checkDef info fc mkerr definable ns
   = checkAddDef False True info fc mkerr definable ns

checkAddDef :: Bool -> Bool -> ElabInfo -> FC -> (Name -> Err -> Err) -> Bool
            -> [(Name, (Int, Maybe Name, Type, [Name]))]
            -> Idris [(Name, (Int, Maybe Name, Type, [Name]))]
checkAddDef add toplvl info fc mkerr def [] = return []
checkAddDef add toplvl info fc mkerr definable ((n, (i, top, t, psns)) : ns)
               = do ctxt <- getContext
                    logElab 5 $ "Rechecking deferred name " ++ show (n, t, definable)
                    (t', _) <- recheckC (constraintNS info) fc (mkerr n) [] t
                    when add $ do addDeferred [(n, (i, top, t, psns, toplvl, definable))]
                                  addIBC (IBCDef n)
                    ns' <- checkAddDef add toplvl info fc mkerr definable ns
                    return ((n, (i, top, t', psns)) : ns')

-- | Get the list of (index, name) of inaccessible arguments from an elaborated
-- type
inaccessibleImps :: Int -> Type -> [Bool] -> [(Int, Name)]
inaccessibleImps i (Bind n (Pi _ t _) sc) (inacc : ins)
    | inacc = (i, n) : inaccessibleImps (i + 1) sc ins
    | otherwise = inaccessibleImps (i + 1) sc ins
inaccessibleImps _ _ _ = []

-- | Get the list of (index, name) of inaccessible arguments from the type.
inaccessibleArgs :: Int -> PTerm -> [(Int, Name)]
inaccessibleArgs i (PPi plicity n _ ty t)
    | InaccessibleArg `elem` pargopts plicity
        = (i,n) : inaccessibleArgs (i+1) t  -- an .{erased : Implicit}
    | otherwise
        = inaccessibleArgs (i+1) t      -- a {regular : Implicit}
inaccessibleArgs _ _ = []

elabCaseBlock :: ElabInfo -> FnOpts -> PDecl -> Idris ()
elabCaseBlock info opts d@(PClauses f o n ps)
        = do addIBC (IBCDef n)
             logElab 5 $ "CASE BLOCK: " ++ show (n, d)
             let opts' = nub (o ++ opts)
             -- propagate totality assertion to the new definitions
             let opts' = filter propagatable opts
             setFlags n opts'
             rec_elabDecl info EAll info (PClauses f opts' n ps )
  where
    propagatable AssertTotal = True
    propagatable Inlinable = True
    propagatable _ = False

-- | Check that the result of type checking matches what the programmer wrote
-- (i.e. - if we inferred any arguments that the user provided, make sure
-- they are the same!)
checkInferred :: FC -> PTerm -> PTerm -> Idris ()
checkInferred fc inf user =
     do logElab 6 $ "Checked to\n" ++ showTmImpls inf ++ "\n\nFROM\n\n" ++
                                     showTmImpls user
        logElab 10 $ "Checking match"
        i <- getIState
        tclift $ case matchClause' True i user inf of
            _ -> return ()
--             Left (x, y) -> tfail $ At fc
--                                     (Msg $ "The type-checked term and given term do not match: "
--                                            ++ show x ++ " and " ++ show y)
        logElab 10 $ "Checked match"
--                           ++ "\n" ++ showImp True inf ++ "\n" ++ showImp True user)

-- | Return whether inferred term is different from given term
-- (as above, but return a Bool)
inferredDiff :: FC -> PTerm -> PTerm -> Idris Bool
inferredDiff fc inf user =
     do i <- getIState
        logElab 6 $ "Checked to\n" ++ showTmImpls inf ++ "\n" ++
                                     showTmImpls user
        tclift $ case matchClause' True i user inf of
            Right vs -> return False
            Left (x, y) -> return True

-- | Check a PTerm against documentation and ensure that every documented
-- argument actually exists.  This must be run _after_ implicits have been
-- found, or it will give spurious errors.
checkDocs :: FC -> [(Name, Docstring a)] -> PTerm -> Idris ()
checkDocs fc args tm = cd (Map.fromList args) tm
  where cd as (PPi _ n _ _ sc) = cd (Map.delete n as) sc
        cd as _ | Map.null as = return ()
                | otherwise   = ierror . At fc . Msg $
                                "There is documentation for argument(s) "
                                ++ (concat . intersperse ", " . map show . Map.keys) as
                                ++ " but they were not found."

decorateid decorate (PTy doc argdocs s f o n nfc t) = PTy doc argdocs s f o (decorate n) nfc t
decorateid decorate (PClauses f o n cs)
   = PClauses f o (decorate n) (map dc cs)
    where dc (PClause fc n t as w ds) = PClause fc (decorate n) (dappname t) as w ds
          dc (PWith   fc n t as w pn ds)
                 = PWith fc (decorate n) (dappname t) as w pn
                            (map (decorateid decorate) ds)
          dappname (PApp fc (PRef fc' hl n) as) = PApp fc (PRef fc' hl (decorate n)) as
          dappname t = t


-- if 't' is an interface application, assume its arguments are injective
pbinds :: IState -> Term -> ElabD ()
pbinds i (Bind n (PVar t) sc)
    = do attack; patbind n
         env <- get_env
         case unApply (normalise (tt_ctxt i) env t) of
              (P _ c _, args) -> case lookupCtxt c (idris_interfaces i) of
                                   [] -> return ()
                                   _ -> -- interface, set as injective
                                        mapM_ setinjArg args
              _ -> return ()
         pbinds i sc
  where setinjArg (P _ n _) = setinj n
        setinjArg _ = return ()
pbinds i tm = return ()

pbty (Bind n (PVar t) sc) tm = Bind n (PVTy t) (pbty sc tm)
pbty _ tm = tm

getPBtys (Bind n (PVar t) sc) = (n, t) : getPBtys sc
getPBtys (Bind n (PVTy t) sc) = (n, t) : getPBtys sc
getPBtys _ = []

psolve (Bind n (PVar t) sc) = do solve; psolve sc
psolve tm = return ()

pvars ist (Bind n (PVar t) sc) = (n, delab ist t) : pvars ist sc
pvars ist _ = []

getFixedInType i env (PExp _ _ _ _ : is) (Bind n (Pi _ t _) sc)
    = nub $ getFixedInType i env [] t ++
            getFixedInType i (n : env) is (instantiate (P Bound n t) sc)
            ++ case unApply t of
                    (P _ n _, _) -> if n `elem` env then [n] else []
                    _ -> []
getFixedInType i env (_ : is) (Bind n (Pi _ t _) sc)
    = getFixedInType i (n : env) is (instantiate (P Bound n t) sc)
getFixedInType i env is tm@(App _ f a)
    | (P _ tn _, args) <- unApply tm
       = case lookupCtxtExact tn (idris_datatypes i) of
            Just t -> nub $ paramNames args env (param_pos t) ++
                            getFixedInType i env is f ++
                            getFixedInType i env is a
            Nothing -> nub $ getFixedInType i env is f ++
                             getFixedInType i env is a
    | otherwise = nub $ getFixedInType i env is f ++
                        getFixedInType i env is a
getFixedInType i _ _ _ = []

getFlexInType i env ps (Bind n (Pi _ t _) sc)
    = nub $ (if (not (n `elem` ps)) then getFlexInType i env ps t else []) ++
            getFlexInType i (n : env) ps (instantiate (P Bound n t) sc)

getFlexInType i env ps tm@(App _ f a)
    | (P nt tn _, args) <- unApply tm, nt /= Bound
       = case lookupCtxtExact tn (idris_datatypes i) of
            Just t -> nub $ paramNames args env [x | x <- [0..length args],
                                                     not (x `elem` param_pos t)]
                          ++ getFlexInType i env ps f ++
                             getFlexInType i env ps a
            Nothing -> let ppos = case lookupCtxtExact tn (idris_fninfo i) of
                                       Just fi -> fn_params fi
                                       Nothing -> []
                       in nub $ paramNames args env [x | x <- [0..length args],
                                                         not (x `elem` ppos)]
                           ++ getFlexInType i env ps f ++
                              getFlexInType i env ps a
    | otherwise = nub $ getFlexInType i env ps f ++
                        getFlexInType i env ps a
getFlexInType i _ _ _ = []

-- | Treat a name as a parameter if it appears in parameter positions in
-- types, and never in a non-parameter position in a (non-param) argument type.
getParamsInType :: IState -> [Name] -> [PArg] -> Type -> [Name]
getParamsInType i env ps t = let fix = getFixedInType i env ps t
                                 flex = getFlexInType i env fix t in
                                 [x | x <- fix, not (x `elem` flex)]

getTCinj i (Bind n (Pi _ t _) sc)
    = getTCinj i t ++ getTCinj i (instantiate (P Bound n t) sc)
getTCinj i ap@(App _ f a)
    | (P _ n _, args) <- unApply ap,
      isTCName n = mapMaybe getInjName args
    | otherwise = []
  where
    isTCName n = case lookupCtxtExact n (idris_interfaces i) of
                      Just _ -> True
                      _ -> False
    getInjName t | (P _ x _, _) <- unApply t = Just x
                 | otherwise = Nothing
getTCinj _ _ = []

getTCParamsInType :: IState -> [Name] -> [PArg] -> Type -> [Name]
getTCParamsInType i env ps t = let params = getParamsInType i env ps t
                                   tcs = nub $ getTCinj i t in
                                   filter (flip  elem tcs) params
paramNames args env [] = []
paramNames args env (p : ps)
   | length args > p = case args!!p of
                          P _ n _ -> if n `elem` env
                                        then n : paramNames args env ps
                                        else paramNames args env ps
                          _ -> paramNames args env ps
   | otherwise = paramNames args env ps

getUniqueUsed :: Context -> Term -> [Name]
getUniqueUsed ctxt tm = execState (getUniq [] [] tm) []
  where
    getUniq :: Env -> [(Name, Bool)] -> Term -> State [Name] ()
    getUniq env us (Bind n b sc)
       = let uniq = case check ctxt env (forgetEnv (map fst env) (binderTy b)) of
                         OK (_, UType UniqueType) -> True
                         OK (_, UType NullType) -> True
                         OK (_, UType AllTypes) -> True
                         _ -> False in
             do getUniqB env us b
                getUniq ((n,b):env) ((n, uniq):us) sc
    getUniq env us (App _ f a) = do getUniq env us f; getUniq env us a
    getUniq env us (V i)
       | i < length us = if snd (us!!i) then use (fst (us!!i)) else return ()
    getUniq env us (P _ n _)
       | Just u <- lookup n us = if u then use n else return ()
    getUniq env us _ = return ()

    use n = do ns <- get; put (n : ns)

    getUniqB env us (Let t v) = getUniq env us v
    getUniqB env us (Guess t v) = getUniq env us v
--     getUniqB env us (Pi t v) = do getUniq env us t; getUniq env us v
    getUniqB env us (NLet t v) = getUniq env us v
    getUniqB env us b = return () -- getUniq env us (binderTy b)

-- In a functional application, return the names which are used
-- directly in a static position
getStaticNames :: IState -> Term -> [Name]
getStaticNames ist (Bind n (PVar _) sc)
    = getStaticNames ist (instantiate (P Bound n Erased) sc)
getStaticNames ist tm
    | (P _ fn _, args) <- unApply tm
        = case lookupCtxtExact fn (idris_statics ist) of
               Just stpos -> getStatics args stpos
               _ -> []
  where
    getStatics (P _ n _ : as) (True : ss) = n : getStatics as ss
    getStatics (_ : as) (_ : ss) = getStatics as ss
    getStatics _ _ = []
getStaticNames _ _ = []

getStatics :: [Name] -> Term -> [Bool]
getStatics ns (Bind n (Pi _ _ _) t)
    | n `elem` ns = True : getStatics ns t
    | otherwise = False : getStatics ns t
getStatics _ _ = []

mkStatic :: [Name] -> PDecl -> PDecl
mkStatic ns (PTy doc argdocs syn fc o n nfc ty)
    = PTy doc argdocs syn fc o n nfc (mkStaticTy ns ty)
mkStatic ns t = t

mkStaticTy :: [Name] -> PTerm -> PTerm
mkStaticTy ns (PPi p n fc ty sc)
    | n `elem` ns = PPi (p { pstatic = Static }) n fc ty (mkStaticTy ns sc)
    | otherwise = PPi p n fc ty (mkStaticTy ns sc)
mkStaticTy ns t = t

-- Check that a name has the minimum required accessibility
checkVisibility :: FC -> Name -> Accessibility -> Accessibility -> Name -> Idris ()
checkVisibility fc n minAcc acc ref
    = do nvis <- getFromHideList ref
         case nvis of
              Nothing -> return ()
              Just acc' -> if acc' > minAcc
                              then tclift $ tfail (At fc
                                      (Msg $ show acc ++ " " ++ show n ++
                                             " can't refer to " ++
                                             show acc' ++ " " ++ show ref))
                              else return ()


-- | Find the type constructor arguments that are parameters, given a
-- list of constructor types.
--
-- Parameters are names which are unchanged across the structure.
-- They appear at least once in every constructor type, always appear
-- in the same argument position(s), and nothing else ever appears in those
-- argument positions.
findParams :: Name   -- ^ the name of the family that we are finding parameters for
           -> Type   -- ^ the type of the type constructor (normalised already)
           -> [Type] -- ^ the declared constructor types
           -> [Int]
findParams tyn famty ts =
    let allapps = map getDataApp ts
        -- do each constructor separately, then merge the results (names
        -- may change between constructors)
        conParams = map paramPos allapps
    in inAll conParams

  where
    inAll :: [[Int]] -> [Int]
    inAll [] = []
    inAll (x : xs) = filter (\p -> all (\ps -> p `elem` ps) xs) x

    paramPos [] = []
    paramPos (args : rest)
          = dropNothing $ keepSame (zip [0..] args) rest

    dropNothing [] = []
    dropNothing ((x, Nothing) : ts) = dropNothing ts
    dropNothing ((x, _) : ts) = x : dropNothing ts

    keepSame :: [(Int, Maybe Name)] -> [[Maybe Name]] ->
                [(Int, Maybe Name)]
    keepSame as [] = as
    keepSame as (args : rest) = keepSame (update as args) rest
      where
        update [] _ = []
        update _ [] = []
        update ((n, Just x) : as) (Just x' : args)
            | x == x' = (n, Just x) : update as args
        update ((n, _) : as) (_ : args) = (n, Nothing) : update as args

    getDataApp :: Type -> [[Maybe Name]]
    getDataApp f@(App _ _ _)
        | (P _ d _, args) <- unApply f
               = if (d == tyn) then [mParam args args] else []
    getDataApp (Bind n (Pi _ t _) sc)
        = getDataApp t ++ getDataApp (instantiate (P Bound n t) sc)
    getDataApp _ = []

    -- keep the arguments which are single names, which appear
    -- in the return type, counting only the first time they appear in
    -- the return type as the parameter position
    mParam args [] = []
    mParam args (P Bound n _ : rest)
           | paramIn False n args = Just n : mParam (filter (noN n) args) rest
        where paramIn ok n [] = ok
              paramIn ok n (P _ t _ : ts)
                   = paramIn (ok || n == t) n ts
              paramIn ok n (t : ts)
                   | n `elem` freeNames t = False -- not a single name
                   | otherwise = paramIn ok n ts

              -- If the name appears again later, don't count that appearance
              -- as a parameter position
              noN n (P _ t _) = n /= t
              noN n _ = False
    mParam args (_ : rest) = Nothing : mParam args rest

-- | Mark a name as detaggable in the global state (should be called
-- for type and constructor names of single-constructor datatypes)
setDetaggable :: Name -> Idris ()
setDetaggable n = do
    ist <- getIState
    let opt = idris_optimisation ist
    case lookupCtxt n opt of
        [oi] -> putIState ist { idris_optimisation = addDef n oi { detaggable = True } opt }
        _    -> putIState ist { idris_optimisation = addDef n (Optimise [] True) opt }

displayWarnings :: EState -> Idris ()
displayWarnings est
     = mapM_ displayImpWarning (implicit_warnings est)
  where
    displayImpWarning :: (FC, Name) -> Idris ()
    displayImpWarning (fc, n) =
       iputStrLn $ show fc ++ ":WARNING: " ++ show (nsroot n) ++ " is bound as an implicit\n"
                   ++ "\tDid you mean to refer to " ++ show n ++ "?"

propagateParams :: IState -> [Name] -> Type -> [Name] -> PTerm -> PTerm
propagateParams i ps t bound tm@(PApp _ (PRef fc hls n) args)
     = PApp fc (PRef fc hls n) (addP t args)
   where addP (Bind n _ sc) (t : ts)
              | Placeholder <- getTm t,
                n `elem` ps,
                not (n `elem` bound)
                    = t { getTm = PPatvar NoFC n } : addP sc ts
         addP (Bind n _ sc) (t : ts) = t : addP sc ts
         addP _ ts = ts
propagateParams i ps t bound (PApp fc ap args)
     = PApp fc (propagateParams i ps t bound ap) args
propagateParams i ps t bound (PRef fc hls n)
     = case lookupCtxt n (idris_implicits i) of
            [is] -> let ps' = filter (isImplicit is) ps in
                        PApp fc (PRef fc hls n) (map (\x -> pimp x (PRef fc [] x) True) ps')
            _ -> PRef fc hls n
    where isImplicit [] n = False
          isImplicit (PImp _ _ _ x _ : is) n | x == n = True
          isImplicit (_ : is) n = isImplicit is n
propagateParams i ps t bound x = x

-- | Gather up all the outer 'PVar's and 'Hole's in an expression and reintroduce
-- them in a canonical order
orderPats :: Term -> Term
orderPats tm = op [] tm
  where
    op [] (App s f a) = App s f (op [] a) -- for Infer terms

    op ps (Bind n (PVar t) sc) = op ((n, PVar t) : ps) sc
    op ps (Bind n (Hole t) sc) = op ((n, Hole t) : ps) sc
    op ps (Bind n (Pi i t k) sc) = op ((n, Pi i t k) : ps) sc
    op ps sc = bindAll (sortP ps) sc

    -- Keep explicit Pi in the same order, insert others as necessary,
    -- Pi as early as possible, Hole as late as possible
    sortP ps = let (exps, imps) = partition isExp ps in
               pick (reverse exps) imps

    isExp (_, Pi Nothing _ _) = True
    isExp (_, Pi (Just i) _ _) = toplevel_imp i && not (machine_gen i)
    isExp _ = False

    pick acc [] = acc
    pick acc ((n, t) : ps) = pick (insert n t acc) ps

    insert n t [] = [(n, t)]
    -- if 't' uses any of the names which appear later, insert it later
    insert n t rest@((n', t') : ps)
        | any (\x -> x `elem` refsIn (binderTy t)) (n' : map fst ps)
              = (n', t') : insert n t ps
        -- otherwise it's fine where it is (preserve ordering)
        | otherwise = (n, t) : rest

-- Make sure all the pattern bindings are as far out as possible
liftPats :: Term -> Term
liftPats tm = let (tm', ps) = runState (getPats tm) [] in
                  orderPats $ bindPats (reverse ps) tm'
  where
    bindPats []          tm = tm
    bindPats ((n, t):ps) tm
         | n `notElem` map fst ps = Bind n (PVar t) (bindPats ps tm)
         | otherwise = bindPats ps tm

    getPats :: Term -> State [(Name, Type)] Term
    getPats (Bind n (PVar t) sc) = do ps <- get
                                      put ((n, t) : ps)
                                      getPats sc
    getPats (Bind n (Guess t v) sc) = do t' <- getPats t
                                         v' <- getPats v
                                         sc' <- getPats sc
                                         return (Bind n (Guess t' v') sc')
    getPats (Bind n (Let t v) sc) = do t' <- getPats t
                                       v' <- getPats v
                                       sc' <- getPats sc
                                       return (Bind n (Let t' v') sc')
    getPats (Bind n (Pi i t k) sc) = do t' <- getPats t
                                        k' <- getPats k
                                        sc' <- getPats sc
                                        return (Bind n (Pi i t' k') sc')
    getPats (Bind n (Lam t) sc) = do t' <- getPats t
                                     sc' <- getPats sc
                                     return (Bind n (Lam t') sc')
    getPats (Bind n (Hole t) sc) = do t' <- getPats t
                                      sc' <- getPats sc
                                      return (Bind n (Hole t') sc')


    getPats (App s f a) = do f' <- getPats f
                             a' <- getPats a
                             return (App s f' a')
    getPats t = return t



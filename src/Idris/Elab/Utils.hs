{-# LANGUAGE PatternGuards #-}
module Idris.Elab.Utils where

import Idris.AbsSyntax
import Idris.Error
import Idris.DeepSeq
import Idris.Delaborate
import Idris.Docstrings

import Idris.Core.TT
import Idris.Core.Elaborate hiding (Tactic(..))
import Idris.Core.Evaluate
import Idris.Core.Typecheck

import Control.Applicative hiding (Const)
import Control.Monad.State
import Control.Monad
import Data.List
import qualified Data.Traversable as Traversable

import Debug.Trace

import qualified Data.Map as Map

recheckC = recheckC_borrowing False []

recheckC_borrowing uniq_check bs fc mkerr env t
    = do -- t' <- applyOpts (forget t) (doesn't work, or speed things up...)
         ctxt <- getContext
         t' <- case safeForget t of
                    Just ft -> return ft
                    Nothing -> tclift $ tfail $ mkerr (At fc (IncompleteTerm t))
         (tm, ty, cs) <- tclift $ case recheck_borrowing uniq_check bs ctxt env t' t of
                                   Error e -> tfail (At fc (mkerr e))
                                   OK x -> return x
         logLvl 6 $ "CONSTRAINTS ADDED: " ++ show cs
         addConstraints fc cs
         return (tm, ty)

iderr :: Name -> Err -> Err
iderr _ e = e

checkDef :: FC -> (Name -> Err -> Err) -> [(Name, (Int, Maybe Name, Type))]
         -> Idris [(Name, (Int, Maybe Name, Type))]
checkDef fc mkerr ns = checkAddDef False True fc mkerr ns

checkAddDef :: Bool -> Bool -> FC -> (Name -> Err -> Err)
            -> [(Name, (Int, Maybe Name, Type))]
            -> Idris [(Name, (Int, Maybe Name, Type))]
checkAddDef add toplvl fc mkerr [] = return []
checkAddDef add toplvl fc mkerr ((n, (i, top, t)) : ns) 
               = do ctxt <- getContext
                    (t', _) <- recheckC fc (mkerr n) [] t
                    when add $ do addDeferred [(n, (i, top, t, toplvl))]
                                  addIBC (IBCDef n)
                    ns' <- checkAddDef add toplvl fc mkerr ns
                    return ((n, (i, top, t')) : ns')

-- | Get the list of (index, name) of inaccessible arguments from an elaborated
-- type
inaccessibleImps :: Int -> Type -> [Bool] -> [(Int, Name)]
inaccessibleImps i (Bind n (Pi _ t _) sc) (inacc : ins)
    | inacc = (i, n) : inaccessibleImps (i + 1) sc ins
    | otherwise = inaccessibleImps (i + 1) sc ins
inaccessibleImps _ _ _ = []

-- | Get the list of (index, name) of inaccessible arguments from the type.
inaccessibleArgs :: Int -> PTerm -> [(Int, Name)]
inaccessibleArgs i (PPi (Imp _ _ _ _) n _ Placeholder t)
        = (i,n) : inaccessibleArgs (i+1) t  -- unbound implicit
inaccessibleArgs i (PPi plicity n _ ty t)
    | InaccessibleArg `elem` pargopts plicity
        = (i,n) : inaccessibleArgs (i+1) t  -- an .{erased : Implicit}
    | otherwise
        = inaccessibleArgs (i+1) t      -- a {regular : Implicit}
inaccessibleArgs _ _ = []

elabCaseBlock :: ElabInfo -> FnOpts -> PDecl -> Idris ()
elabCaseBlock info opts d@(PClauses f o n ps)
        = do addIBC (IBCDef n)
             logLvl 5 $ "CASE BLOCK: " ++ show (n, d)
             let opts' = nub (o ++ opts)
             -- propagate totality assertion to the new definitions
             when (AssertTotal `elem` opts) $ setFlags n [AssertTotal]
             rec_elabDecl info EAll info (PClauses f opts' n ps )

-- | Check that the result of type checking matches what the programmer wrote
-- (i.e. - if we inferred any arguments that the user provided, make sure
-- they are the same!)
checkInferred :: FC -> PTerm -> PTerm -> Idris ()
checkInferred fc inf user =
     do logLvl 6 $ "Checked to\n" ++ showTmImpls inf ++ "\n\nFROM\n\n" ++
                                     showTmImpls user
        logLvl 10 $ "Checking match"
        i <- getIState
        tclift $ case matchClause' True i user inf of
            _ -> return ()
--             Left (x, y) -> tfail $ At fc
--                                     (Msg $ "The type-checked term and given term do not match: "
--                                            ++ show x ++ " and " ++ show y)
        logLvl 10 $ "Checked match"
--                           ++ "\n" ++ showImp True inf ++ "\n" ++ showImp True user)

-- | Return whether inferred term is different from given term
-- (as above, but return a Bool)
inferredDiff :: FC -> PTerm -> PTerm -> Idris Bool
inferredDiff fc inf user =
     do i <- getIState
        logLvl 6 $ "Checked to\n" ++ showTmImpls inf ++ "\n" ++
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

decorateid decorate (PTy doc argdocs s f o n t) = PTy doc argdocs s f o (decorate n) t
decorateid decorate (PClauses f o n cs)
   = PClauses f o (decorate n) (map dc cs)
    where dc (PClause fc n t as w ds) = PClause fc (decorate n) (dappname t) as w ds
          dc (PWith   fc n t as w pn ds)
                 = PWith fc (decorate n) (dappname t) as w pn
                            (map (decorateid decorate) ds)
          dappname (PApp fc (PRef fc' n) as) = PApp fc (PRef fc' (decorate n)) as
          dappname t = t


-- if 't' is a type class application, assume its arguments are injective
pbinds :: IState -> Term -> ElabD ()
pbinds i (Bind n (PVar t) sc) 
    = do attack; patbind n
         case unApply t of
              (P _ c _, args) -> case lookupCtxt c (idris_classes i) of
                                   [] -> return ()
                                   _ -> -- type class, set as injective
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
            ++ case t of
                    P _ n _ -> if n `elem` env then [n] else []
                    _ -> []
getFixedInType i env (_ : is) (Bind n (Pi _ t _) sc)
    = getFixedInType i (n : env) is (instantiate (P Bound n t) sc)
getFixedInType i env is tm@(App _ f a)
    | (P _ tn _, args) <- unApply tm
       = case lookupCtxt tn (idris_datatypes i) of
            [t] -> nub $ paramNames args env (param_pos t) ++
                         getFixedInType i env is f ++
                         getFixedInType i env is a
            [] -> nub $ getFixedInType i env is f ++
                        getFixedInType i env is a
    | otherwise = nub $ getFixedInType i env is f ++
                        getFixedInType i env is a
getFixedInType i _ _ _ = []

getFlexInType i env ps (Bind n (Pi _ t _) sc)
    = nub $ (if (not (n `elem` ps)) then getFlexInType i env ps t else []) ++
            getFlexInType i (n : env) ps (instantiate (P Bound n t) sc)

getFlexInType i env ps tm@(App _ f a)
    | (P nt tn _, args) <- unApply tm, nt /= Bound
       = case lookupCtxt tn (idris_datatypes i) of
            [t] -> nub $ paramNames args env [x | x <- [0..length args],
                                                  not (x `elem` param_pos t)] 
                          ++ getFlexInType i env ps f ++
                             getFlexInType i env ps a
            [] -> let ppos = case lookupCtxtName tn (idris_fninfo i) of
                                  [fi] -> fn_params (snd fi)
                                  [] -> []
                                  xs -> error ("Too much function info: " ++ show xs)
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
mkStatic ns (PTy doc argdocs syn fc o n ty) 
    = PTy doc argdocs syn fc o n (mkStaticTy ns ty)
mkStatic ns t = t

mkStaticTy :: [Name] -> PTerm -> PTerm
mkStaticTy ns (PPi p n fc ty sc) 
    | n `elem` ns = PPi (p { pstatic = Static }) n fc ty (mkStaticTy ns sc)
    | otherwise = PPi p n fc ty (mkStaticTy ns sc)
mkStaticTy ns t = t




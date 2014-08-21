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
import Control.Monad
import Data.List

import Debug.Trace

import qualified Data.Map as Map

recheckC = recheckC_borrowing [] 

recheckC_borrowing bs fc env t
    = do -- t' <- applyOpts (forget t) (doesn't work, or speed things up...)
         ctxt <- getContext
         (tm, ty, cs) <- tclift $ case recheck_borrowing bs ctxt env (forget t) t of
                                   Error e -> tfail (At fc e)
                                   OK x -> return x
         addConstraints fc cs
         return (tm, ty)


checkDef fc ns = checkAddDef False True fc ns

checkAddDef add toplvl fc [] = return []
checkAddDef add toplvl fc ((n, (i, top, t)) : ns) 
               = do ctxt <- getContext
                    (t', _) <- recheckC fc [] t
                    when add $ do addDeferred [(n, (i, top, t, toplvl))]
                                  addIBC (IBCDef n)
                    ns' <- checkAddDef add toplvl fc ns
                    return ((n, (i, top, t')) : ns')

-- Get the list of (index, name) of inaccessible arguments from an elaborated
-- type
inaccessibleImps :: Int -> Type -> [Bool] -> [(Int, Name)]
inaccessibleImps i (Bind n (Pi t) sc) (inacc : ins)
    | inacc = (i, n) : inaccessibleImps (i + 1) sc ins
    | otherwise = inaccessibleImps (i + 1) sc ins
inaccessibleImps _ _ _ = []

-- Get the list of (index, name) of inaccessible arguments from the type.
inaccessibleArgs :: Int -> PTerm -> [(Int, Name)]
inaccessibleArgs i (PPi (Imp _ _ _) n Placeholder t)
        = (i,n) : inaccessibleArgs (i+1) t  -- unbound implicit
inaccessibleArgs i (PPi plicity n ty t)
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

-- Check that the result of type checking matches what the programmer wrote
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

-- Return whether inferred term is different from given term
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
checkDocs :: FC -> [(Name, Docstring)] -> PTerm -> Idris ()
checkDocs fc args tm = cd (Map.fromList args) tm
  where cd as (PPi _ n _ sc) = cd (Map.delete n as) sc
        cd as _ | Map.null as = return ()
                | otherwise   = ierror . At fc . Msg $
                                "There is documentation for argument(s) "
                                ++ (concat . intersperse ", " . map show . Map.keys) as
                                ++ " but they were not found."

decorateid decorate (PTy doc argdocs s f o n t) = PTy doc argdocs s f o (decorate n) t
decorateid decorate (PClauses f o n cs)
   = PClauses f o (decorate n) (map dc cs)
    where dc (PClause fc n t as w ds) = PClause fc (decorate n) (dappname t) as w ds
          dc (PWith   fc n t as w ds)
                 = PWith fc (decorate n) (dappname t) as w
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

getFixedInType i env (PExp _ _ _ _ : is) (Bind n (Pi t) sc)
    = nub $ getFixedInType i env [] t ++
            getFixedInType i (n : env) is (instantiate (P Bound n t) sc)
getFixedInType i env (_ : is) (Bind n (Pi t) sc)
    = getFixedInType i (n : env) is (instantiate (P Bound n t) sc)
getFixedInType i env is tm@(App f a)
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

getFlexInType i env ps (Bind n (Pi t) sc)
    = nub $ (if (not (n `elem` ps)) then getFlexInType i env ps t else []) ++
            getFlexInType i (n : env) ps (instantiate (P Bound n t) sc)
getFlexInType i env ps tm@(App f a)
    | (P _ tn _, args) <- unApply tm
       = case lookupCtxt tn (idris_datatypes i) of
            [t] -> nub $ paramNames args env [x | x <- [0..length args],
                                                  not (x `elem` param_pos t)] 
                          ++ getFlexInType i env ps f ++
                             getFlexInType i env ps a
            [] -> let ppos = case lookupCtxt tn (idris_fninfo i) of
                                  [fi] -> fn_params fi 
                                  [] -> [] in
                      nub $ paramNames args env [x | x <- [0..length args],
                                                     not (x `elem` ppos)] 
                            ++ getFlexInType i env ps f ++
                               getFlexInType i env ps a
    | otherwise = nub $ getFlexInType i env ps f ++
                        getFlexInType i env ps a
getFlexInType i _ _ _ = []

-- Treat a name as a parameter if it appears in parameter positions in
-- types, and never in a non-parameter position in a (non-param) argument type.

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

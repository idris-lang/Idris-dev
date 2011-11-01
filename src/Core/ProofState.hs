{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, PatternGuards #-}

{- Implements a proof state, some primitive tactics for manipulating
   proofs, and some high level commands for introducing new theorems,
   evaluation/checking inside the proof system, etc. --}

module Core.ProofState(ProofState(..), newProof, envAtFocus, goalAtFocus,
                  Tactic(..), Goal(..), processTactic) where

import Core.Typecheck
import Core.Evaluate
import Core.TT
import Core.Unify

import Control.Monad.State
import Control.Applicative
import Data.List
import Debug.Trace

data ProofState = PS { thname   :: Name,
                       holes    :: [Name], -- holes still to be solved
                       nextname :: Int,    -- name supply
                       pterm    :: Term,   -- current proof term
                       ptype    :: Type,   -- original goal
                       unified  :: (Name, [(Name, Term)]),
                       deferred :: [Name], -- names we'll need to define
                       previous :: Maybe ProofState, -- for undo
                       context  :: Context,
                       plog     :: String,
                       done     :: Bool
                     }
                   
data Goal = GD { premises :: Env,
                 goalType :: Binder Term
               }

data Tactic = Attack
            | Claim Name Raw
            | Exact Raw
            | Fill Raw
            | PrepFill Name [Name]
            | CompleteFill
            | Regret
            | Solve
            | StartUnify Name
            | EndUnify
            | Compute
            | EvalIn Raw
            | CheckIn Raw
            | Intro (Maybe Name)
            | Forall Name Raw
            | LetBind Name Raw Raw
            | Rewrite Raw
            | PatVar Name
            | PatBind Name
            | Focus Name
            | Defer Name
            | MoveLast Name
            | ProofState
            | Undo
            | QED
    deriving Show

-- Some utilites on proof and tactic states

instance Show ProofState where
    show (PS nm [] _ tm _ _ _ _ _ _ _) = show nm ++ ": no more goals"
    show (PS nm (h:hs) _ tm _ _ i _ ctxt _ _) 
          = let OK g = goal (Just h) tm
                wkenv = premises g in
                "Other goals: " ++ show hs ++ "\n" ++
                showPs wkenv (reverse wkenv) ++ "\n" ++
                "-------------------------------- (" ++ show nm ++ 
                ") -------\n  " ++
                show h ++ " : " ++ showG wkenv (goalType g) ++ "\n"
         where showPs env [] = ""
               showPs env ((n, Let t v):bs) 
                   = "  " ++ show n ++ " : " ++ 
                     showEnv env ({- normalise ctxt env -} t) ++ "   =   " ++
                     showEnv env ({- normalise ctxt env -} v) ++
                     "\n" ++ showPs env bs
               showPs env ((n, b):bs) 
                   = "  " ++ show n ++ " : " ++ 
                     showEnv env ({- normalise ctxt env -} (binderTy b)) ++ 
                     "\n" ++ showPs env bs
               showG ps (Guess t v) = showEnv ps ({- normalise ctxt ps -} t) ++ 
                                         " =?= " ++ showEnv ps v
               showG ps b = showEnv ps (binderTy b)

same Nothing n  = True
same (Just x) n = x == n

hole (Hole _)    = True
hole (Guess _ _) = True
hole _           = False

holeName i = MN i "hole" 

getName :: Monad m => String -> StateT TState m Name
getName tag = do ps <- get
                 let n = nextname ps
                 put (ps { nextname = n+1 })
                 return $ MN n tag

action :: Monad m => (ProofState -> ProofState) -> StateT TState m ()
action a = do ps <- get
              put (a ps)

addLog :: Monad m => String -> StateT TState m ()
addLog str = action (\ps -> ps { plog = plog ps ++ str ++ "\n" })

newProof :: Name -> Context -> Type -> ProofState
newProof n ctxt ty = let h = holeName 0 
                         ty' = vToP ty in
                         PS n [h] 1 (Bind h (Hole ty') (P Bound h ty')) ty (h, []) []
                            Nothing ctxt "" False

type TState = ProofState -- [TacticAction])
type RunTactic = Context -> Env -> Term -> StateT TState TC Term
type Hole = Maybe Name -- Nothing = default hole, first in list in proof state

envAtFocus :: ProofState -> TC Env
envAtFocus ps 
    | not $ null (holes ps) = do g <- goal (Just (head (holes ps))) (pterm ps)
                                 return (premises g)
    | otherwise = fail "No holes"

goalAtFocus :: ProofState -> TC (Binder Type)
goalAtFocus ps
    | not $ null (holes ps) = do g <- goal (Just (head (holes ps))) (pterm ps)
                                 return (goalType g)

goal :: Hole -> Term -> TC Goal
goal h tm = g [] tm where
    g env (Bind n b sc) | hole b && same h n = return $ GD env b 
                        | otherwise          
                           = gb env b `mplus` g ((n, b):env) sc
    g env (App f a)   = g env f `mplus` g env a
    g env t           = fail "Can't find hole"

    gb env (Let t v) = g env t `mplus` g env v
    gb env (Guess t v) = g env t `mplus` g env v
    gb env t = g env (binderTy t)

tactic :: Hole -> RunTactic -> StateT TState TC ()
tactic h f = do ps <- get
                tm' <- atH (context ps) [] (pterm ps)
                ps <- get -- might have changed while processing
                put (ps { pterm = tm' })
  where
    atH c env binder@(Bind n b sc) 
        | hole b && same h n = f c env binder
        | otherwise          
            = liftM2 (Bind n) (atHb c env b) (atH c ((n, b) : env) sc) 
    atH c env (App f a)    = liftM2 App (atH c env f) (atH c env a)
    atH c env t            = return t
    
    atHb c env (Let t v)   = liftM2 Let (atH c env t) (atH c env v)    
    atHb c env (Guess t v) = liftM2 Guess (atH c env t) (atH c env v)
    atHb c env t           = do ty' <- atH c env (binderTy t)
                                return $ t { binderTy = ty' }

attack :: RunTactic
attack ctxt env (Bind x (Hole t) sc) 
    = do h <- getName "hole"
         action (\ps -> ps { holes = h : holes ps })
         return $ Bind x (Guess t (newtm h)) sc
  where
    newtm h = Bind h (Hole t) (P Bound h t) 
attack ctxt env _ = fail "Not an attackable hole"

claim :: Name -> Raw -> RunTactic
claim n ty ctxt env t =
    do (tyv, tyt) <- lift $ check ctxt env ty
       lift $ isSet ctxt env tyt
       action (\ps -> let (g:gs) = holes ps in
                          ps { holes = g : n : gs } )
       return $ Bind n (Hole tyv) t -- (weakenTm 1 t)

focus :: Name -> RunTactic
focus n ctxt env t = do action (\ps -> let hs = holes ps in
                                            if n `elem` hs
                                               then ps { holes = n : (hs \\ [n]) }
                                               else ps)
                        return t 

movelast :: Name -> RunTactic
movelast n ctxt env t = do action (\ps -> let hs = holes ps in
                                              if n `elem` hs
                                                  then ps { holes = (hs \\ [n]) ++ [n] }
                                                  else ps)
                           return t 

defer :: Name -> RunTactic
defer n ctxt env (Bind x (Hole t) (P nt x' ty)) | x == x' = 
    do action (\ps -> let hs = holes ps in
                          ps { holes = hs \\ [x] })
       return (Bind n (GHole (mkTy (reverse env) t)) 
                      (mkApp (P Ref n ty) (map getP (reverse env))))
  where
    mkTy []           t = t
    mkTy ((n,b) : bs) t = Bind n (Pi (binderTy b)) (mkTy bs t)

    getP (n, b) = P Bound n (binderTy b)

-- Hmmm. YAGNI?
regret :: RunTactic
regret = undefined

exact :: Raw -> RunTactic
exact guess ctxt env (Bind x (Hole ty) sc) = 
    do (val, valty) <- lift $ check ctxt env guess 
       lift $ converts ctxt env valty ty
       return $ Bind x (Guess ty val) sc
exact _ _ _ _ = fail "Can't fill here."

-- As exact, but attempts to solve other goals by unification

fill :: Raw -> RunTactic
fill guess ctxt env (Bind x (Hole ty) sc) =
    do (val, valty) <- lift $ check ctxt env guess
       ns <- lift $ unify ctxt env valty ty
       ps <- get
       let (uh, uns) = unified ps
       put (ps { unified = (uh, uns ++ ns) })
--        addLog (show (uh, uns ++ ns))
       return $ Bind x (Guess ty val) sc
fill _ _ _ _ = fail "Can't fill here."

prep_fill :: Name -> [Name] -> RunTactic
prep_fill f as ctxt env (Bind x (Hole ty) sc) =
    do let val = mkApp (P Ref f undefined) (map (\n -> P Ref n undefined) as)
       return $ Bind x (Guess ty val) sc
prep_fill f as ctxt env t = fail $ "Can't prepare fill at " ++ show t

complete_fill :: RunTactic
complete_fill ctxt env (Bind x (Guess ty val) sc) =
    do let guess = forget val
       (val', valty) <- lift $ check ctxt env guess    
       ns <- lift $ unify ctxt env valty ty
       ps <- get
       let (uh, uns) = unified ps
       put (ps { unified = (uh, uns ++ ns) })
       return $ Bind x (Guess ty val) sc
complete_fill ctxt env t = fail $ "Can't complete fill at " ++ show t

solve :: RunTactic
solve ctxt env (Bind x (Guess ty val) sc)
   | pureTerm val = do action (\ps -> ps { holes = holes ps \\ [x] })
                       return $ {- Bind x (Let ty val) sc -} instantiate val (pToV x sc)
   | otherwise    = fail "I see a hole in your solution."
solve _ _ h = fail $ "Not a guess " ++ show h

intro :: Maybe Name -> RunTactic
intro mn ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do let n = case mn of 
                  Just name -> name
                  Nothing -> x
       let t' = normalise ctxt env t
       case t' of
           Bind y (Pi s) t -> let t' = instantiate (P Bound n s) (pToV y t) in 
                                  return $ Bind n (Lam s) (Bind x (Hole t') (P Bound x t'))
           _ -> fail "Nothing to introduce"
intro n ctxt env _ = fail "Can't introduce here."

forall :: Name -> Raw -> RunTactic
forall n ty ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do (tyv, tyt) <- lift $ check ctxt env ty
       lift $ isSet ctxt env tyt
       lift $ isSet ctxt env t
       return $ Bind n (Pi tyv) (Bind x (Hole t) (P Bound x t))
forall n ty ctxt env _ = fail "Can't pi bind here"

patvar :: Name -> RunTactic
patvar n ctxt env (Bind x (Hole t) sc) =
    do action (\ps -> ps { holes = holes ps \\ [x] })
       return $ Bind n (PVar t) (instantiate (P Bound n t) (pToV x sc))

letbind :: Name -> Raw -> Raw -> RunTactic
letbind n ty val ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do (tyv,  tyt)  <- lift $ check ctxt env ty
       (valv, valt) <- lift $ check ctxt env val
       lift $ isSet ctxt env tyt
       return $ Bind n (Let tyv valv) (Bind x (Hole t) (P Bound x t))
letbind n ty val ctxt env _ = fail "Can't let bind here"

rewrite :: Raw -> RunTactic
rewrite tm ctxt env (Bind x (Hole t) xp@(P _ x' _)) | x == x' =
    do (tmv, tmt) <- lift $ check ctxt env tm
       case unApply tmt of
         (P _ (UN ["="]) _, [lt,rt,l,r]) ->
            do let p = Bind rname (Lam lt) (mkP (P Bound rname lt) r l t)
               let newt = mkP l r l t 
               let sc = forget $ (Bind x (Hole newt) 
                                       (mkApp (P Ref (UN ["replace"]) (Set 0))
                                              [lt, l, r, p, tmv, xp]))
               (scv, sct) <- lift $ check ctxt env sc
               return scv
         _ -> fail "Not an equality type"
  where
    -- to make the P for rewrite, replace syntactic occurrences of l in ty with
    -- and x, and put \x : lt in front
    mkP lt l r ty | l == ty = lt
    mkP lt l r (App f a) = let f' = if (r /= f) then mkP lt l r f else f
                               a' = if (r /= a) then mkP lt l r a else a in
                               App f' a'
    mkP lt l r x = x

    rname = MN 0 "replaced"
rewrite _ _ _ _ = fail "Can't rewrite here"

patbind :: Name -> RunTactic
patbind n ctxt env (Bind x (Hole t) (P _ x' _)) | x == x' =
    do let t' = normalise ctxt env t
       case t' of
           Bind y (PVTy s) t -> let t' = instantiate (P Bound n s) (pToV y t) in
                                    return $ Bind n (PVar s) (Bind x (Hole t') (P Bound x t'))
           _ -> fail "Nothing to pattern bind"
patbind n ctxt env _ = fail "Can't pattern bind here"

compute :: RunTactic
compute ctxt env (Bind x (Hole ty) sc) =
    do return $ Bind x (Hole (normalise ctxt env ty)) sc
        
check_in :: Raw -> RunTactic
check_in t ctxt env tm = 
    do (val, valty) <- lift $ check ctxt env t
       addLog (showEnv env val ++ " : " ++ showEnv env valty)
       return tm

eval_in :: Raw -> RunTactic
eval_in t ctxt env tm = 
    do (val, valty) <- lift $ check ctxt env t
       let val' = normalise ctxt env val
       let valty' = normalise ctxt env valty
       addLog (showEnv env val ++ " : " ++ 
               showEnv env valty ++ 
--                     " in " ++ show env ++ 
               " ==>\n " ++
               showEnv env val' ++ " : " ++ 
               showEnv env valty')
       return tm

start_unify :: Name -> RunTactic
start_unify n ctxt env tm = do action (\ps -> ps { unified = (n, []) })
                               return tm

solve_unified :: RunTactic
solve_unified ctxt env tm = 
    do ps <- get
       let (_, ns) = unified ps
       action (\ps -> ps { holes = holes ps \\ map fst ns })
--        action (\ps -> ps { pterm = updateSolved ns (pterm ps) })
       return (updateSolved ns tm)
    where
       updateSolved xs (Bind n (Hole ty) t)
           | Just v <- lookup n xs = instantiate v (pToV n (updateSolved xs t))
       updateSolved xs (Bind n b t) 
           | otherwise = Bind n (fmap (updateSolved xs) b) (updateSolved xs t)
       updateSolved xs (App f a) = App (updateSolved xs f) (updateSolved xs a)
       updateSolved xs (P _ n _)
           | Just v <- lookup n xs = v
       updateSolved xs t = t

-- shuffleHoles :: Term -> Term
-- shuffleHoles tm = shuffle [] tm
--   where
--     shuffle ns (Bind n b sc)
--         | 

processTactic :: Tactic -> ProofState -> TC (ProofState, String)
processTactic QED ps = case holes ps of
                           [] -> do let tm = {- normalise (context ps) [] -} (pterm ps)
                                    (tm', ty') <- recheck (context ps) [] tm
                                    return (ps { done = True, pterm = tm' }, 
                                            "Proof complete: " ++ showEnv [] tm')
                           _  -> fail "Still holes to fill."
processTactic ProofState ps = return (ps, showEnv [] (pterm ps))
processTactic Undo ps = case previous ps of
                            Nothing -> fail "Nothing to undo."
                            Just pold -> return (pold, "")
processTactic EndUnify ps = let (h, ns) = unified ps
                                tm' = updateSolved ns (pterm ps) in
                                return (ps { pterm = tm', 
                                             unified = (h, []),
                                             holes = holes ps \\ map fst ns }, "")
    where
       updateSolved xs (Bind n (Hole ty) t)
           | Just v <- lookup n xs = instantiate v (pToV n (updateSolved xs t))
       updateSolved xs (Bind n b t) 
           | otherwise = Bind n (fmap (updateSolved xs) b) (updateSolved xs t)
       updateSolved xs (App f a) = App (updateSolved xs f) (updateSolved xs a)
       updateSolved xs (P _ n _)
           | Just v <- lookup n xs = v
       updateSolved xs t = t
processTactic t ps   
    = case holes ps of
        [] -> fail "Nothing to fill in."
        (h:_)  -> do let n = nextname ps
                     ps' <- execStateT (process t h) ps
                     return (ps' { previous = Just ps, plog = "" }, plog ps')

process :: Tactic -> Name -> StateT TState TC ()
process EndUnify _ 
   = do ps <- get
        let (h, _) = unified ps
        tactic (Just h) solve_unified
process t h = tactic (Just h) (mktac t)
   where mktac Attack        = attack
         mktac (Claim n r)   = claim n r
         mktac (Exact r)     = exact r
         mktac (Fill r)      = fill r
         mktac (PrepFill n ns) = prep_fill n ns
         mktac CompleteFill  = complete_fill
         mktac Regret        = regret
         mktac Solve         = solve
         mktac (StartUnify n) = start_unify n
         mktac Compute       = compute
         mktac (Intro n)     = intro n
         mktac (Forall n t)  = forall n t
         mktac (LetBind n t v) = letbind n t v
         mktac (Rewrite t)   = rewrite t
         mktac (PatVar n)    = patvar n
         mktac (PatBind n)   = patbind n
         mktac (CheckIn r)   = check_in r
         mktac (EvalIn r)    = eval_in r
         mktac (Focus n)     = focus n
         mktac (MoveLast n)  = movelast n
         mktac (Defer n)     = defer n

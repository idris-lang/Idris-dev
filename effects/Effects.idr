module Effects

import Language.Reflection
import Control.Catchable

%access public

---- Effects

Effect : Type
Effect = Type -> Type -> Type -> Type

data EFFECT : Type where
     MkEff : Type -> Effect -> EFFECT

class Handler (e : Effect) (m : Type -> Type) where
     handle : res -> (eff : e res res' t) -> (res' -> t -> m a) -> m a

---- Properties and proof construction

using (xs : List a, ys : List a)
  data SubList : List a -> List a -> Type where
       SubNil : SubList {a} [] []
       Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
       Drop   : SubList xs ys -> SubList xs (x :: ys)

  subListId : SubList xs xs
  subListId {xs = Nil} = SubNil
  subListId {xs = x :: xs} = Keep subListId

data Env  : (m : Type -> Type) -> List EFFECT -> Type where
     Nil  : Env m Nil
     (::) : Handler eff m => a -> Env m xs -> Env m (MkEff a eff :: xs)

data EffElem : (Type -> Type -> Type -> Type) -> Type ->
               List EFFECT -> Type where
     Here : EffElem x a (MkEff a x :: xs)
     There : EffElem x a xs -> EffElem x a (y :: xs)

-- make an environment corresponding to a sub-list
dropEnv : Env m ys -> SubList xs ys -> Env m xs
dropEnv [] SubNil = []
dropEnv (v :: vs) (Keep rest) = v :: dropEnv vs rest
dropEnv (v :: vs) (Drop rest) = dropEnv vs rest

updateWith : (ys' : List a) -> (xs : List a) ->
             SubList ys xs -> List a
updateWith (y :: ys) (x :: xs) (Keep rest) = y :: updateWith ys xs rest
updateWith ys        (x :: xs) (Drop rest) = x :: updateWith ys xs rest
updateWith []        []        SubNil      = []
updateWith (y :: ys) []        SubNil      = y :: ys
updateWith []        (x :: xs) (Keep rest) = []

-- put things back, replacing old with new in the sub-environment
rebuildEnv : Env m ys' -> (prf : SubList ys xs) -> 
             Env m xs -> Env m (updateWith ys' xs prf) 
rebuildEnv []        SubNil      env = env
rebuildEnv (x :: xs) (Keep rest) (y :: env) = x :: rebuildEnv xs rest env
rebuildEnv xs        (Drop rest) (y :: env) = y :: rebuildEnv xs rest env
rebuildEnv (x :: xs) SubNil      [] = x :: xs 

---- The Effect EDSL itself ----

-- some proof automation
findEffElem : Nat -> List (TTName, Binder TT) -> TT -> Tactic -- Nat is maximum search depth
findEffElem Z ctxt goal = Refine "Here" `Seq` Solve
findEffElem (S n) ctxt goal = GoalType "EffElem" 
          (Try (Refine "Here" `Seq` Solve)
               (Refine "There" `Seq` (Solve `Seq` findEffElem n ctxt goal)))

findSubList : Nat -> List (TTName, Binder TT) -> TT -> Tactic
findSubList Z ctxt goal = Refine "SubNil" `Seq` Solve
findSubList (S n) ctxt goal
   = GoalType "SubList" 
         (Try (Refine "subListId" `Seq` Solve)
         ((Try (Refine "Keep" `Seq` Solve)
               (Refine "Drop" `Seq` Solve)) `Seq` findSubList n ctxt goal))

updateResTy : (xs : List EFFECT) -> EffElem e a xs -> e a b t -> 
              List EFFECT
updateResTy {b} (MkEff a e :: xs) Here n = (MkEff b e) :: xs
updateResTy (x :: xs)        (There p) n = x :: updateResTy xs p n

updateResTyImm : (xs : List EFFECT) -> EffElem e a xs -> Type -> 
                 List EFFECT
updateResTyImm (MkEff a e :: xs) Here b = (MkEff b e) :: xs
updateResTyImm (x :: xs)    (There p) b = x :: updateResTyImm xs p b

infix 5 :::, :-, :=

data LRes : lbl -> Type -> Type where
     (:=) : (x : lbl) -> res -> LRes x res

(:::) : lbl -> EFFECT -> EFFECT 
(:::) {lbl} x (MkEff r eff) = MkEff (LRes x r) eff

private
unlabel : {l : ty} -> Env m [l ::: x] -> Env m [x]
unlabel {m} {x = MkEff a eff} [l := v] = [v]

private
relabel : (l : ty) -> Env m [x] -> Env m [l ::: x]
relabel {x = MkEff a eff} l [v] = [l := v]

-- the language of Effects

data EffM : (m : Type -> Type) ->
            List EFFECT -> List EFFECT -> Type -> Type where
     value   : a -> EffM m xs xs a
     ebind   : EffM m xs xs' a -> (a -> EffM m xs' xs'' b) -> EffM m xs xs'' b
     effect  : (prf : EffElem e a xs) -> 
               (eff : e a b t) -> 
               EffM m xs (updateResTy xs prf eff) t
     lift    : (prf : SubList ys xs) ->
               EffM m ys ys' t -> EffM m xs (updateWith ys' xs prf) t
     new     : Handler e m =>
               res -> EffM m (MkEff res e :: xs) (MkEff res' e :: xs') a ->
               EffM m xs xs' a
     test    : (prf : EffElem e (Either l r) xs) ->
               EffM m (updateResTyImm xs prf l) xs' t ->
               EffM m (updateResTyImm xs prf r) xs' t ->
               EffM m xs xs' t
     test_lbl : {x : lbl} ->
                (prf : EffElem e (LRes x (Either l r)) xs) ->
                EffM m (updateResTyImm xs prf (LRes x l)) xs' t ->
                EffM m (updateResTyImm xs prf (LRes x r)) xs' t ->
                EffM m xs xs' t
     catch   : Catchable m err =>
               EffM m xs xs' a -> (err -> EffM m xs xs' a) ->
               EffM m xs xs' a
     (:-)    : (l : ty) -> EffM m [x] [y] t -> EffM m [l ::: x] [l ::: y] t

--   Eff : List (EFFECT m) -> Type -> Type

implicit
lift' : {default tactics { applyTactic findSubList 20; solve; }
           prf : SubList ys xs} ->
        EffM m ys ys' t -> EffM m xs (updateWith ys' xs prf) t
lift' {prf} e = lift prf e

implicit
effect' : {a, b: _} -> {e : Effect} ->
          {default tactics { applyTactic findEffElem 20; solve; } 
             prf : EffElem e a xs} -> 
          (eff : e a b t) -> 
         EffM m xs (updateResTy xs prf eff) t
effect' {prf} e = effect prf e

-- For making proofs implicitly for 'test' and 'test_lbl'

syntax if_valid then [e] else [t] =
     test (tactics { applyTactic findEffElem 20; solve; }) t e
  
syntax if_valid [lbl] then [e] else [t] =
     test_lbl {x=lbl} (tactics { applyTactic findEffElem 20; solve; }) t e
  
syntax if_error then [t] else [e] =
     test (tactics { applyTactic findEffElem 20; solve; }) t e
  
syntax if_error [lbl] then [t] else [e] =
     test_lbl {x=lbl} (tactics { applyTactic findEffElem 20; solve; }) t e

-- These may read better in some contexts

syntax if_right then [e] else [t] =
     test (tactics { applyTactic findEffElem 20; solve; }) t e
  
syntax if_right [lbl] then [e] else [t] =
     test_lbl {x=lbl} (tactics { applyTactic findEffElem 20; solve; }) t e
  
syntax if_left then [t] else [e] =
     test (tactics { applyTactic findEffElem 20; solve; }) t e
  
syntax if_left [lbl] then [t] else [e] =
     test_lbl {x=lbl} (tactics { applyTactic findEffElem 20; solve; }) t e
  

-- for 'do' notation

return : a -> EffM m xs xs a
return x = value x

(>>=) : EffM m xs xs' a -> (a -> EffM m xs' xs'' b) -> EffM m xs xs'' b
(>>=) = ebind

-- for idiom brackets

infixl 2 <$>

pure : a -> EffM m xs xs a
pure = value

(<$>) : EffM m xs xs (a -> b) -> EffM m xs xs a -> EffM m xs xs b
(<$>) prog v = do fn <- prog
                  arg <- v
                  return (fn arg)

-- an interpreter

private
execEff : Env m xs -> (p : EffElem e res xs) -> 
          (eff : e res b a) ->
          (Env m (updateResTy xs p eff) -> a -> m t) -> m t
execEff (val :: env) Here eff' k 
    = handle val eff' (\res, v => k (res :: env) v)
execEff (val :: env) (There p) eff k 
    = execEff env p eff (\env', v => k (val :: env') v)

private
testEff : Env m xs -> (p : EffElem e (Either l r) xs) ->
          (Env m (updateResTyImm xs p l) -> m b) ->
          (Env m (updateResTyImm xs p r) -> m b) ->
          m b
testEff (Left err :: env) Here lk rk = lk (err :: env)
testEff (Right ok :: env) Here lk rk = rk (ok :: env)
testEff (val :: env) (There p) lk rk
   = testEff env p (\envk => lk (val :: envk))
                   (\envk => rk (val :: envk)) 

private
testEffLbl : {x : lbl} ->
             Env m xs -> (p : EffElem e (LRes x (Either l r)) xs) ->
             (Env m (updateResTyImm xs p (LRes x l)) -> m b) ->
             (Env m (updateResTyImm xs p (LRes x r)) -> m b) ->
             m b
testEffLbl ((lbl := Left err) :: env) Here lk rk = lk ((lbl := err) :: env)
testEffLbl ((lbl := Right ok) :: env) Here lk rk = rk ((lbl := ok) :: env)
testEffLbl (val :: env) (There p) lk rk
   = testEffLbl env p (\envk => lk (val :: envk))
                      (\envk => rk (val :: envk)) 

-- Q: Instead of m b, implement as StateT (Env m xs') m b, so that state
-- updates can be propagated even through failing computations?

eff : Env m xs -> EffM m xs xs' a -> (Env m xs' -> a -> m b) -> m b
eff env (value x) k = k env x
eff env (prog `ebind` c) k 
   = eff env prog (\env', p' => eff env' (c p') k)
eff env (effect prf effP) k = execEff env prf effP k
eff env (lift prf effP) k 
   = let env' = dropEnv env prf in 
         eff env' effP (\envk, p' => k (rebuildEnv envk prf env) p')
eff env (new r prog) k
   = let env' = r :: env in 
         eff env' prog (\(v :: envk), p' => k envk p')
eff env (test prf l r) k
   = testEff env prf (\envk => eff envk l k) (\envk => eff envk r k)
eff env (test_lbl prf l r) k
   = testEffLbl env prf (\envk => eff envk l k) (\envk => eff envk r k)
eff env (catch prog handler) k
   = catch (eff env prog k)
           (\e => eff env (handler e) k)
-- FIXME:
-- xs is needed explicitly because otherwise the pattern binding for
-- 'l' appears too late. Solution seems to be to reorder patterns at the
-- end so that everything is in scope when it needs to be.
eff {xs = [l ::: x]} env (l :- prog) k
   = let env' = unlabel env in
         eff env' prog (\envk, p' => k (relabel l envk) p')

run : Applicative m => Env m xs -> EffM m xs xs' a -> m a
run env prog = eff env prog (\env, r => pure r)

runEnv : Applicative m => Env m xs -> EffM m xs xs' a -> m (Env m xs', a)
runEnv env prog = eff env prog (\env, r => pure (env, r))

runPure : Env id xs -> EffM id xs xs' a -> a
runPure env prog = eff env prog (\env, r => r)

runPureEnv : Env id xs -> EffM id xs xs' a -> (Env id xs', a)
runPureEnv env prog = eff env prog (\env, r => (env, r))

runWith : (a -> m a) -> Env m xs -> EffM m xs xs' a -> m a
runWith inj env prog = eff env prog (\env, r => inj r)

Eff : (Type -> Type) -> List EFFECT -> Type -> Type
Eff m xs t = EffM m xs xs t

-- some higher order things

mapE : Applicative m => (a -> Eff m xs b) -> List a -> Eff m xs (List b)
mapE f []        = pure [] 
mapE f (x :: xs) = [| f x :: mapE f xs |]

when : Applicative m => Bool -> Eff m xs () -> Eff m xs ()
when True  e = e
when False e = pure ()

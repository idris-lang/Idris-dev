module Effects

import Language.Reflection
import Control.Catchable
import Effect.Default

%access public

---- Effects

Effect : Type
Effect = (x : Type) -> Type -> (x -> Type) -> Type

%error_reverse
data EFFECT : Type where
     MkEff : Type -> Effect -> EFFECT

class Handler (e : Effect) (m : Type -> Type) where
     handle : res -> (eff : e t res resk) -> 
              ((x : t) -> resk x -> m a) -> m a

-- A bit of syntactic sugar ('syntax' is not very flexible so we only go
-- up to a small number of parameters...)

syntax "{" [inst] "==>" "{" {b} "}" [outst] "}" [eff] 
       = eff inst (\b => outst)
syntax "{" [inst] "==>" [outst] "}" [eff] = eff inst (\result => outst)
syntax "{" [inst] "}" [eff] = eff inst (\result => inst)

---- Properties and proof construction

using (xs : List a, ys : List a)
  data SubList : List a -> List a -> Type where
       SubNil : SubList {a} [] []
       Keep   : SubList xs ys -> SubList (x :: xs) (x :: ys)
       Drop   : SubList xs ys -> SubList xs (x :: ys)

  subListId : SubList xs xs
  subListId {xs = Nil} = SubNil
  subListId {xs = x :: xs} = Keep subListId

namespace Env
  data Env  : (m : Type -> Type) -> List EFFECT -> Type where
       Nil  : Env m Nil
       (::) : Handler eff m => a -> Env m xs -> Env m (MkEff a eff :: xs)
       
data EffElem : Effect -> Type ->
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

%reflection
reflectListEffElem : List a -> Tactic
reflectListEffElem [] = Refine "Here" `Seq` Solve
reflectListEffElem (x :: xs)
     = Try (Refine "Here" `Seq` Solve)
           (Refine "There" `Seq` (Solve `Seq` reflectListEffElem xs))
-- TMP HACK! FIXME!
-- The evaluator needs a 'function case' to know its a reflection function
-- until we propagate that information! Without this, the _ case won't get
-- matched. 
reflectListEffElem (x ++ y) = Refine "Here" `Seq` Solve
reflectListEffElem _ = Refine "Here" `Seq` Solve

%reflection
reflectSubList : List a -> Tactic
reflectSubList [] = Refine "subListId" `Seq` Solve
reflectSubList (x :: xs)
     = Try (Refine "subListId" `Seq` Solve)
           (Try (Refine "Keep" `Seq` (Solve `Seq` reflectSubList xs))
                (Refine "Drop" `Seq` (Solve `Seq` reflectSubList xs)))
reflectSubList (x ++ y) = Refine "subListId" `Seq` Solve
reflectSubList _ = Refine "subListId" `Seq` Solve

%reflection
reflectDefaultList : List a -> Tactic
reflectDefaultList [] = Refine "enil" `Seq` Solve
reflectDefaultList (x :: xs)
     = Refine "econs" `Seq` 
         (Solve `Seq`
           (Instance `Seq` 
         (Refine "default" `Seq`
           (Solve `Seq`
             (Instance `Seq`
              (reflectDefaultList xs))))))
reflectDefaultList (x ++ y) = Refine "Nil" `Seq` Solve
reflectDefaultList _ = Refine "Nil" `Seq` Solve

%reflection
reflectEff : (P : Type) -> Tactic
reflectEff (EffElem m a xs)
     = reflectListEffElem xs `Seq` Solve
reflectEff (SubList xs ys)
     = reflectSubList ys `Seq` Solve
reflectEff (Env m xs)
     = reflectDefaultList xs `Seq` Solve

updateResTy : (val : t) ->
              (xs : List EFFECT) -> EffElem e a xs -> e t a b ->
              List EFFECT
updateResTy {b} val (MkEff a e :: xs) Here n = (MkEff (b val) e) :: xs
updateResTy     val (x :: xs)    (There p) n = x :: updateResTy val xs p n

-- updateResTyImm : (xs : List EFFECT) -> EffElem e a xs -> Type ->
--                  List EFFECT
-- updateResTyImm (MkEff a e :: xs) Here b = (MkEff b e) :: xs
-- updateResTyImm (x :: xs)    (There p) b = x :: updateResTyImm xs p b

infix 5 :::, :-, :=

data LRes : lbl -> Type -> Type where
     (:=) : (x : lbl) -> res -> LRes x res

(:::) : lbl -> EFFECT -> EFFECT
(:::) {lbl} x (MkEff r e) = MkEff (LRes x r) e

using (lbl : Type)
  instance Default a => Default (LRes lbl a) where
    default = lbl := default

private
unlabel : {l : ty} -> Env m [l ::: x] -> Env m [x]
unlabel {m} {x = MkEff a eff} [l := v] = [v]

private
relabel : (l : ty) -> Env m xs -> Env m (map (\x => l ::: x) xs)
relabel {xs = []} l [] = []
relabel {xs = (MkEff a e :: xs)} l (v :: vs) = (l := v) :: relabel l vs

-- the language of Effects

data Eff : (m : Type -> Type) ->
           (x : Type) ->
           List EFFECT -> (x -> List EFFECT) -> Type where
     value   : a -> Eff m a xs (\v => xs)
     ebind   : Eff m a xs xs' -> 
               ((val : a) -> Eff m b (xs' val) xs'') -> Eff m b xs xs''
     effect  : (prf : EffElem e a xs) ->
               (eff : e t a b) ->
               Eff m t xs (\v => updateResTy v xs prf eff)

     lift    : (prf : SubList ys xs) ->
               Eff m t ys ys' -> Eff m t xs (\v => updateWith (ys' v) xs prf)
     new     : Handler e m =>
               res -> 
               Eff m a (MkEff res e :: xs) (\v => (MkEff res' e :: xs')) ->
               Eff m a xs (\v => xs')
     catch   : Catchable m err =>
               Eff m a xs xs' -> (err -> Eff m a xs xs') ->
               Eff m a xs xs'

     (:-)    : (l : ty) -> 
               Eff m t [x] xs' -> -- [x] (\v => xs) -> 
               Eff m t [l ::: x] (\v => map (l :::) (xs' v))

(>>=)   : Eff m a xs xs' -> 
          ((val : a) -> Eff m b (xs' val) xs'') -> Eff m b xs xs''
(>>=) = ebind 

implicit
lift' : Eff m t ys ys' ->
        {default tactics { byReflection reflectEff; }
           prf : SubList ys xs} ->
        Eff m t xs (\v => updateWith (ys' v) xs prf)
lift' e {prf} = lift prf e

implicit
effect' : {a, b: _} -> {e : Effect} ->
          (eff : e t a b) ->
          {default tactics { byReflection reflectEff; }
             prf : EffElem e a xs} ->
         Eff m t xs (\v => updateResTy v xs prf eff)
effect' e {prf} = effect prf e

return : a -> Eff m a xs (\v => xs)
return x = value x

-- for idiom brackets

infixl 2 <$>

pure : a -> Eff m a xs (\v => xs)
pure = value

(<$>) : Eff m (a -> b) xs (\v => xs) -> 
        Eff m a xs (\v => xs) -> Eff m b xs (\v => xs)
(<$>) prog v = do fn <- prog
                  arg <- v
                  return (fn arg)

-- an interpreter

private
execEff : Env m xs -> (p : EffElem e res xs) ->
          (eff : e a res resk) ->
          ((v : a) -> Env m (updateResTy v xs p eff) -> m t) -> m t
execEff (val :: env) Here eff' k
    = handle val eff' (\v, res => k v (res :: env))
execEff (val :: env) (There p) eff k
    = execEff env p eff (\v, env' => k v (val :: env'))

-- Q: Instead of m b, implement as StateT (Env m xs') m b, so that state
-- updates can be propagated even through failing computations?

eff : Env m xs -> Eff m a xs xs' -> ((x : a) -> Env m (xs' x) -> m b) -> m b
eff env (value x) k = k x env
eff env (prog `ebind` c) k
   = eff env prog (\p', env' => eff env' (c p') k)
eff env (effect prf effP) k = execEff env prf effP k
eff env (lift prf effP) k
   = let env' = dropEnv env prf in
         eff env' effP (\p', envk => k p' (rebuildEnv envk prf env))
eff env (new r prog) k
   = let env' = r :: env in
         eff env' prog (\p' => \ (v :: envk) => k p' envk)
eff env (catch prog handler) k
   = catch (eff env prog k)
           (\e => eff env (handler e) k)
-- FIXME:
-- xs is needed explicitly because otherwise the pattern binding for
-- 'l' appears too late. Solution seems to be to reorder patterns at the
-- end so that everything is in scope when it needs to be.
eff {xs = [l ::: x]} env (l :- prog) k
   = let env' = unlabel env in
         eff env' prog (\p', envk => k p' (relabel l envk))

-- yuck :) Haven't got type class instances working nicely in tactic
-- proofs yet, so just brute force it.
syntax MkDefaultEnv = (| [], [default], [default, default],
                         [default, default, default],
                         [default, default, default, default],
                         [default, default, default, default, default],
                         [default, default, default, default, default, default],
                         [default, default, default, default, default, default, default],
                         [default, default, default, default, default, default, default, default] |)

run : Applicative m => {default MkDefaultEnv env : Env m xs} -> Eff m a xs xs' -> m a
run {env} prog = eff env prog (\r, env => pure r)

runPure : {default MkDefaultEnv env : Env id xs} -> Eff id a xs xs' -> a
runPure {env} prog = eff env prog (\r, env => r)

runInit : Applicative m => Env m xs -> Eff m a xs xs' -> m a
runInit env prog = eff env prog (\r, env => pure r)

runPureInit : Env id xs -> Eff id a xs xs' -> a
runPureInit env prog = eff env prog (\r, env => r)

runWith : (a -> m a) -> Env m xs -> Eff m a xs xs' -> m a
runWith inj env prog = eff env prog (\r, env => inj r)

runEnv : Applicative m => Env m xs -> Eff m a xs xs' -> 
         m (x : a ** Env m (xs' x))
runEnv env prog = eff env prog (\r, env => pure (r ** env))

-- some higher order things

mapE : Applicative m => (a -> {xs} Eff m b) -> List a -> {xs} Eff m (List b)
mapE f []        = pure []
mapE f (x :: xs) = [| f x :: mapE f xs |]

when : Applicative m => Bool -> ({xs} Eff m ()) -> {xs} Eff m ()
when True  e = e
when False e = pure ()


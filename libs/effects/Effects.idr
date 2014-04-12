module Effects

import Language.Reflection
import Control.Catchable
import Effect.Default

--- Effectful computations are described as algebraic data types that
--- explain how an effect is interpreted in some underlying context.

%access public
-- ----------------------------------------------------------------- [ Effects ]
||| The Effect type describes effectful computations.
||| 
||| This type is parameterised by:
||| + The input resource.
||| + The return type of the computation.
||| + The computation to run on the resource.
Effect : Type
Effect = (x : Type) -> Type -> (x -> Type) -> Type

||| The `EFFECT` Data type describes how to promote the Effect
||| description into a concrete effect.
%error_reverse
data EFFECT : Type where
     MkEff : Type -> Effect -> EFFECT

||| Handler classes describe how an effect `e` is translated to the
||| underlying computation context `m` for execution.
class Handler (e : Effect) (m : Type -> Type) where
  ||| How to handle the effect.
  ||| 
  ||| @ r The resource being handled.
  ||| @ eff The effect to be applied.
  ||| @ ctxt The context in which to handle the effect.
  handle : (r : res) -> (eff : e t res resk) -> 
           (ctxt : ((x : t) -> resk x -> m a)) -> m a

||| Get the resource type (handy at the REPL to find out about an effect)
resourceType : EFFECT -> Type
resourceType (MkEff t e) = t

-- --------------------------------------------------------- [ Syntactic Sugar ]

-- A bit of syntactic sugar ('syntax' is not very flexible so we only go
-- up to a small number of parameters...)

-- No state transition
syntax "{" [inst] "}" [eff] = eff inst (\result => inst)

-- The state transition is dependent on a result `b`, a bound variable.
syntax "{" [inst] "==>" "{" {b} "}" [outst] "}" [eff] 
       = eff inst (\b => outst)

--- A simple state transition
syntax "{" [inst] "==>" [outst] "}" [eff] = eff inst (\result => outst)

-- --------------------------------------- [ Properties and Proof Construction ]
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

||| make an environment corresponding to a sub-list
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

||| Put things back, replacing old with new in the sub-environment
rebuildEnv : Env m ys' -> (prf : SubList ys xs) ->
             Env m xs -> Env m (updateWith ys' xs prf)
rebuildEnv []        SubNil      env = env
rebuildEnv (x :: xs) SubNil      env = x :: xs
rebuildEnv []        (Keep rest) (y :: env) = []
rebuildEnv (x :: xs) (Keep rest) (y :: env) = x :: rebuildEnv xs rest env
rebuildEnv xs        (Drop rest) (y :: env) = y :: rebuildEnv xs rest env


-- -------------------------------------------------- [ The Effect EDSL itself ]
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

-- ------------------------------------------------- [ The Language of Effects ]
||| Definition of an Effect.
||| 
||| @ m The computation context
||| @ x The return type of the result.
||| @ es The list of allowed side-effects.
||| @ ce Function to compute a new list of allowed side-effects.
data Eff : (m : Type -> Type)
           -> (x : Type)
           -> (es : List EFFECT)
           -> (ce : x -> List EFFECT) -> Type where
     value    : a -> Eff m a xs (\v => xs)
     with_val : (val : a) -> Eff m () xs (\v => xs' val) ->
                Eff m a xs xs'
     ebind    : Eff m a xs xs' -> 
                ((val : a) -> Eff m b (xs' val) xs'') -> Eff m b xs xs''
     effect   : (prf : EffElem e a xs) ->
                (eff : e t a b) ->
                Eff m t xs (\v => updateResTy v xs prf eff)

     lift     : (prf : SubList ys xs) ->
                Eff m t ys ys' -> Eff m t xs (\v => updateWith (ys' v) xs prf)
     newInit  : Handler e m =>
                res -> 
                Eff m a (MkEff res e :: xs) (\v => (MkEff res' e :: xs')) ->
                Eff m a xs (\v => xs')
     catch    : Catchable m err =>
                Eff m a xs xs' -> (err -> Eff m a xs xs') ->
                Eff m a xs xs'

     (:-)     : (l : ty) -> 
                Eff m t [x] xs' -> -- [x] (\v => xs) -> 
                Eff m t [l ::: x] (\v => map (l :::) (xs' v))

(>>=)   : Eff m a xs xs' -> 
          ((val : a) -> Eff m b (xs' val) xs'') -> Eff m b xs xs''
(>>=) = ebind 

return : a -> Eff m a xs (\v => xs)
return x = value x

-- ------------------------------------------------------ [ for idiom brackets ]

infixl 2 <$>

pure : a -> Eff m a xs (\v => xs)
pure = value

syntax pureM [val] = with_val val (pure ())

(<$>) : Eff m (a -> b) xs (\v => xs) -> 
        Eff m a xs (\v => xs) -> Eff m b xs (\v => xs)
(<$>) prog v = do fn <- prog
                  arg <- v
                  return (fn arg)

-- ---------------------------------------------------------- [ an interpreter ]

private
execEff : Env m xs -> (p : EffElem e res xs) ->
          (eff : e a res resk) ->
          ((v : a) -> Env m (updateResTy v xs p eff) -> m t) -> m t
execEff (val :: env) Here eff' k
    = handle val eff' (\v, res => k v (res :: env))
-- FIXME: Teach the elaborator to propagate parameters here
execEff {e} {a} {res} {resk} (val :: env) (There p) eff k
    = execEff {e} {a} {res} {resk} env p eff (\v, env' => k v (val :: env'))

-- Q: Instead of m b, implement as StateT (Env m xs') m b, so that state
-- updates can be propagated even through failing computations?

eff : Env m xs -> Eff m a xs xs' -> ((x : a) -> Env m (xs' x) -> m b) -> m b
eff env (value x) k = k x env
eff env (with_val x prog) k = eff env prog (\p', env' => k x env') 
eff env (prog `ebind` c) k
   = eff env prog (\p', env' => eff env' (c p') k)
eff env (effect prf effP) k = execEff env prf effP k
eff env (lift prf effP) k
   = let env' = dropEnv env prf in
         eff env' effP (\p', envk => k p' (rebuildEnv envk prf env))
eff env (newInit r prog) k
   = eff (r :: env) prog (\p' => \ (v :: envk) => k p' envk)
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
syntax MkDefaultEnv = with Env
                       (| [], [default], [default, default],
                          [default, default, default],
                          [default, default, default, default],
                          [default, default, default, default, default],
                          [default, default, default, default, default, default],
                          [default, default, default, default, default, default, default],
                          [default, default, default, default, default, default, default, default] |)

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

new : Handler e m =>
      {default default r : res} -> 
      Eff m a (MkEff res e :: xs) (\v => (MkEff res' e :: xs')) ->
      Eff m a xs (\v => xs')
new {r} e = newInit r e

-- --------------------------------------------------------- [ Running Effects ]

||| Run an effectful program
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

-- ----------------------------------------------- [ some higher order things ]

mapE : Applicative m => (a -> {xs} Eff m b) -> List a -> {xs} Eff m (List b)
mapE f []        = pure []
mapE f (x :: xs) = [| f x :: mapE f xs |]


mapVE : Applicative m => 
          (a -> {xs} Eff m b) -> 
          Vect n a -> 
          {xs} Eff m (Vect n b)
mapVE f []        = pure []
mapVE f (x :: xs) = [| f x :: mapVE f xs |]


when : Applicative m => Bool -> ({xs} Eff m ()) -> {xs} Eff m ()
when True  e = e
when False e = pure ()

-- --------------------------------------------------------------------- [ EOF ]

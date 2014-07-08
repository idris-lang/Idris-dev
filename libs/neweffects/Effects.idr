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
  ||| @ k The continuation to pass the result of the effect
  covering handle : (r : res) -> (eff : e t res resk) -> 
                    (k : ((x : t) -> resk x -> m a)) -> m a

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
||| Definition of a language of effectful programs.
||| 
||| @ x The return type of the result.
||| @ es The list of allowed side-effects.
||| @ ce Function to compute a new list of allowed side-effects.
data Eff : (x : Type)
           -> (es : List EFFECT)
           -> (ce : x -> List EFFECT) -> Type where
     value    : a -> Eff a xs (\v => xs)
     with_val : (val : a) -> Eff () xs (\v => xs' val) ->
                Eff a xs xs'
     ebind    : Eff a xs xs' -> 
                ((val : a) -> Eff b (xs' val) xs'') -> Eff b xs xs''
     callP    : (prf : EffElem e a xs) ->
                (eff : e t a b) ->
                Eff t xs (\v => updateResTy v xs prf eff)

     liftP    : (prf : SubList ys xs) ->
                Eff t ys ys' -> Eff t xs (\v => updateWith (ys' v) xs prf)

     (:-)     : (l : ty) -> 
                Eff t [x] xs' -> -- [x] (\v => xs) -> 
                Eff t [l ::: x] (\v => map (l :::) (xs' v))

(>>=)   : Eff a xs xs' -> 
          ((val : a) -> Eff b (xs' val) xs'') -> Eff b xs xs''
(>>=) = ebind 

-- namespace SimpleBind
--   (>>=) : Eff m a xs (\v => xs) -> 
--           ((val : a) -> Eff m b xs xs') -> Eff m b xs xs'
--   (>>=) = ebind 

||| Run a subprogram which results in an effect state the same as the input.
staticEff : Eff a xs (\v => xs) -> Eff a xs (\v => xs)
staticEff = id

||| Explicitly give the expected set of result effects for an effectful
||| operation.
toEff : .(xs' : List EFFECT) -> Eff a xs (\v => xs') -> Eff a xs (\v => xs')
toEff xs' = id

return : a -> Eff a xs (\v => xs)
return x = value x

-- ------------------------------------------------------ [ for idiom brackets ]

infixl 2 <$>

pure : a -> Eff a xs (\v => xs)
pure = value

syntax pureM [val] = with_val val (pure ())

(<$>) : Eff (a -> b) xs (\v => xs) -> 
        Eff a xs (\v => xs) -> Eff b xs (\v => xs)
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

eff : Env m xs -> Eff a xs xs' -> ((x : a) -> Env m (xs' x) -> m b) -> m b
eff env (value x) k = k x env
eff env (with_val x prog) k = eff env prog (\p', env' => k x env') 
eff env (prog `ebind` c) k
   = eff env prog (\p', env' => eff env' (c p') k)
eff env (callP prf effP) k = execEff env prf effP k
eff env (liftP prf effP) k
   = let env' = dropEnv env prf in
         eff env' effP (\p', envk => k p' (rebuildEnv envk prf env))
-- FIXME:
-- xs is needed explicitly because otherwise the pattern binding for
-- 'l' appears too late. Solution seems to be to reorder patterns at the
-- end so that everything is in scope when it needs to be.
eff {xs = [l ::: x]} env (l :- prog) k
   = let env' = unlabel env in
         eff env' prog (\p', envk => k p' (relabel l envk))

-- yuck :) Haven't got type class instances working nicely in tactic
-- proofs yet, and 'search' can't be told about any hints yet,
-- so just brute force it.
syntax MkDefaultEnv = with Env
                       (| [], [default], [default, default],
                          [default, default, default],
                          [default, default, default, default],
                          [default, default, default, default, default],
                          [default, default, default, default, default, default],
                          [default, default, default, default, default, default, default],
                          [default, default, default, default, default, default, default, default] |)

call : {a, b: _} -> {e : Effect} ->
       (eff : e t a b) ->
       {default tactics { search 100; }
          prf : EffElem e a xs} ->
      Eff t xs (\v => updateResTy v xs prf eff)
call e {prf} = callP prf e

implicit
lift : Eff t ys ys' ->
       {default tactics { search 100; }
          prf : SubList ys xs} ->
       Eff t xs (\v => updateWith (ys' v) xs prf)
lift e {prf} = liftP prf e


-- --------------------------------------------------------- [ Running Effects ]

||| Run an effectful program
run : Applicative m => {default MkDefaultEnv env : Env m xs} -> Eff a xs xs' -> m a
run {env} prog = eff env prog (\r, env => pure r)

runPure : {default MkDefaultEnv env : Env id xs} -> Eff a xs xs' -> a
runPure {env} prog = eff env prog (\r, env => r)

runInit : Applicative m => Env m xs -> Eff a xs xs' -> m a
runInit env prog = eff env prog (\r, env => pure r)

runPureInit : Env id xs -> Eff a xs xs' -> a
runPureInit env prog = eff env prog (\r, env => r)

runWith : (a -> m a) -> Env m xs -> Eff a xs xs' -> m a
runWith inj env prog = eff env prog (\r, env => inj r)

runEnv : Applicative m => Env m xs -> Eff a xs xs' -> 
         m (x : a ** Env m (xs' x))
runEnv env prog = eff env prog (\r, env => pure (r ** env))

-- ----------------------------------------------- [ some higher order things ]

mapE : (a -> {xs} Eff b) -> List a -> {xs} Eff (List b)
mapE f []        = pure []
mapE f (x :: xs) = [| f x :: mapE f xs |]


mapVE : (a -> {xs} Eff b) ->
        Vect n a ->
        {xs} Eff (Vect n b)
mapVE f []        = pure []
mapVE f (x :: xs) = [| f x :: mapVE f xs |]


when : Bool -> Lazy ({xs} Eff ()) -> {xs} Eff ()
when True  e = Force e
when False e = pure ()

-- --------------------------------------------------------------------- [ EOF ]

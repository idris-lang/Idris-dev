module Effects

import Language.Reflection
import public Effect.Default
import Data.Vect
import public Data.List

--- Effectful computations are described as algebraic data types that
--- explain how an effect is interpreted in some underlying context.

%access export
-- ----------------------------------------------------------------- [ Effects ]
||| The Effect type describes effectful computations.
|||
||| This type is parameterised by:
||| + The return type of the computation.
||| + The input resource.
||| + The computation to run on the resource given the return value.
public export
Effect : Type
Effect = (x : Type) -> Type -> (x -> Type) -> Type

||| The `EFFECT` Data type describes how to promote the Effect
||| description into a concrete effect.
public export
%error_reverse
data EFFECT : Type where
     MkEff : Type -> Effect -> EFFECT

-- 'sig' gives the signature for an effect. There are four versions
-- depending on whether there is no resource needed,
-- no state change, a non-dependent change,
-- or a dependent change. These are easily disambiguated by type.

namespace NoResourceEffect
  public export
  sig : Effect -> Type -> Type
  sig e r = e r () (\v => ())

namespace NoUpdateEffect
  public export
  sig : Effect -> (ret : Type) -> (resource : Type) -> Type
  sig e r e_in = e r e_in (\v => e_in)

namespace UpdateEffect
  public export
  sig : Effect -> (ret : Type) -> (res_in : Type) -> (res_out : Type) -> Type
  sig e r e_in e_out = e r e_in (\v => e_out)

namespace DepUpdateEffect
  public export
  sig : Effect ->
        (ret : Type) -> (res_in : Type) -> (res_out : ret -> Type) -> Type
  sig e r e_in e_out = e r e_in e_out

||| Handler interfaces describe how an effect `e` is translated to the
||| underlying computation context `m` for execution.
public export
interface Handler (e : Effect) (m : Type -> Type) where
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

public export
data SubElem : a -> List a -> Type where
  Z : SubElem a (a :: as)
  S : SubElem a as -> SubElem a (b :: as)

public export
data SubList : List a -> List a -> Type where
  SubNil : SubList [] xs
  InList : SubElem x ys -> SubList xs ys -> SubList (x :: xs) ys

Uninhabited (SubElem x []) where
  uninhabited Z impossible
  uninhabited (S _) impossible

-- Some useful hints for proof construction in polymorphic programs
%hint
public export total
dropFirst : SubList xs ys -> SubList xs (x :: ys)
dropFirst SubNil = SubNil
dropFirst (InList el sub) = InList (S el) (dropFirst sub)

%hint
public export total
subListId : (xs : List a) -> SubList xs xs
subListId [] = SubNil
subListId (x :: xs) = InList Z (dropFirst (subListId xs))

public export total
inSuffix : SubElem x ys -> SubList xs ys -> SubElem x (zs ++ ys)
inSuffix {zs = []} el sub = el
inSuffix {zs = (x :: xs)} el sub = S (inSuffix el sub)

%hint
public export total
dropPrefix : SubList xs ys -> SubList xs (zs ++ ys)
dropPrefix SubNil = SubNil
dropPrefix (InList el sub) = InList (inSuffix el sub) (dropPrefix sub)

public export total
inPrefix : SubElem x ys -> SubList xs ys -> SubElem x (ys ++ zs)
inPrefix {zs = []} {ys} el sub
    = rewrite appendNilRightNeutral ys in el
inPrefix {zs = (x :: xs)} Z sub = Z
inPrefix {zs = (x :: xs)} (S y) sub = S (inPrefix y SubNil)

%hint
public export total
dropSuffix : SubList xs ys -> SubList xs (ys ++ zs)
dropSuffix SubNil = SubNil
dropSuffix (InList el sub) = InList (inPrefix el sub) (dropSuffix sub)

namespace Env
  public export
  data Env  : (m : Type -> Type) -> List EFFECT -> Type where
    Nil  : Env m Nil
    (::) : Handler eff m => a -> Env m xs -> Env m (MkEff a eff :: xs)

total envElem : SubElem x xs -> Env m xs -> Env m [x]
envElem Z (x :: xs) = [x]
envElem (S k) (x :: xs) = envElem k xs

||| make an environment corresponding to a sub-list
total dropEnv : Env m ys -> SubList xs ys -> Env m xs
dropEnv [] SubNil = []
dropEnv [] (InList idx rest) = absurd idx
dropEnv (y::ys) SubNil = []
dropEnv e@(y::ys) (InList idx rest) =
  let [x] = envElem idx e
  in x :: dropEnv e rest

public export
total updateAt : (idx : SubElem x' xs) -> (a:Type) -> List EFFECT -> List EFFECT
updateAt Z a [] = []
updateAt Z a ((MkEff b eff) :: xs) = (MkEff a eff) :: xs
updateAt (S k) a [] = []
updateAt (S k) a (x :: xs) = x :: updateAt k a xs

public export
total updateWith : (ys' : List EFFECT) -> (xs : List EFFECT) ->
             SubList ys xs -> List EFFECT
updateWith [] xs sl = xs
updateWith (y :: ys) xs SubNil = xs
updateWith ((MkEff a f) :: ys) xs (InList idx rest) = updateAt idx a (updateWith ys xs rest)

public export
total replaceEnvAt : (x : a) -> (idx : SubElem x' xs) -> Env m ys ->
               Env m (updateAt idx a ys)
replaceEnvAt x Z [] = []
replaceEnvAt x Z (y :: ys) = x :: ys
replaceEnvAt x (S k) [] = []
replaceEnvAt x (S k) (y :: ys) = y :: replaceEnvAt x k ys

||| Put things back, replacing old with new in the sub-environment
public export
total rebuildEnv : {ys':List EFFECT} -> Env m ys' -> (prf : SubList ys xs) ->
             Env m xs -> Env m (updateWith ys' xs prf)
rebuildEnv [] SubNil env = env
rebuildEnv (x :: xs) SubNil env = env
rebuildEnv [] (InList w s) env = env
rebuildEnv (x :: xs) (InList idx rest) env = replaceEnvAt x idx (rebuildEnv xs rest env)

-- -------------------------------------------------- [ The Effect EDSL itself ]

public export
total updateResTy : (val : t) ->
              (xs : List EFFECT) -> with List Elem (MkEff a e) xs -> e t a b ->
              List EFFECT
updateResTy {b} val (MkEff a e :: xs) Here n = (MkEff (b val) e) :: xs
updateResTy     val (x :: xs)    (There p) n = x :: updateResTy val xs p n

infix 5 :::, :-, :=

public export
data LRes : lbl -> Type -> Type where
     (:=) : (x : lbl) -> res -> LRes x res

public export
(:::) : lbl -> EFFECT -> EFFECT
(:::) {lbl} x (MkEff r e) = MkEff (LRes x r) e

using (lbl : Type)
  implementation Default a => Default (LRes lbl a) where
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
public export
data EffM : (m : Type -> Type) -> (x : Type)
            -> (es : List EFFECT)
            -> (ce : x -> List EFFECT) -> Type where
     Value    : (val : a) -> EffM m a (xs val) xs
     EBind    : EffM m a xs xs' ->
                ((val : a) -> EffM m b (xs' val) xs'') -> EffM m b xs xs''
     CallP    : (prf : with List Elem (MkEff a e) xs) ->
                (eff : e t a b) ->
                EffM m t xs (\v => updateResTy v xs prf eff)

     LiftP    : (prf : SubList ys xs) ->
                EffM m t ys ys' -> EffM m t xs (\v => updateWith (ys' v) xs prf)

     New      : Handler e' m => (e : EFFECT) -> resTy ->
                {auto prf : e = MkEff resTy e'} ->
                EffM m t (e :: es) (\v => e :: es) ->
                EffM m t es (\v => es)

     (:-)     : (l : ty) ->
                EffM m t [x] xs' -> -- [x] (\v => xs) ->
                EffM m t [l ::: x] (\v => map (l :::) (xs' v))

-- Some type synonyms, so we don't always have to write EffM in full

namespace SimpleEff
  -- Simple effects, no updates
  public export
  Eff : (x : Type) -> (es : List EFFECT) -> Type
  Eff x es = {m : Type -> Type} -> EffM m x es (\v => es)

  public export
  EffT : (m : Type -> Type) -> (x : Type) -> (es : List EFFECT) -> Type
  EffT m x es = EffM m x es (\v => es)

namespace TransEff
  -- Dependent effects, updates not dependent on result
  public export
  Eff : (x : Type) -> (es : List EFFECT) -> (ce : List EFFECT) -> Type
  Eff x es ce = {m : Type -> Type} -> EffM m x es (\_ => ce)

  public export
  EffT : (m : Type -> Type) ->
         (x : Type) -> (es : List EFFECT) -> (ce : List EFFECT) -> Type
  EffT m x es ce = EffM m x es (\_ => ce)

namespace DepEff
  -- Dependent effects, updates dependent on result
  public export
  Eff : (x : Type) -> (es : List EFFECT)
        -> (ce : x -> List EFFECT) -> Type
  Eff x es ce = {m : Type -> Type} -> EffM m x es ce

  public export
  EffT : (m : Type -> Type) -> (x : Type) -> (es : List EFFECT)
        -> (ce : x -> List EFFECT) -> Type
  EffT m x es ce = EffM m x es ce


%no_implicit
(>>=)   : EffM m a xs xs' ->
          ((val : a) -> EffM m b (xs' val) xs'') -> EffM m b xs xs''
(>>=) = EBind

-- namespace SimpleBind
--   (>>=) : Eff m a xs (\v => xs) ->
--           ((val : a) -> Eff m b xs xs') -> Eff m b xs xs'
--   (>>=) = EBind

||| Run a subprogram which results in an effect state the same as the input.
staticEff : EffM m a xs (\v => xs) -> EffM m a xs (\v => xs)
staticEff = id

||| Explicitly give the expected set of result effects for an effectful
||| operation.
toEff : .(xs' : List EFFECT) -> EffM m a xs (\v => xs') -> EffM m a xs (\v => xs')
toEff xs' = id

infixl 2 <*>

pure : a -> EffM m a xs (\v => xs)
pure = Value

return : a -> EffM m a xs (\v => xs)
return = pure

%deprecate Effects.return "Please use `pure`."

pureM : (val : a) -> EffM m a (xs val) xs
pureM = Value

(<*>) : EffM m (a -> b) xs (\v => xs) ->
        EffM m a xs (\v => xs) -> EffM m b xs (\v => xs)
(<*>) prog v = do fn <- prog
                  arg <- v
                  pure (fn arg)

(<$>) : (a -> b) ->
        EffM m a xs (\v => xs) -> EffM m b xs (\v => xs)
(<$>) f v = pure f <*> v

(*>) : EffM m a xs (\v => xs) ->
       EffM m b xs (\v => xs) -> EffM m b xs (\v => xs)
a *> b = do a
            b

new : Handler e' m => (e : EFFECT) -> resTy ->
      {auto prf : e = MkEff resTy e'} ->
      EffM m t (e :: es) (\v => e :: es) ->
      EffM m t es (\v => es)
new = New

-- ---------------------------------------------------------- [ an interpreter ]

private
execEff : Env m xs -> (p : with List Elem (MkEff res e) xs) ->
          (eff : e a res resk) ->
          ((v : a) -> Env m (updateResTy v xs p eff) -> m t) -> m t
execEff (val :: env) Here eff' k
    = handle val eff' (\v, res => k v (res :: env))
execEff (val :: env) (There p) eff k
    = execEff env p eff (\v, env' => k v (val :: env'))

-- Q: Instead of m b, implement as StateT (Env m xs') m b, so that state
-- updates can be propagated even through failing computations?

export
eff : Env m xs -> EffM m a xs xs' -> ((x : a) -> Env m (xs' x) -> m b) -> m b
eff env (Value x) k = k x env
eff env (prog `EBind` c) k
   = eff env prog (\p', env' => eff env' (c p') k)
eff env (CallP prf effP) k = execEff env prf effP k
eff env (LiftP prf effP) k
   = let env' = dropEnv env prf in
         eff env' effP (\p', envk => k p' (rebuildEnv envk prf env))
eff env (New (MkEff resTy newEff) res {prf=Refl} effP) k
   = eff (res :: env) effP (\p', (val :: envk) => k p' envk)
eff env (l :- prog) k
   = let env' = unlabel env in
         eff env' prog (\p', envk => k p' (relabel l envk))

-- yuck :) Haven't got interface implementations working nicely in tactic
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

%no_implicit
call : {a, b: _} -> {e : Effect} ->
       (eff : e t a b) ->
       {auto prf : with List Elem (MkEff a e) xs} ->
      EffM m t xs (\v => updateResTy v xs prf eff)
call e {prf} = CallP prf e

implicit
lift : EffM m t ys ys' ->
       {auto prf : SubList ys xs} ->
       EffM m t xs (\v => updateWith (ys' v) xs prf)
lift e {prf} = LiftP prf e


-- --------------------------------------------------------- [ Running Effects ]
||| Run an effectful program.
|||
||| The content (`m`) in which to run the program is taken from the
||| environment in which the program is called. The `env` argument is
||| implicit and initialised automatically.
|||
||| @prog The effectful program to run.
%no_implicit
run : Applicative m =>
      (prog : EffM m a xs xs') -> {default MkDefaultEnv env : Env m xs} ->
      m a
run prog {env} = eff env prog (\r, env => pure r)

||| Run an effectful program in the identity context.
|||
||| A helper function useful for when the given context is 'pure'.
||| The `env` argument is implicit and initialised automatically.
|||
||| @prog The effectful program to run.
%no_implicit
runPure : (prog : EffM Basics.id a xs xs') ->
          {default MkDefaultEnv env : Env Basics.id xs} -> a
runPure prog {env} = eff env prog (\r, env => r)

||| Run an effectful program in a given context `m` with a default value for the environment.
|||
||| This is useful for when there is no default environment for the given context.
|||
||| @env The environment to use.
||| @prog The effectful program to run.
%no_implicit
runInit : Applicative m => (env : Env m xs) -> (prog : EffM m a xs xs') -> m a
runInit env prog = eff env prog (\r, env => pure r)

||| Run an effectful program with a given default value for the environment.
|||
||| A helper function useful for when the given context is 'pure' and there is no default environment.
|||
||| @env The environment to use.
||| @prog The effectful program to run.
%no_implicit
runPureInit : (env : Env Basics.id xs) -> (prog : EffM Basics.id a xs xs') -> a
runPureInit env prog = eff env prog (\r, env => r)

%no_implicit
runWith : (a -> m a) -> Env m xs -> EffM m a xs xs' -> m a
runWith inj env prog = eff env prog (\r, env => inj r)

%no_implicit
runEnv : Applicative m => Env m xs -> EffM m a xs xs' ->
         m (x : a ** Env m (xs' x))
runEnv env prog = eff env prog (\r, env => pure (r ** env))

-- ----------------------------------------------- [ some higher order things ]

mapE : (a -> EffM m b xs (\_ => xs)) -> List a -> EffM m (List b) xs (\_ => xs)
mapE f []        = pure []
mapE f (x :: xs) = [| f x :: mapE f xs |]


mapVE : (a -> EffM m b xs (\_ => xs)) ->
        Vect n a ->
        EffM m (Vect n b) xs (\_ => xs)
mapVE f []        = pure []
mapVE f (x :: xs) = [| f x :: mapVE f xs |]


when : Bool -> Lazy (EffM m () xs (\_ => xs)) -> EffM m () xs (\_ => xs)
when True  e = Force e
when False e = pure ()


-- --------------------------------------------------------------------- [ EOF ]

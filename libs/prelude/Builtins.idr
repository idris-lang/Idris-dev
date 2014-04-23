%unqualified

%access public
%default total

||| Dependent pairs, in their internal representation
||| @ a the type of the witness
||| @ P the type of the proof
data Exists : (a : Type) -> (P : a -> Type) -> Type where
    Ex_intro : {P : a -> Type} -> (x : a) -> P x -> Exists a P

||| The first projection from a dependent pair
getWitness : {P : a -> Type} -> Exists a P -> a
getWitness (a ** v) = a

||| The second projection from a dependent pair
getProof : {P : a -> Type} -> (s : Exists a P) -> P (getWitness s)
getProof (a ** v) = v

||| The eliminator for the empty type.
FalseElim : _|_ -> a

||| For 'symbol syntax. 'foo becomes Symbol_ "foo"
data Symbol_ : String -> Type where

-- ------------------------------------------------------ [ For rewrite tactic ]
||| Perform substitution in a term according to some equality.
|||
||| This is used by the `rewrite` tactic and term.
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
replace refl prf = prf

||| Symmetry of propositional equality
sym : {l:a} -> {r:a} -> l = r -> r = l
sym refl = refl

||| Transitivity of propositional equality
trans : {a:x} -> {b:y} -> {c:z} -> a = b -> b = c -> a = c
trans refl refl = refl

lazy : a -> a
lazy x = x -- compiled specially

force : a -> a
force x = x -- compiled specially

||| There are two types of laziness: that arising from lazy functions, and that
||| arising from codata. They differ in their totality condition.
data LazyType = LazyCodata | LazyEval

||| The underlying implementation of Lazy and Inf.
data Lazy' : LazyType -> Type -> Type where
     ||| A delayed computation.
     |||
     |||Delay is inserted automatically by the elaborator where necessary.
     |||
     ||| Note that compiled code gives `Delay` special semantics.
     ||| @ t   whether this is laziness from codata or normal lazy evaluation
     ||| @ a   the type of the eventual value
     ||| @ val a computation that will produce a value
     Delay : {t, a : _} -> (val : a) -> Lazy' t a

||| Compute a value from a delayed computation.
|||
||| Inserted by the elaborator where necessary.
Force : {t, a : _} -> Lazy' t a -> a
Force (Delay x) = x

||| Lazily evaluated values. This has special evaluation semantics.
Lazy : Type -> Type
Lazy t = Lazy' LazyEval t

||| Recursive parameters to codata. Inserted automatically by the elaborator
||| on a "codata" definition but is necessary by hand if mixing inductive and
||| coinductive parameters.
Inf : Type -> Type
Inf t = Lazy' LazyCodata t

par : Lazy a -> a -- Doesn't actually do anything yet. Maybe a 'Par a' type
                  -- is better in any case?
par (Delay x) = x 

malloc : Int -> a -> a
malloc size x = x -- compiled specially

trace_malloc : a -> a
trace_malloc x = x -- compiled specially

||| Assert to the totality checker than y is always structurally smaller than
||| x (which is typically a pattern argument)
||| @ x the larger value (typically a pattern argument)
||| @ y the smaller value (typically an argument to a recursive call)
assert_smaller : (x : a) -> (y : b) -> b
assert_smaller x y = y

||| Assert to the totality checker than the given expression will always
||| terminate.
assert_total : a -> a
assert_total x = x

||| Subvert the type checker. This function is abstract, so it will not reduce in
||| the type checker. Use it with care - it can result in segfaults or worse!
abstract %assert_total -- need to pretend
believe_me : a -> b
believe_me x = prim__believe_me _ _ x

||| Subvert the type checker. This function *will*  reduce in the type checker.
||| Use it with extreme care - it can result in segfaults or worse!
public %assert_total
really_believe_me : a -> b
really_believe_me x = prim__believe_me _ _ x


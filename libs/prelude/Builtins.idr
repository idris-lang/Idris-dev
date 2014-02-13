%unqualified

%access public
%default total

data Exists : (a : Type) -> (P : a -> Type) -> Type where
    Ex_intro : {P : a -> Type} -> (x : a) -> P x -> Exists a P

getWitness : {P : a -> Type} -> Exists a P -> a
getWitness (a ** v) = a

getProof : {P : a -> Type} -> (s : Exists a P) -> P (getWitness s)
getProof (a ** v) = v

FalseElim : _|_ -> a

-- For 'symbol syntax. 'foo becomes Symbol_ "foo"
data Symbol_ : String -> Type where

-- ------------------------------------------------------ [ For rewrite tactic ]
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
replace refl prf = prf

sym : {l:a} -> {r:a} -> l = r -> r = l
sym refl = refl

trans : {a:x} -> {b:x} -> {c:x} -> a = b -> b = c -> a = c
trans refl refl = refl

lazy : a -> a
lazy x = x -- compiled specially

force : a -> a
force x = x -- compiled specially

data Lazy : Type -> Type where
     Delay : (val : a) -> Lazy a

Force : Lazy a -> a
Force (Delay x) = x

par : |(thunk:a) -> a
par x = x -- compiled specially

malloc : Int -> a -> a
malloc size x = x -- compiled specially

trace_malloc : a -> a
trace_malloc x = x -- compiled specially

-- Assert to the totality checker than y is always structureally smaller than
-- x (which is typically a pattern argument)
assert_smaller : a -> a -> a
assert_smaller x y = y

-- Assert to the totality checker than the given expression will always
-- terminate.
assert_total : a -> a
assert_total x = x

abstract %assert_total -- need to pretend
believe_me : a -> b -- compiled specially as id, use with care!
believe_me x = prim__believe_me _ _ x

public %assert_total -- reduces at compile time, use with extreme care!
really_believe_me : a -> b
really_believe_me x = prim__believe_me _ _ x


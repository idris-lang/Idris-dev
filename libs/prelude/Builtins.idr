%unqualified

%access public export
%default total
%language UniquenessTypes

||| The canonical single-element type, also known as the trivially
||| true proposition.
%elim data Unit =
  ||| The trivial constructor for `()`.
  MkUnit

namespace Builtins
  ||| The non-dependent pair type, also known as conjunction.
  ||| @A the type of the left elements in the pair
  ||| @B the type of the right elements in the pair
  %elim data Pair : (A : Type) -> (B : Type) -> Type where
     ||| A pair of elements
     ||| @a the left element of the pair
     ||| @b the right element of the pair
     MkPair : {A, B : Type} -> (a : A) -> (b : B) -> Pair A B

  -- Usage hints for erasure analysis
  %used MkPair a
  %used MkPair b

  ||| The non-dependent pair type, also known as conjunction, usable with
  ||| UniqueTypes.
  ||| @A the type of the left elements in the pair
  ||| @B the type of the right elements in the pair
  data UPair : (A : AnyType) -> (B : AnyType) -> AnyType where
     ||| A pair of elements
     ||| @a the left element of the pair
     ||| @b the right element of the pair
     MkUPair : {A, B : AnyType} -> (a : A) -> (b : B) -> UPair A B

  -- Usage hints for erasure analysis
  %used MkUPair a
  %used MkUPair b

  ||| Dependent pairs aid in the construction of dependent types by
  ||| providing evidence that some value resides in the type.
  |||
  ||| Formally, speaking, dependent pairs represent existential
  ||| quantification - they consist of a witness for the existential
  ||| claim and a proof that the property holds for it.
  |||
  |||  @a the value to place in the type.
  |||  @P the dependent type that requires the value.
  data DPair : (a : Type) -> (P : a -> Type) -> Type where
      MkDPair : .{P : a -> Type} -> (x : a) -> (pf : P x) -> DPair a P

  Sigma : (a : Type) -> (P : a -> Type) -> Type
  Sigma wit prf = DPair wit prf
  %deprecate Sigma "This name is being deprecated in favour of `DPair`."

  MkSigma : .{P : a -> Type} -> (x : a) -> (prf : P x) -> DPair a P
  MkSigma wit prf = MkDPair wit prf
  %deprecate MkSigma "This constructor is being deprecated in favour of `MkDPair`."

||| The empty type, also known as the trivially false proposition.
|||
||| Use `void` or `absurd` to prove anything if you have a variable of type `Void` in scope.
%elim data Void : Type where

||| The eliminator for the `Void` type.
void : Void -> a
-- We can't define void yet. We can't define a function with no clauses without
-- elaborator reflection, and we can't do elaborator reflection without
-- Language.Reflection.Elab, and Language.Reflection.Elab depends on Builtins.
-- We can't delay the declaration of void, because Prelude.Uninhabited depends on
-- it, Prelude.Nat depends on Prelude.Uninhabited, and Language.Reflection.Elab
-- depends on Prelude.Nat. Instead, void is defined in Prelude.idr

||| For 'symbol syntax. 'foo becomes Symbol_ "foo"
data Symbol_ : String -> Type where

infix 5 ~=~

||| Explicit heterogeneous ("John Major") equality. Use this when Idris
||| incorrectly chooses homogeneous equality for `(=)`.
||| @ a the type of the left side
||| @ b the type of the right side
||| @ x the left side
||| @ y the right side
(~=~) : (x : a) -> (y : b) -> Type
(~=~) x y = (x = y)

||| Perform substitution in a term according to some equality.
replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
replace Refl prf = prf

||| Perform substitution in a term according to some equality.
|||
||| Like `replace`, but with an explicit predicate, and applying the rewrite
||| in the other direction, which puts it in a form usable by the `rewrite`
||| tactic and term.
rewrite__impl : (P : a -> Type) -> x = y -> P y -> P x
rewrite__impl P Refl prf = prf

||| Symmetry of propositional equality
sym : {left:a} -> {right:b} -> left = right -> right = left
sym Refl = Refl

||| Transitivity of propositional equality
trans : {a:x} -> {b:y} -> {c:z} -> a = b -> b = c -> a = c
trans Refl Refl = Refl

||| Two types of delayed computation: that arising from lazy functions, and that
||| arising from infinite data. They differ in their totality condition.
data DelayReason = Infinite | LazyValue

||| The underlying implementation of Lazy and Inf.
%error_reverse
data Delayed : DelayReason -> Type -> Type where
     ||| A delayed computation.
     |||
     ||| Delay is inserted automatically by the elaborator where necessary.
     |||
     ||| Note that compiled code gives `Delay` special semantics.
     ||| @ t   whether this is laziness from an infinite structure or lazy evaluation
     ||| @ a   the type of the eventual value
     ||| @ val a computation that will produce a value
     Delay : {t, a : _} -> (val : a) -> Delayed t a

||| Compute a value from a delayed computation.
|||
||| Inserted by the elaborator where necessary.
Force : {t, a : _} -> Delayed t a -> a
Force (Delay x) = x

||| Lazily evaluated values. 
||| At run time, the delayed value will only be computed when required by
||| a case split.
%error_reverse
Lazy : Type -> Type
Lazy t = Delayed LazyValue t

||| Possibly infinite data. 
||| A value which may be infinite is accepted by the totality checker if
||| it appears under a data constructor. At run time, the delayed value will
||| only be computed when required by a case split.
%error_reverse
Inf : Type -> Type
Inf t = Delayed Infinite t

namespace Ownership
  ||| A read-only version of a unique value
  data Borrowed : UniqueType -> NullType where
       Read : {a : UniqueType} -> a -> Borrowed a

  ||| Make a read-only version of a unique value, which can be passed to another
  ||| function without the unique value being consumed.
  implicit -- needs a special case in the coercion code, since implicits need
           -- a concrete type to coerce!
  lend : {a : UniqueType} -> a -> Borrowed a
  lend x = Read x

par : Lazy a -> a -- Doesn't actually do anything yet. Maybe a 'Par a' type
                  -- is better in any case?
par (Delay x) = x

||| Assert to the totality checker that y is always structurally smaller than
||| x (which is typically a pattern argument, and *must* be in normal form
||| for this to work)
||| @ x the larger value (typically a pattern argument)
||| @ y the smaller value (typically an argument to a recursive call)
assert_smaller : (x : a) -> (y : b) -> b
assert_smaller x y = y

||| Assert to the totality checker that the given expression will always
||| terminate.
assert_total : a -> a
assert_total x = x

||| Assert to the totality checker that the case using this expression
||| is unreachable
assert_unreachable : a
-- compiled as primitive

||| Abort immediately with an error message
idris_crash : (msg : String) -> a
-- compiled as primitive

%used idris_crash msg

||| Subvert the type checker. This function is abstract, so it will not reduce in
||| the type checker. Use it with care - it can result in segfaults or worse!
export 
believe_me : a -> b
believe_me x = assert_total (prim__believe_me _ _ x)

||| Subvert the type checker. This function *will*  reduce in the type checker.
||| Use it with extreme care - it can result in segfaults or worse!
public export 
really_believe_me : a -> b
really_believe_me x = assert_total (prim__believe_me _ _ x)

||| Deprecated alias for `Double`, for the purpose of backwards
||| compatibility. Idris does not support 32 bit floats at present.
Float : Type
Float = Double
%deprecate Float

-- Pointers as external primitive; there's no literals for these, so no
-- need for them to be part of the compiler.

export data Ptr : Type
export data ManagedPtr : Type
export data CData : Type

%extern prim__readFile : prim__WorldType -> Ptr -> String
%extern prim__readChars : prim__WorldType -> Int -> Ptr -> String
%extern prim__writeFile : prim__WorldType -> Ptr -> String -> Int

%extern prim__vm : prim__WorldType -> Ptr
%extern prim__stdin : Ptr
%extern prim__stdout : Ptr
%extern prim__stderr : Ptr

%extern prim__null : Ptr
%extern prim__eqPtr : Ptr -> Ptr -> Int
%extern prim__eqManagedPtr : ManagedPtr -> ManagedPtr -> Int
%extern prim__registerPtr : Ptr -> Int -> ManagedPtr

-- primitives for accessing memory.
%extern prim__asPtr : ManagedPtr -> Ptr
%extern prim__sizeofPtr : Int
%extern prim__ptrOffset : Ptr -> Int -> Ptr
%extern prim__peek8 : prim__WorldType -> Ptr -> Int -> Bits8
%extern prim__peek16 : prim__WorldType -> Ptr -> Int -> Bits16
%extern prim__peek32 : prim__WorldType -> Ptr -> Int -> Bits32
%extern prim__peek64 : prim__WorldType -> Ptr -> Int -> Bits64

%extern prim__poke8 : prim__WorldType -> Ptr -> Int -> Bits8 -> Int
%extern prim__poke16 : prim__WorldType -> Ptr -> Int -> Bits16 -> Int
%extern prim__poke32 : prim__WorldType -> Ptr -> Int -> Bits32 -> Int
%extern prim__poke64 : prim__WorldType -> Ptr -> Int -> Bits64 -> Int

%extern prim__peekPtr : prim__WorldType -> Ptr -> Int -> Ptr
%extern prim__pokePtr : prim__WorldType -> Ptr -> Int -> Ptr -> Int

%extern prim__peekDouble : prim__WorldType -> Ptr -> Int -> Double
%extern prim__pokeDouble : prim__WorldType -> Ptr -> Int -> Double -> Int
%extern prim__peekSingle : prim__WorldType -> Ptr -> Int -> Double
%extern prim__pokeSingle : prim__WorldType -> Ptr -> Int -> Double -> Int

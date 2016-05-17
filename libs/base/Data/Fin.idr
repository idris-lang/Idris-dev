module Data.Fin

%default total
%access public export

||| Numbers strictly less than some bound.  The name comes from "finite sets".
|||
||| It's probably not a good idea to use `Fin` for arithmetic, and they will be
||| exceedingly inefficient at run time.
||| @ n the upper bound
data Fin : (n : Nat) -> Type where
    FZ : Fin (S k)
    FS : Fin k -> Fin (S k)

implementation Uninhabited (Fin Z) where
  uninhabited FZ impossible
  uninhabited (FS f) impossible

FSInjective : (m : Fin k) -> (n : Fin k) -> FS m = FS n -> m = n
FSInjective left _ Refl = Refl

implementation Eq (Fin n) where
    (==) FZ FZ = True
    (==) (FS k) (FS k') = k == k'
    (==) _ _ = False

||| There are no elements of `Fin Z`
FinZAbsurd : Fin Z -> Void
FinZAbsurd FZ impossible

FinZElim : Fin Z -> a
FinZElim x = void (FinZAbsurd x)

||| Convert a Fin to a Nat
finToNat : Fin n -> Nat
finToNat FZ = Z
finToNat (FS k) = S (finToNat k)

||| `finToNat` is injective
finToNatInjective : (fm : Fin k) -> (fn : Fin k) -> (finToNat fm) = (finToNat fn) -> fm = fn
finToNatInjective FZ     FZ     Refl = Refl
finToNatInjective (FS m) FZ     Refl impossible
finToNatInjective FZ     (FS n) Refl impossible
finToNatInjective (FS m) (FS n) prf  =
  cong (finToNatInjective m n (succInjective (finToNat m) (finToNat n) prf))

implementation Cast (Fin n) Nat where
    cast x = finToNat x

||| Convert a Fin to an Integer
finToInteger : Fin n -> Integer
finToInteger FZ     = 0
finToInteger (FS k) = 1 + finToInteger k

implementation Cast (Fin n) Integer where
    cast x = finToInteger x

||| Weaken the bound on a Fin by 1
weaken : Fin n -> Fin (S n)
weaken FZ     = FZ
weaken (FS k) = FS (weaken k)

||| Weaken the bound on a Fin by some amount
weakenN : (n : Nat) -> Fin m -> Fin (m + n)
weakenN n FZ = FZ
weakenN n (FS f) = FS (weakenN n f)

||| Attempt to tighten the bound on a Fin.
||| Return `Left` if the bound could not be tightened, or `Right` if it could.
strengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} FZ = Right FZ
strengthen {n = S k} (FS i) with (strengthen i)
  strengthen (FS k) | Left x   = Left (FS x)
  strengthen (FS k) | Right x  = Right (FS x)
strengthen f = Left f

||| Add some natural number to a Fin, extending the bound accordingly
||| @ n the previous bound
||| @ m the number to increase the Fin by
shift : (m : Nat) -> Fin n -> Fin (m + n)
shift Z f = f
shift {n=n} (S m) f = FS {k = (m + n)} (shift m f)

||| The largest element of some Fin type
last : Fin (S n)
last {n=Z} = FZ
last {n=S _} = FS last

total FSinjective : {f : Fin n} -> {f' : Fin n} -> (FS f = FS f') -> f = f'
FSinjective Refl = Refl

implementation Ord (Fin n) where
  compare  FZ     FZ    = EQ
  compare  FZ    (FS _) = LT
  compare (FS _)  FZ    = GT
  compare (FS x) (FS y) = compare x y

implementation MinBound (Fin (S n)) where
  minBound = FZ

implementation MaxBound (Fin (S n)) where
  maxBound = last


-- Construct a Fin from an integer literal which must fit in the given Fin

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just FZ
natToFin (S k) (S j) with (natToFin k j)
                          | Just k' = Just (FS k')
                          | Nothing = Nothing
natToFin _ _ = Nothing

||| Convert an `Integer` to a `Fin`, provided the integer is within bounds.
||| @n The upper bound of the Fin
integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x Z = Nothing -- make sure 'n' is concrete, to save reduction!
integerToFin x n = if x >= 0 then natToFin (cast x) n else Nothing

||| Allow overloading of Integer literals for Fin.
||| @ x the Integer that the user typed
||| @ prf an automatically-constructed proof that `x` is in bounds
fromInteger : (x : Integer) ->
              {default ItIsJust
               prf : (IsJust (integerToFin x n))} ->
              Fin n
fromInteger {n} x {prf} with (integerToFin x n)
  fromInteger {n} x {prf = ItIsJust} | Just y = y

||| Convert an Integer to a Fin in the required bounds/
||| This is essentially a composition of `mod` and `fromInteger`
export
restrict : (n : Nat) -> Integer -> Fin (S n)
restrict n val = let val' = assert_total (abs (mod val (cast (S n)))) in
                     -- reasoning about primitives, so we need the
                     -- 'believe_me'. It's fine because val' must be
                     -- in the right range
                     fromInteger val'
                         {prf = believe_me {a=IsJust (Just val')} ItIsJust}

%language ErrorReflection

||| Attempt to convert a reflected (fromInteger n) to a Nat
total private
getNat' : TT -> Maybe TT
getNat' `(fromInteger ~(TConst (BI c)) : Nat) = Just $ quote (the Nat (fromInteger c))
getNat' _ = Nothing

||| Attempt to convert a reflected (fromInteger n) to a Nat. Return
||| the original term on failure.
total private
getNat : TT -> TT
getNat tm = maybe tm id $ getNat' tm

total private
mkFinIntegerErr : TT -> TT -> List ErrorReportPart -> Maybe (List ErrorReportPart)
mkFinIntegerErr lit finSize subErr
  = Just [ TextPart "When using", TermPart lit
         , TextPart "as a literal for a"
         , TermPart `(Fin ~(getNat finSize))
         , SubReport subErr
         ]
total export
finFromIntegerErrors : Err -> Maybe (List ErrorReportPart)
finFromIntegerErrors (CantUnify x tm `(IsJust (integerToFin ~(TConst c) ~m)) err xs y)
  = mkFinIntegerErr (TConst c) m
      [ TermPart (TConst c)
      , TextPart "is not strictly less than"
      , TermPart (getNat m)
      ]
finFromIntegerErrors (CantUnify x tm `(IsJust (integerToFin ~(P Bound n t) ~m)) err xs y)
  = mkFinIntegerErr (P Bound n t) m
      [ TextPart "Could not show that", TermPart (P Bound n t)
      , TextPart "is less than", TermPart (getNat m)
      , TextPart "because", TermPart (P Bound n t)
      , TextPart "is a bound variable instead of a constant"
      , TermPart `(Integer : Type)
      ]
finFromIntegerErrors (CantUnify x tm `(IsJust (integerToFin ~n ~m)) err xs y)
  = mkFinIntegerErr n m
      [ TextPart "Could not show that" , TermPart n
      , TextPart "is less than" , TermPart (getNat m)
      ]
finFromIntegerErrors _ = Nothing

%error_handlers Data.Fin.fromInteger prf finFromIntegerErrors

implementation Enum (Fin (S n)) where
  pred FZ = FZ
  pred (FS n) = weaken n
  succ n = case strengthen (FS n) of
    Left _ => last
    Right k => k
  toNat n = cast n
  fromNat {n=n} m = case natToFin m (S n) of
    Just k => k
    Nothing => last

--------------------------------------------------------------------------------
-- DecEq
--------------------------------------------------------------------------------

total FZNotFS : {f : Fin n} -> FZ {k = n} = FS f -> Void
FZNotFS Refl impossible

implementation DecEq (Fin n) where
  decEq FZ FZ = Yes Refl
  decEq FZ (FS f) = No FZNotFS
  decEq (FS f) FZ = No $ negEqSym FZNotFS
  decEq (FS f) (FS f') with (decEq f f')
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ FSinjective {f = f} {f' = f'} h

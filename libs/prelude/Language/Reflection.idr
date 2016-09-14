module Language.Reflection

import Builtins
import Prelude.Applicative
import Prelude.Basics
import Prelude.Foldable
import Prelude.Functor
import Prelude.List
import Prelude.Nat
import Prelude.Traversable
import Prelude.Uninhabited
import Decidable.Equality

%access public export

||| A source location in an Idris file
record SourceLocation where
  ||| Either a source span or a source location. `start` and `end`
  ||| will be the same if it's a point location.
  constructor FileLoc

  ||| The file name of the source location
  filename : String
  ||| The line and column of the beginning of the source span
  start : (Int, Int)
  ||| The line and column of the end of the source span
  end : (Int, Int)

%name SourceLocation loc, loc'

private
fileLocInj : (FileLoc fn s e = FileLoc fn' s' e') -> (fn = fn', s = s', e = e')
fileLocInj Refl = (Refl, Refl, Refl)

implementation DecEq SourceLocation where
  decEq (FileLoc f s e) (FileLoc f' s' e') with (decEq f f')
    decEq (FileLoc f s e) (FileLoc f s' e')  | Yes Refl with (decEq s s')
      decEq (FileLoc f s e) (FileLoc f s e')  | Yes Refl | Yes Refl with (decEq e e')
        decEq (FileLoc f s e) (FileLoc f s e)  | Yes Refl | Yes Refl | Yes Refl =
            Yes Refl
        decEq (FileLoc f s e) (FileLoc f s e') | Yes Refl | Yes Refl | No contra =
            No $ contra . snd . snd . fileLocInj
      decEq (FileLoc f s e) (FileLoc f s' e') | Yes Refl | No contra =
          No $ contra . fst . snd . fileLocInj
    decEq (FileLoc f s e) (FileLoc f' s' e') | No contra =
        No $ contra . fst . fileLocInj



mutual
  data TTName =
              ||| A user-provided name
              UN String |
              ||| A name in some namespace.
              |||
              ||| The namespace is in reverse order, so `(NS (UN "foo") ["B", "A"])`
              ||| represents the name `A.B.foo`
              NS TTName (List String) |
              ||| Machine-chosen names
              MN Int String |
              ||| Special names, to make conflicts impossible and language features
              ||| predictable
              SN SpecialName
  %name TTName n, n'

  data SpecialName = WhereN Int TTName TTName
                   | WithN Int TTName
                   | ImplementationN TTName (List String)
                   | ParentN TTName String
                   | MethodN TTName
                   | CaseN SourceLocation TTName
                   | ElimN TTName
                   | ImplementationCtorN TTName
                   | MetaN TTName TTName
  %name SpecialName sn, sn'

InstanceN : TTName -> (List String) -> SpecialName
InstanceN = ImplementationN
%deprecate InstanceN "`InstanceN` is deprecated, Please use `ImplementationN` instead."

InstanceCtorN : TTName ->  SpecialName
InstanceCtorN = ImplementationCtorN
%deprecate InstanceCtorN "`InstanceCtorN` is deprecated, Please use `ImplementationCtorN` instead."

-- Rather  than  implement  one-off  private functions,  we  make  the
-- disjointness of  the constructors available to  all Idris programs,
-- at the cost of a bit of scrolling here.

implementation Uninhabited (UN _ = NS _ _) where
  uninhabited Refl impossible

implementation Uninhabited (UN _ = MN _ _) where
  uninhabited Refl impossible

implementation Uninhabited (UN _ = SN _) where
  uninhabited Refl impossible

implementation Uninhabited (NS _ _ = UN _) where
  uninhabited Refl impossible

implementation Uninhabited (NS _ _ = MN _ _) where
  uninhabited Refl impossible

implementation Uninhabited (NS _ _ = SN _) where
  uninhabited Refl impossible

implementation Uninhabited (MN _ _ = UN _) where
  uninhabited Refl impossible

implementation Uninhabited (MN _ _ = NS _ _) where
  uninhabited Refl impossible

implementation Uninhabited (MN _ _ = SN _) where
  uninhabited Refl impossible

implementation Uninhabited (SN _ = UN _) where
  uninhabited Refl impossible

implementation Uninhabited (SN _ = MN _ _) where
  uninhabited Refl impossible

implementation Uninhabited (SN _ = NS _ _) where
  uninhabited Refl impossible

implementation Uninhabited ((WhereN x n n') = (WithN y z)) where
  uninhabited Refl impossible

implementation Uninhabited ((WhereN x n n') = (ImplementationN y xs)) where
  uninhabited Refl impossible

implementation Uninhabited ((WhereN x n n') = (ParentN y z)) where
  uninhabited Refl impossible

implementation Uninhabited ((WhereN x n n') = (MethodN y)) where
  uninhabited Refl impossible

implementation Uninhabited ((WhereN x n n') = (CaseN loc y)) where
  uninhabited Refl impossible

implementation Uninhabited ((WhereN x n n') = (ElimN y)) where
  uninhabited Refl impossible

implementation Uninhabited ((WhereN x n n') = (ImplementationCtorN y)) where
  uninhabited Refl impossible

implementation Uninhabited ((WhereN x n n') = (MetaN y z)) where
  uninhabited Refl impossible

implementation Uninhabited ((WithN x n) = (WhereN y n' z)) where
  uninhabited Refl impossible

implementation Uninhabited ((WithN x n) = (ImplementationN n' xs)) where
  uninhabited Refl impossible

implementation Uninhabited ((WithN x n) = (ParentN n' y)) where
  uninhabited Refl impossible

implementation Uninhabited ((WithN x n) = (MethodN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((WithN x n) = (CaseN loc n')) where
  uninhabited Refl impossible

implementation Uninhabited ((WithN x n) = (ElimN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((WithN x n) = (ImplementationCtorN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((WithN x n) = (MetaN n' y)) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationN n xs) = (WhereN x n' y)) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationN n xs) = (WithN x n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationN n xs) = (ParentN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationN n xs) = (MethodN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationN n xs) = (CaseN loc n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationN n xs) = (ElimN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationN n xs) = (ImplementationCtorN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationN n xs) = (MetaN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((ParentN n x) = (WhereN y n' z)) where
  uninhabited Refl impossible

implementation Uninhabited ((ParentN n x) = (WithN y n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ParentN n x) = (ImplementationN n' xs)) where
  uninhabited Refl impossible

implementation Uninhabited ((ParentN n x) = (MethodN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ParentN n x) = (CaseN loc n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ParentN n x) = (ElimN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ParentN n x) = (ImplementationCtorN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ParentN n x) = (MetaN n' y)) where
  uninhabited Refl impossible

implementation Uninhabited ((MethodN n) = (WhereN x n' y)) where
  uninhabited Refl impossible

implementation Uninhabited ((MethodN n) = (WithN x n')) where
  uninhabited Refl impossible

implementation Uninhabited ((MethodN n) = (ImplementationN n' xs)) where
  uninhabited Refl impossible

implementation Uninhabited ((MethodN n) = (ParentN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((MethodN n) = (CaseN loc n')) where
  uninhabited Refl impossible

implementation Uninhabited ((MethodN n) = (ElimN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((MethodN n) = (ImplementationCtorN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((MethodN n) = (MetaN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((CaseN loc n) = (WhereN x n' y)) where
  uninhabited Refl impossible

implementation Uninhabited ((CaseN loc n) = (WithN x n')) where
  uninhabited Refl impossible

implementation Uninhabited ((CaseN loc n) = (ImplementationN n' xs)) where
  uninhabited Refl impossible

implementation Uninhabited ((CaseN loc n) = (ParentN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((CaseN loc n) = (MethodN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((CaseN loc n) = (ElimN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((CaseN loc n) = (ImplementationCtorN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((CaseN loc n) = (MetaN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((ElimN n) = (WhereN x n' y)) where
  uninhabited Refl impossible

implementation Uninhabited ((ElimN n) = (WithN x n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ElimN n) = (ImplementationN n' xs)) where
  uninhabited Refl impossible

implementation Uninhabited ((ElimN n) = (ParentN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((ElimN n) = (MethodN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ElimN n) = (CaseN loc n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ElimN n) = (ImplementationCtorN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ElimN n) = (MetaN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationCtorN n) = (WhereN x n' y)) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationCtorN n) = (WithN x n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationCtorN n) = (ImplementationN n' xs)) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationCtorN n) = (ParentN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationCtorN n) = (MethodN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationCtorN n) = (CaseN loc n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationCtorN n) = (ElimN n')) where
  uninhabited Refl impossible

implementation Uninhabited ((ImplementationCtorN n) = (MetaN n' x)) where
  uninhabited Refl impossible

implementation Uninhabited ((MetaN n n') = (WhereN x y z)) where
  uninhabited Refl impossible

implementation Uninhabited ((MetaN n n') = (WithN x y)) where
  uninhabited Refl impossible

implementation Uninhabited ((MetaN n n') = (ImplementationN x xs)) where
  uninhabited Refl impossible

implementation Uninhabited ((MetaN n n') = (ParentN x y)) where
  uninhabited Refl impossible

implementation Uninhabited ((MetaN n n') = (MethodN x)) where
  uninhabited Refl impossible

implementation Uninhabited ((MetaN n n') = (CaseN loc x)) where
  uninhabited Refl impossible

implementation Uninhabited ((MetaN n n') = (ElimN x)) where
  uninhabited Refl impossible

implementation Uninhabited ((MetaN n n') = (ImplementationCtorN x)) where
  uninhabited Refl impossible

mutual
  private
  unInj : (UN x = UN y) -> x = y
  unInj Refl = Refl

  private
  nsInj : (NS n ns = NS n' ns') -> (n = n', ns = ns')
  nsInj Refl = (Refl, Refl)

  private
  mnInj : (MN i s = MN i' s') -> (i = i', s = s')
  mnInj Refl = (Refl, Refl)

  private
  snInj : SN sn = SN sn' -> sn = sn'
  snInj Refl = Refl

  private
  decTTNameEq : (n1, n2 : TTName) -> Dec (n1 = n2)
  decTTNameEq (UN x) (UN y) with (decEq x y)
    decTTNameEq (UN x) (UN y) | Yes prf =
        Yes (cong prf)
    decTTNameEq (UN x) (UN y) | No contra =
        No $ contra . unInj
  decTTNameEq (UN x) (NS n xs) = No absurd
  decTTNameEq (UN x) (MN y z) = No absurd
  decTTNameEq (UN x) (SN y) = No absurd
  decTTNameEq (NS n xs) (UN x) = No absurd
  decTTNameEq (NS n ns) (NS n' ns') with (decTTNameEq n n')
    decTTNameEq (NS n ns) (NS n ns')  | Yes Refl with (decEq ns ns')
      decTTNameEq (NS n ns) (NS n ns)   | Yes Refl | Yes Refl =
          Yes Refl
      decTTNameEq (NS n ns) (NS n ns')  | Yes Refl | No contra =
          No $ contra . snd . nsInj
    decTTNameEq (NS n ns) (NS n' ns') | No contra =
        No $ contra . fst . nsInj
  decTTNameEq (NS n xs) (MN x y) = No absurd
  decTTNameEq (NS n xs) (SN x) = No absurd
  decTTNameEq (MN x y) (UN z) = No absurd
  decTTNameEq (MN x y) (NS n xs) = No absurd
  decTTNameEq (MN x y) (MN z w) with (decEq x z)
    decTTNameEq (MN x y) (MN x w) | Yes Refl with (decEq y w)
      decTTNameEq (MN x y) (MN x y) | Yes Refl | Yes Refl =
          Yes Refl
      decTTNameEq (MN x y) (MN x w) | Yes Refl | No contra =
          No $ contra . snd . mnInj
    decTTNameEq (MN x y) (MN z w) | No contra =
        No $ contra . fst . mnInj
  decTTNameEq (MN x y) (SN z) = No absurd
  decTTNameEq (SN x) (UN y) = No absurd
  decTTNameEq (SN x) (NS n xs) = No absurd
  decTTNameEq (SN x) (MN y z) = No absurd
  decTTNameEq (SN x) (SN y) with (decSNEq x y)
    decTTNameEq (SN x) (SN x) | Yes Refl = Yes Refl
    decTTNameEq (SN x) (SN y) | (No contra) = No $ contra . snInj


  private
  whereNInj : (WhereN x n n' = WhereN y z w) -> (x = y, n = z, n' = w)
  whereNInj Refl = (Refl, Refl, Refl)

  private
  withNInj : (WithN x n = WithN y n') -> (x = y, n = n')
  withNInj Refl = (Refl, Refl)

  private
  instanceNInj : (ImplementationN n xs = ImplementationN n' ys) -> (n = n', xs = ys)
  instanceNInj Refl = (Refl, Refl)

  private
  implementationNInj : (ImplementationN n xs = ImplementationN n' ys) -> (n = n', xs = ys)
  implementationNInj Refl = (Refl, Refl)
  
  private
  parentNInj : (ParentN n x = ParentN n' y) -> (n = n', x = y)
  parentNInj Refl = (Refl, Refl)

  private
  methodNInj : (MethodN n = MethodN n') -> n = n'
  methodNInj Refl = Refl

  private
  caseNInj : (CaseN loc n = CaseN loc' n') -> (loc = loc', n = n')
  caseNInj Refl = (Refl, Refl)

  private
  elimNInj : (ElimN n = ElimN n') -> n = n'
  elimNInj Refl = Refl

  private
  implementationCtorNInj : (ImplementationCtorN n = ImplementationCtorN n') -> n = n'
  implementationCtorNInj Refl = Refl

  private
  metaNInj : (MetaN n m = MetaN n' m') -> (n = n', m = m')
  metaNInj Refl = (Refl, Refl)

  private
  decSNEq : (n1, n2 : SpecialName) -> Dec (n1 = n2)
  decSNEq (WhereN x n n') (WhereN y z w) with (decEq x y)
    decSNEq (WhereN x n n') (WhereN x z w) | Yes Refl with (assert_total $ decTTNameEq n z)
      decSNEq (WhereN x n n') (WhereN x n w) | Yes Refl | Yes Refl with (assert_total $ decTTNameEq n' w)
        decSNEq (WhereN x n n') (WhereN x n n') | Yes Refl | Yes Refl | Yes Refl =
            Yes Refl
        decSNEq (WhereN x n n') (WhereN x n w) | Yes Refl | Yes Refl | No contra =
            No $ contra . snd . snd . whereNInj
      decSNEq (WhereN x n n') (WhereN x z w) | Yes Refl | No contra =
          No $ contra . fst . snd . whereNInj
    decSNEq (WhereN x n n') (WhereN y z w) | No contra =
        No $ contra . fst . whereNInj
  decSNEq (WhereN x n n') (WithN y z) = No absurd
  decSNEq (WhereN x n n') (ImplementationN y xs) = No absurd
  decSNEq (WhereN x n n') (ParentN y z) = No absurd
  decSNEq (WhereN x n n') (MethodN y) = No absurd
  decSNEq (WhereN x n n') (CaseN loc y) = No absurd
  decSNEq (WhereN x n n') (ElimN y) = No absurd
  decSNEq (WhereN x n n') (ImplementationCtorN y) = No absurd
  decSNEq (WhereN x n n') (MetaN y z) = No absurd
  decSNEq (WithN x n) (WhereN y n' z) = No absurd
  decSNEq (WithN x n) (WithN y n') with (decEq x y)
    decSNEq (WithN x n) (WithN x n') | Yes Refl  with (assert_total $ decTTNameEq n n')
      decSNEq (WithN x n) (WithN x n)  | Yes Refl  | Yes Refl =
          Yes Refl
      decSNEq (WithN x n) (WithN x n') | Yes Refl  | No contra =
          No $ contra . snd . withNInj
    decSNEq (WithN x n) (WithN y n') | No contra =
        No $ contra . fst . withNInj
  decSNEq (WithN x n) (ImplementationN n' xs) = No absurd
  decSNEq (WithN x n) (ParentN n' y) = No absurd
  decSNEq (WithN x n) (MethodN n') = No absurd
  decSNEq (WithN x n) (CaseN loc n') = No absurd
  decSNEq (WithN x n) (ElimN n') = No absurd
  decSNEq (WithN x n) (ImplementationCtorN n') = No absurd
  decSNEq (WithN x n) (MetaN n' y) = No absurd
  decSNEq (ImplementationN n xs) (WhereN x n' y) = No absurd
  decSNEq (ImplementationN n xs) (WithN x n') = No absurd
  decSNEq (ImplementationN n xs) (ImplementationN n' ys) with (assert_total $ decTTNameEq n n')
    decSNEq (ImplementationN n xs) (ImplementationN n ys)  | Yes Refl with (decEq xs ys)
      decSNEq (ImplementationN n xs) (ImplementationN n xs)  | Yes Refl | Yes Refl =
          Yes Refl
      decSNEq (ImplementationN n xs) (ImplementationN n ys)  | Yes Refl | No contra =
          No $ contra . snd . implementationNInj
    decSNEq (ImplementationN n xs) (ImplementationN n' ys) | No contra =
        No $ contra . fst . implementationNInj
  decSNEq (ImplementationN n xs) (ParentN n' x) = No absurd
  decSNEq (ImplementationN n xs) (MethodN n') = No absurd
  decSNEq (ImplementationN n xs) (CaseN loc n') = No absurd
  decSNEq (ImplementationN n xs) (ElimN n') = No absurd
  decSNEq (ImplementationN n xs) (ImplementationCtorN n') = No absurd
  decSNEq (ImplementationN n xs) (MetaN n' x) = No absurd
  decSNEq (ParentN n x) (WhereN y n' z) = No absurd
  decSNEq (ParentN n x) (WithN y n') = No absurd
  decSNEq (ParentN n x) (ImplementationN n' xs) = No absurd
  decSNEq (ParentN n x) (ParentN n' y) with (assert_total $ decTTNameEq n n')
    decSNEq (ParentN n x) (ParentN n y)  | Yes Refl with (decEq x y)
      decSNEq (ParentN n x) (ParentN n x) | Yes Refl | Yes Refl =
          Yes Refl
      decSNEq (ParentN n x) (ParentN n y) | Yes Refl | No contra =
          No $ contra . snd . parentNInj
    decSNEq (ParentN n x) (ParentN n' y) | No contra =
        No $ contra . fst . parentNInj
  decSNEq (ParentN n x) (MethodN n') = No absurd
  decSNEq (ParentN n x) (CaseN loc n') = No absurd
  decSNEq (ParentN n x) (ElimN n') = No absurd
  decSNEq (ParentN n x) (ImplementationCtorN n') = No absurd
  decSNEq (ParentN n x) (MetaN n' y) = No absurd
  decSNEq (MethodN n) (WhereN x n' y) = No absurd
  decSNEq (MethodN n) (WithN x n') = No absurd
  decSNEq (MethodN n) (ImplementationN n' xs) = No absurd
  decSNEq (MethodN n) (ParentN n' x) = No absurd
  decSNEq (MethodN n) (MethodN n') with (assert_total $ decTTNameEq n n')
    decSNEq (MethodN n) (MethodN n)  | Yes Refl =
        Yes Refl
    decSNEq (MethodN n) (MethodN n') | No contra =
        No $ contra . methodNInj
  decSNEq (MethodN n) (CaseN loc n') = No absurd
  decSNEq (MethodN n) (ElimN n') = No absurd
  decSNEq (MethodN n) (ImplementationCtorN n') = No absurd
  decSNEq (MethodN n) (MetaN n' x) = No absurd
  decSNEq (CaseN loc n) (WhereN x n' y) = No absurd
  decSNEq (CaseN loc n) (WithN x n') = No absurd
  decSNEq (CaseN loc n) (ImplementationN n' xs) = No absurd
  decSNEq (CaseN loc n) (ParentN n' x) = No absurd
  decSNEq (CaseN loc n) (MethodN n') = No absurd
  decSNEq (CaseN loc n) (CaseN loc' n') with (decEq loc loc')
    decSNEq (CaseN loc n) (CaseN loc n')  | Yes Refl with (assert_total $ decTTNameEq n n')
      decSNEq (CaseN loc n) (CaseN loc n)  | Yes Refl | Yes Refl =
          Yes Refl
      decSNEq (CaseN loc n) (CaseN loc n') | Yes Refl | No contra =
          No $ contra . snd . caseNInj
    decSNEq (CaseN loc n) (CaseN loc' n') | No contra =
        No $ contra . fst . caseNInj
  decSNEq (CaseN loc n) (ElimN n') = No absurd
  decSNEq (CaseN loc n) (ImplementationCtorN n') = No absurd
  decSNEq (CaseN loc n) (MetaN n' x) = No absurd
  decSNEq (ElimN n) (WhereN x n' y) = No absurd
  decSNEq (ElimN n) (WithN x n') = No absurd
  decSNEq (ElimN n) (ImplementationN n' xs) = No absurd
  decSNEq (ElimN n) (ParentN n' x) = No absurd
  decSNEq (ElimN n) (MethodN n') = No absurd
  decSNEq (ElimN n) (CaseN loc n') = No absurd
  decSNEq (ElimN n) (ElimN n') with (assert_total $ decTTNameEq n n')
    decSNEq (ElimN n) (ElimN n)  | Yes Refl =
        Yes Refl
    decSNEq (ElimN n) (ElimN n') | No contra =
        No $ contra . elimNInj
  decSNEq (ElimN n) (ImplementationCtorN n') = No absurd
  decSNEq (ElimN n) (MetaN n' x) = No absurd
  decSNEq (ImplementationCtorN n) (WhereN x n' y) = No absurd
  decSNEq (ImplementationCtorN n) (WithN x n') = No absurd
  decSNEq (ImplementationCtorN n) (ImplementationN n' xs) = No absurd
  decSNEq (ImplementationCtorN n) (ParentN n' x) = No absurd
  decSNEq (ImplementationCtorN n) (MethodN n') = No absurd
  decSNEq (ImplementationCtorN n) (CaseN loc n') = No absurd
  decSNEq (ImplementationCtorN n) (ElimN n') = No absurd
  decSNEq (ImplementationCtorN n) (ImplementationCtorN n') with (assert_total $ decTTNameEq n n')
    decSNEq (ImplementationCtorN n) (ImplementationCtorN n)  | Yes Refl =
        Yes Refl
    decSNEq (ImplementationCtorN n) (ImplementationCtorN n') | No contra =
        No $ contra . implementationCtorNInj
  decSNEq (ImplementationCtorN n) (MetaN n' x) = No absurd
  decSNEq (MetaN n n') (WhereN x y z) = No absurd
  decSNEq (MetaN n n') (WithN x y) = No absurd
  decSNEq (MetaN n n') (ImplementationN x xs) = No absurd
  decSNEq (MetaN n n') (ParentN x y) = No absurd
  decSNEq (MetaN n n') (MethodN x) = No absurd
  decSNEq (MetaN n n') (CaseN loc x) = No absurd
  decSNEq (MetaN n n') (ElimN x) = No absurd
  decSNEq (MetaN n n') (ImplementationCtorN x) = No absurd
  decSNEq (MetaN n n') (MetaN x y) with (assert_total $ decTTNameEq n x)
    decSNEq (MetaN n n') (MetaN n y) | Yes Refl with (assert_total $ decTTNameEq n' y)
      decSNEq (MetaN n n') (MetaN n n') | Yes Refl | Yes Refl =
          Yes Refl
      decSNEq (MetaN n n') (MetaN n y) | Yes Refl | No contra =
          No $ contra . snd . metaNInj
    decSNEq (MetaN n n') (MetaN x y) | No contra =
        No $ contra . fst . metaNInj

-- (Temporarily?) Outside the mutual block, since otherwise we get the
-- warning on the second pass!
%deprecate instanceNInj "`instanceNInj` is deprecated, Please use `implementationNInj` instead."

implementation DecEq TTName where
  decEq = decTTNameEq

implementation DecEq SpecialName where
  decEq = decSNEq

data TTUExp =
            ||| Universe variable
            UVar String Int |
            ||| Explicit universe level
            UVal Int
%name TTUExp uexp

data NativeTy = IT8 | IT16 | IT32 | IT64

data IntTy = ITFixed NativeTy | ITNative | ITBig | ITChar

data ArithTy = ATInt Language.Reflection.IntTy | ATDouble

||| Primitive constants
data Const = I Int | BI Integer | Fl Double | Ch Char | Str String
           | B8 Bits8 | B16 Bits16 | B32 Bits32 | B64 Bits64
           | AType ArithTy | StrType
           | VoidType | Forgot
           | WorldType | TheWorld
%name Const c, c'

export interface ReflConst (a : Type) where
   toConst : a -> Const

implementation ReflConst Int where
   toConst x = I x

implementation ReflConst Integer where
   toConst = BI

implementation ReflConst Double where
   toConst = Fl

implementation ReflConst Char where
   toConst = Ch

implementation ReflConst String where
   toConst = Str

implementation ReflConst Bits8 where
   toConst = B8

implementation ReflConst Bits16 where
   toConst = B16

implementation ReflConst Bits32 where
   toConst = B32

implementation ReflConst Bits64 where
   toConst = B64

implicit export
reflectConstant: (ReflConst a) => a -> Const
reflectConstant = toConst


||| Types of named references
data NameType =
  ||| A reference which is just bound, e.g. by intro
  Bound |
  ||| A reference to a de Bruijn-indexed variable
  Ref |
  ||| Data constructor with tag and number
  DCon Int Int |
  ||| Type constructor with tag and number
  TCon Int Int

%name NameType nt, nt'

||| Types annotations for bound variables in different
||| binding contexts
|||
||| @ tmTy the terms that can occur inside the binder, as type
|||        annotations or bound values
data Binder : (tmTy : Type) -> Type where
  ||| Lambdas
  |||
  ||| @ ty the type of the argument
  Lam : (ty : a) -> Binder a

  ||| Function types.
  |||
  ||| @ kind The kind of arrow. Only relevant when dealing with
  |||        uniqueness, so you can usually pretend that this
  |||        field doesn't exist. For ordinary functions, use the
  |||        type of types here.
  Pi : (ty, kind : a) -> Binder a

  ||| A let binder
  |||
  ||| @ ty the type of the bound variable
  ||| @ val the bound value
  Let : (ty, val : a) -> Binder a

  ||| A hole that can occur during elaboration, and must be filled
  |||
  ||| @ ty the type of the value that will eventually be put into the hole
  Hole : (ty : a) -> Binder a

  ||| A hole that will later become a top-level metavariable
  GHole : (ty : a) -> Binder a

  ||| A hole with a solution in it. Computationally inert.
  |||
  ||| @ ty the type of the value in the hole
  ||| @ val the value in the hole
  Guess : (ty, val : a) -> Binder a

  ||| A pattern variable. These bindings surround the terms that make
  ||| up the left and right sides of pattern-matching definition
  ||| clauses.
  |||
  ||| @ ty the type of the pattern variable
  PVar : (ty : a) -> Binder a

  ||| The type of a pattern binding. This is to `PVar` as `Pi` is to
  ||| `Lam`.
  |||
  ||| @ ty the type of the pattern variable
  PVTy : (ty : a) -> Binder a

%name Binder b, b'

implementation Functor Binder where
  map f (Lam x) = Lam (f x)
  map f (Pi x k) = Pi (f x) (f k)
  map f (Let x y) = Let (f x) (f y)
  map f (Hole x) = Hole (f x)
  map f (GHole x) = GHole (f x)
  map f (Guess x y) = Guess (f x) (f y)
  map f (PVar x) = PVar (f x)
  map f (PVTy x) = PVTy (f x)

implementation Foldable Binder where
  foldr f z (Lam x) = f x z
  foldr f z (Pi x k) = f x (f k z)
  foldr f z (Let x y) = f x (f y z)
  foldr f z (Hole x) = f x z
  foldr f z (GHole x) = f x z
  foldr f z (Guess x y) = f x (f y z)
  foldr f z (PVar x) = f x z
  foldr f z (PVTy x) = f x z

implementation Traversable Binder where
  traverse f (Lam x) = [| Lam (f x) |]
  traverse f (Pi x k) = [| Pi (f x) (f k) |]
  traverse f (Let x y) = [| Let (f x) (f y) |]
  traverse f (Hole x) = [| Hole (f x) |]
  traverse f (GHole x) = [| GHole (f x) |]
  traverse f (Guess x y) = [| Guess (f x) (f y) |]
  traverse f (PVar x) = [| PVar (f x) |]
  traverse f (PVTy x) = [| PVTy (f x) |]

||| The various universes involved in the uniqueness mechanism
data Universe = NullType | UniqueType | AllTypes

||| Reflection of the well typed core language
data TT =
        ||| A reference to some name (P for Parameter)
        P NameType TTName TT |
        ||| de Bruijn variables
        V Int |
        ||| Bind a variable
        Bind TTName (Binder TT) TT |
        ||| Apply one term to another
        App TT TT |
        ||| Embed a constant
        TConst Const |
        ||| Erased terms
        Erased |
        ||| The type of types along (with universe constraints)
        TType TTUExp |
        ||| Alternative universes for dealing with uniqueness
        UType Universe
%name TT tm, tm'

||| Raw terms without types
data Raw =
         ||| Variables, global or local
         Var TTName |
         ||| Bind a variable
         RBind TTName (Binder Raw) Raw |
         ||| Application
         RApp Raw Raw |
         ||| The type of types
         RType |
         ||| Alternative universes for dealing with uniqueness
         RUType Universe |
         ||| Embed a constant
         RConstant Const
%name Raw tm, tm'

||| Error reports are a list of report parts
data ErrorReportPart =
                     ||| A human-readable string
                     TextPart String |
                     ||| An Idris name (to be semantically coloured)
                     NamePart TTName |
                     ||| An Idris term, to be pretty printed
                     TermPart TT |
                     ||| A Raw term to be displayed by the compiler
                     RawPart Raw |
                     ||| An indented sub-report, to provide more details
                     SubReport (List ErrorReportPart)
%name ErrorReportPart part, p

||| A representation of Idris's old tactics that can be returned from custom
||| tactic implementations. Generate these using `applyTactic`.
data Tactic =
            ||| Try the first tactic and resort to the second one on failure
            Try Tactic Tactic |
            ||| Only run if the goal has the right type
            GoalType String Tactic |
            ||| Resolve function name, find matching arguments in the
            ||| context and compute the proof target
            Refine TTName |
            ||| Apply both tactics in sequence
            Seq Tactic Tactic |
            ||| Introduce a new hole with a particular type
            Claim TTName TT |
            ||| Move the current hole to the end
            Unfocus |
            ||| Intelligently construct the proof target from the context
            Trivial |
            ||| Build a proof by applying contructors up to a maximum depth
            Search Int |
            ||| Resolve an interface
            Implementation |
            ||| Infer the proof target from the context
            Solve |
            ||| introduce all variables into the context
            Intros |
            ||| Introduce a named variable into the context, use the
            ||| first one if the given name is not found
            Intro TTName |
            ||| Invoke the reflected rep. of another tactic
            ApplyTactic TT |
            ||| Turn a value into its reflected representation
            Reflect TT |
            ||| Use a `%reflection` function
            ByReflection TT |
            ||| Turn a raw value back into a term
            Fill Raw |
            ||| Use the given value to conclude the proof
            Exact TT |
            ||| Focus on a particular hole
            Focus TTName |
            ||| Rewrite with an equality
            Rewrite TT |
            ||| Perform induction on a particular expression
            Induction TT |
            ||| Perform case analysis on a particular expression
            Case TT |
            ||| Name a reflected term
            LetTac TTName TT |
            ||| Name a reflected term and type it
            LetTacTy TTName TT TT |
            ||| Normalise the goal
            Compute |
            ||| Do nothing
            Skip |
            ||| Fail with an error message
            Fail (List ErrorReportPart) |
            ||| Attempt to fill the hole with source code information
            SourceFC

%name Tactic tac, tac'


||| Things with a canonical representation as a reflected term.
|||
||| This interface is intended to be used during proof automation and the
||| construction of custom tactics.
|||
||| @ a the type to be quoted
||| @ t the type to quote it to (typically `TT` or `Raw`)
interface Quotable a t where
  ||| A representation of the type `a`.
  |||
  ||| This is to enable quoting polymorphic datatypes
  quotedTy : t

  ||| Quote a particular element of `a`.
  |||
  ||| Each equation should look something like ```quote (Foo x y) = `(Foo ~(quote x) ~(quote y))```
  quote : a -> t

implementation Quotable Nat TT where
  quotedTy = `(Nat)

  quote Z     = `(Z)
  quote (S k) = `(S ~(quote k))

implementation Quotable Nat Raw where
  quotedTy = `(Nat)

  quote Z     = `(Z)
  quote (S k) = `(S ~(quote k))

implementation Quotable Int TT where
  quotedTy = `(Int)
  quote x = TConst (I x)

implementation Quotable Int Raw where
  quotedTy = `(Int)
  quote x = RConstant (I x)

implementation Quotable Double TT where
  quotedTy = `(Double)
  quote x = TConst (Fl x)

implementation Quotable Double Raw where
  quotedTy = `(Double)
  quote x = RConstant (Fl x)

implementation Quotable Char TT where
  quotedTy = `(Char)
  quote x = TConst (Ch x)

implementation Quotable Char Raw where
  quotedTy = `(Char)
  quote x = RConstant (Ch x)

implementation Quotable Bits8 TT where
  quotedTy = `(Bits8)
  quote x = TConst (B8 x)

implementation Quotable Bits8 Raw where
  quotedTy = `(Bits8)
  quote x = RConstant (B8 x)

implementation Quotable Bits16 TT where
  quotedTy = `(Bits16)
  quote x = TConst (B16 x)

implementation Quotable Bits16 Raw where
  quotedTy = `(Bits16)
  quote x = RConstant (B16 x)

implementation Quotable Bits32 TT where
  quotedTy = `(Bits32)
  quote x = TConst (B32 x)

implementation Quotable Bits32 Raw where
  quotedTy = `(Bits32)
  quote x = RConstant (B32 x)

implementation Quotable Bits64 TT where
  quotedTy = `(Bits64)
  quote x = TConst (B64 x)

implementation Quotable Bits64 Raw where
  quotedTy = `(Bits64)
  quote x = RConstant (B64 x)

implementation Quotable Integer TT where
  quotedTy = `(Integer)
  quote x = TConst (BI x)

implementation Quotable Integer Raw where
  quotedTy = `(Integer)
  quote x = RConstant (BI x)

implementation Quotable String TT where
  quotedTy = `(String)
  quote x = TConst (Str x)

implementation Quotable String Raw where
  quotedTy = `(String)
  quote x = RConstant (Str x)

implementation Quotable a TT => Quotable (List a) TT where
  quotedTy = `(List ~(quotedTy {a}))
  quote [] = `(List.Nil {elem=~(quotedTy {a})})
  quote (x :: xs) = `(List.(::) {elem=~(quotedTy {a})} ~(quote x) ~(quote xs))

implementation Quotable a Raw => Quotable (List a) Raw where
  quotedTy = `(List ~(quotedTy {a}))
  quote [] = `(List.Nil {elem=~(quotedTy {a})})
  quote (x :: xs) = `(List.(::) {elem=~(quotedTy {a})} ~(quote x) ~(quote xs))

implementation Quotable () TT where
  quotedTy = `(Unit)
  quote () = `(MkUnit)

implementation Quotable () Raw where
  quotedTy = `(Unit)
  quote () = `(MkUnit)

implementation (Quotable a TT, Quotable b TT) => Quotable (a, b) TT where
  quotedTy = `(Pair ~(quotedTy {a=a}) ~(quotedTy {a=b}))
  quote (x, y) = `(MkPair {A=~(quotedTy {a=a})} {B=~(quotedTy {a=b})} ~(quote x) ~(quote y))

implementation (Quotable a Raw, Quotable b Raw) => Quotable (a, b) Raw where
  quotedTy = `(Pair ~(quotedTy {a=a}) ~(quotedTy {a=b}))
  quote (x, y) = `(MkPair {A=~(quotedTy {a=a})} {B=~(quotedTy {a=b})} ~(quote x) ~(quote y))

implementation Quotable SourceLocation TT where
  quotedTy = `(SourceLocation)
  quote (FileLoc fn (sl, sc) (el, ec)) =
    `(FileLoc ~(quote fn)
              (~(quote sl), ~(quote sc))
              (~(quote el), ~(quote ec)))

implementation Quotable SourceLocation Raw where
  quotedTy = `(SourceLocation)
  quote (FileLoc fn (sl, sc) (el, ec)) =
    `(FileLoc ~(quote {t=Raw} fn)
              (~(quote {t=Raw} sl), ~(quote {t=Raw} sc))
              (~(quote {t=Raw} el), ~(quote {t=Raw} ec)))


mutual
  implementation Quotable TTName TT where
    quotedTy = `(TTName)
    quote (UN x) = `(UN ~(quote x))
    quote (NS n xs) = `(NS ~(quote n) ~(quote xs))
    quote (MN x y) = `(MN ~(quote x) ~(quote y))
    quote (SN sn) = `(SN ~(assert_total $ quote sn))

  implementation Quotable SpecialName TT where
    quotedTy = `(SpecialName)
    quote (WhereN i n1 n2) = `(WhereN ~(quote i) ~(quote n1) ~(quote n2))
    quote (WithN i n) = `(WithN ~(quote i) ~(quote n))
    quote (ImplementationN i ss) = `(ImplementationN ~(quote i) ~(quote ss))
    quote (ParentN n s) = `(ParentN ~(quote n) ~(quote s))
    quote (MethodN n) = `(MethodN ~(quote n))
    quote (CaseN fc n) = `(CaseN ~(quote fc) ~(quote n))
    quote (ElimN n) = `(ElimN ~(quote n))
    quote (ImplementationCtorN n) = `(ImplementationCtorN ~(quote n))
    quote (MetaN parent meta) = `(MetaN ~(quote parent) ~(quote meta))

mutual
  implementation Quotable TTName Raw where
    quotedTy = `(TTName)
    quote (UN x) = `(UN ~(quote {t=Raw} x))
    quote (NS n xs) = `(NS ~(quote {t=Raw} n) ~(quote {t=Raw} xs))
    quote (MN x y) = `(MN ~(quote {t=Raw} x) ~(quote {t=Raw} y))
    quote (SN sn) = `(SN ~(assert_total $ quote sn))

  implementation Quotable SpecialName Raw where
    quotedTy = `(SpecialName)
    quote (WhereN i n1 n2) = `(WhereN ~(quote i) ~(quote n1) ~(quote n2))
    quote (WithN i n) = `(WithN ~(quote i) ~(quote n))
    quote (ImplementationN i ss) = `(ImplementationN ~(quote i) ~(quote ss))
    quote (ParentN n s) = `(ParentN ~(quote n) ~(quote s))
    quote (MethodN n) = `(MethodN ~(quote n))
    quote (CaseN fc n) = `(CaseN ~(quote fc) ~(quote n))
    quote (ElimN n) = `(ElimN ~(quote n))
    quote (ImplementationCtorN n) = `(ImplementationCtorN ~(quote n))
    quote (MetaN parent meta) = `(MetaN ~(quote parent) ~(quote meta))


implementation Quotable TTUExp TT where
  quotedTy = `(TTUExp)
  quote (UVar ns x) = `(UVar ~(quote ns) ~(quote x))
  quote (UVal x) = `(UVal ~(quote x))

implementation Quotable TTUExp Raw where
  quotedTy = `(TTUExp)
  quote (UVar ns x) = `(UVar ~(quote ns) ~(quote {t=Raw} x))
  quote (UVal x) = `(UVal ~(quote {t=Raw} x))

implementation Quotable NativeTy TT where
    quotedTy = `(NativeTy)
    quote IT8 = `(Reflection.IT8)
    quote IT16 = `(Reflection.IT16)
    quote IT32 = `(Reflection.IT32)
    quote IT64 = `(Reflection.IT64)

implementation Quotable NativeTy Raw where
    quotedTy = `(NativeTy)
    quote IT8 = `(Reflection.IT8)
    quote IT16 = `(Reflection.IT16)
    quote IT32 = `(Reflection.IT32)
    quote IT64 = `(Reflection.IT64)

implementation Quotable Reflection.IntTy TT where
  quotedTy = `(Reflection.IntTy)
  quote (ITFixed x) = `(ITFixed ~(quote x))
  quote ITNative = `(Reflection.ITNative)
  quote ITBig = `(ITBig)
  quote ITChar = `(Reflection.ITChar)

implementation Quotable Reflection.IntTy Raw where
  quotedTy = `(Reflection.IntTy)
  quote (ITFixed x) = `(ITFixed ~(quote {t=Raw} x))
  quote ITNative = `(Reflection.ITNative)
  quote ITBig = `(ITBig)
  quote ITChar = `(Reflection.ITChar)

implementation Quotable ArithTy TT where
  quotedTy = `(ArithTy)
  quote (ATInt x) = `(ATInt ~(quote x))
  quote ATDouble = `(ATDouble)

implementation Quotable ArithTy Raw where
  quotedTy = `(ArithTy)
  quote (ATInt x) = `(ATInt ~(quote {t=Raw} x))
  quote ATDouble = `(ATDouble)

implementation Quotable Const TT where
  quotedTy = `(Const)
  quote (I x) = `(I ~(quote x))
  quote (BI x) = `(BI ~(quote x))
  quote (Fl x) = `(Fl ~(quote x))
  quote (Ch x) = `(Ch ~(quote x))
  quote (Str x) = `(Str ~(quote x))
  quote (B8 x) = `(B8 ~(quote x))
  quote (B16 x) = `(B16 ~(quote x))
  quote (B32 x) = `(B32 ~(quote x))
  quote (B64 x) = `(B64 ~(quote x))
  quote (AType x) = `(AType ~(quote x))
  quote StrType = `(StrType)
  quote VoidType = `(VoidType)
  quote Forgot = `(Forgot)
  quote WorldType = `(WorldType)
  quote TheWorld = `(TheWorld)

implementation Quotable Const Raw where
  quotedTy = `(Const)
  quote (I x) = `(I ~(quote {t=Raw} x))
  quote (BI x) = `(BI ~(quote {t=Raw} x))
  quote (Fl x) = `(Fl ~(quote {t=Raw} x))
  quote (Ch x) = `(Ch ~(quote {t=Raw} x))
  quote (Str x) = `(Str ~(quote {t=Raw} x))
  quote (B8 x) = `(B8 ~(quote {t=Raw} x))
  quote (B16 x) = `(B16 ~(quote {t=Raw} x))
  quote (B32 x) = `(B32 ~(quote {t=Raw} x))
  quote (B64 x) = `(B64 ~(quote {t=Raw} x))
  quote (AType x) = `(AType ~(quote {t=Raw} x))
  quote StrType = `(StrType)
  quote VoidType = `(VoidType)
  quote Forgot = `(Forgot)
  quote WorldType = `(WorldType)
  quote TheWorld = `(TheWorld)

implementation Quotable NameType TT where
  quotedTy = `(NameType)
  quote Bound = `(Bound)
  quote Ref = `(Ref)
  quote (DCon x y) = `(DCon ~(quote x) ~(quote y))
  quote (TCon x y) = `(TCon ~(quote x) ~(quote y))

implementation Quotable NameType Raw where
  quotedTy = `(NameType)
  quote Bound = `(Bound)
  quote Ref = `(Ref)
  quote (DCon x y) = `(DCon ~(quote {t=Raw} x) ~(quote {t=Raw} y))
  quote (TCon x y) = `(TCon ~(quote {t=Raw} x) ~(quote {t=Raw} y))

implementation Quotable Universe TT where
  quotedTy = `(Universe)
  quote Reflection.NullType = `(NullType)
  quote Reflection.UniqueType = `(UniqueType)
  quote Reflection.AllTypes = `(AllTypes)

implementation Quotable Universe Raw where
  quotedTy = `(Universe)
  quote Reflection.NullType = `(NullType)
  quote Reflection.UniqueType = `(UniqueType)
  quote Reflection.AllTypes = `(AllTypes)

mutual
  implementation Quotable TT TT where
    quotedTy = `(TT)
    quote (P nt n tm) = `(P ~(quote nt) ~(quote n) ~(quote tm))
    quote (V x) = `(V ~(quote x))
    quote (Bind n b tm) = `(Bind ~(quote n) ~(assert_total (quote b)) ~(quote tm))
    quote (App f x) = `(App ~(quote f) ~(quote x))
    quote (TConst c) = `(TConst ~(quote c))
    quote Erased = `(Erased)
    quote (TType uexp) = `(TType ~(quote uexp))
    quote (UType u) = `(UType ~(quote u))

  implementation Quotable (Binder TT) TT where
    quotedTy = `(Binder TT)
    quote (Lam x) = `(Lam {a=TT} ~(assert_total (quote x)))
    quote (Pi x k) = `(Pi {a=TT} ~(assert_total (quote x))
                                 ~(assert_total (quote k)))
    quote (Let x y) = `(Let {a=TT} ~(assert_total (quote x))
                                           ~(assert_total (quote y)))
    quote (Hole x) = `(Hole {a=TT} ~(assert_total (quote x)))
    quote (GHole x) = `(GHole {a=TT} ~(assert_total (quote x)))
    quote (Guess x y) = `(Guess {a=TT} ~(assert_total (quote x))
                                             ~(assert_total (quote y)))
    quote (PVar x) = `(PVar {a=TT} ~(assert_total (quote x)))
    quote (PVTy x) = `(PVTy {a=TT} ~(assert_total (quote x)))

mutual
  quoteTTRaw : TT -> Raw
  quoteTTRaw (P nt n tm) = `(P ~(quote nt) ~(quote n) ~(quoteTTRaw tm))
  quoteTTRaw (V x) = `(V ~(quote x))
  quoteTTRaw (Bind n b tm) = `(Bind ~(quote n) ~(assert_total $ quoteTTBinderRaw b) ~(quoteTTRaw tm))
  quoteTTRaw (App f x) = `(App ~(quoteTTRaw f) ~(quoteTTRaw x))
  quoteTTRaw (TConst c) = `(TConst ~(quote c))
  quoteTTRaw Erased = `(Erased)
  quoteTTRaw (TType uexp) = `(TType ~(quote uexp))
  quoteTTRaw (UType u) = `(UType ~(quote u))

  quoteTTBinderRaw : Binder TT -> Raw
  quoteTTBinderRaw (Lam x) = `(Lam {a=TT} ~(quoteTTRaw x))
  quoteTTBinderRaw (Pi x k) = `(Pi {a=TT} ~(quoteTTRaw x)
                                          ~(quoteTTRaw k))
  quoteTTBinderRaw (Let x y) = `(Let {a=TT} ~(quoteTTRaw x)
                                            ~(quoteTTRaw y))
  quoteTTBinderRaw (Hole x) = `(Hole {a=TT} ~(quoteTTRaw x))
  quoteTTBinderRaw (GHole x) = `(GHole {a=TT} ~(quoteTTRaw x))
  quoteTTBinderRaw (Guess x y) = `(Guess {a=TT} ~(quoteTTRaw x)
                                                ~(quoteTTRaw y))
  quoteTTBinderRaw (PVar x) = `(PVar {a=TT} ~(quoteTTRaw x))
  quoteTTBinderRaw (PVTy x) = `(PVTy {a=TT} ~(quoteTTRaw x))

implementation Quotable TT Raw where
  quotedTy = `(TT)
  quote = quoteTTRaw

implementation Quotable (Binder TT) Raw where
  quotedTy = `(Binder TT)
  quote = quoteTTBinderRaw

mutual
  quoteRawTT : Raw -> TT
  quoteRawTT (Var n) = `(Var ~(quote n))
  quoteRawTT (RBind n b tm) = `(RBind ~(quote n) ~(assert_total $ quoteRawBinderTT b) ~(quoteRawTT tm))
  quoteRawTT (RApp tm tm') = `(RApp ~(quoteRawTT tm) ~(quoteRawTT tm'))
  quoteRawTT RType = `(RType)
  quoteRawTT (RUType u) = `(RUType ~(quote u))
  quoteRawTT (RConstant c) = `(RConstant ~(quote c))

  quoteRawBinderTT : Binder Raw -> TT
  quoteRawBinderTT (Lam x) = `(Lam {a=Raw} ~(quoteRawTT x))
  quoteRawBinderTT (Pi x k) = `(Pi {a=Raw} ~(quoteRawTT x) ~(quoteRawTT k))
  quoteRawBinderTT (Let x y) = `(Let {a=Raw} ~(quoteRawTT x) ~(quoteRawTT y))
  quoteRawBinderTT (Hole x) = `(Hole {a=Raw} ~(quoteRawTT x))
  quoteRawBinderTT (GHole x) = `(GHole {a=Raw} ~(quoteRawTT x))
  quoteRawBinderTT (Guess x y) = `(Guess {a=Raw} ~(quoteRawTT x) ~(quoteRawTT y))
  quoteRawBinderTT (PVar x) = `(PVar {a=Raw} ~(quoteRawTT x))
  quoteRawBinderTT (PVTy x) = `(PVTy {a=Raw} ~(quoteRawTT x))

implementation Quotable Raw TT where
  quotedTy = `(Raw)
  quote = quoteRawTT

implementation Quotable (Binder Raw) TT where
  quotedTy = `(Binder Raw)
  quote = quoteRawBinderTT

mutual
  quoteRawRaw : Raw -> Raw
  quoteRawRaw (Var n) = `(Var ~(quote n))
  quoteRawRaw (RBind n b tm) = `(RBind ~(quote n) ~(assert_total $ quoteRawBinderRaw b) ~(quoteRawRaw tm))
  quoteRawRaw (RApp tm tm') = `(RApp ~(quoteRawRaw tm) ~(quoteRawRaw tm'))
  quoteRawRaw RType = `(RType)
  quoteRawRaw (RUType u) = `(RUType ~(quote u))
  quoteRawRaw (RConstant c) = `(RConstant ~(quote c))

  quoteRawBinderRaw : Binder Raw -> Raw
  quoteRawBinderRaw (Lam x) = `(Lam {a=Raw} ~(quoteRawRaw x))
  quoteRawBinderRaw (Pi x k) = `(Pi {a=Raw} ~(quoteRawRaw x) ~(quoteRawRaw k))
  quoteRawBinderRaw (Let x y) = `(Let {a=Raw} ~(quoteRawRaw x) ~(quoteRawRaw y))
  quoteRawBinderRaw (Hole x) = `(Hole {a=Raw} ~(quoteRawRaw x))
  quoteRawBinderRaw (GHole x) = `(GHole {a=Raw} ~(quoteRawRaw x))
  quoteRawBinderRaw (Guess x y) = `(Guess {a=Raw} ~(quoteRawRaw x) ~(quoteRawRaw y))
  quoteRawBinderRaw (PVar x) = `(PVar {a=Raw} ~(quoteRawRaw x))
  quoteRawBinderRaw (PVTy x) = `(PVTy {a=Raw} ~(quoteRawRaw x))

implementation Quotable Raw Raw where
  quotedTy = `(Raw)
  quote = quoteRawRaw

implementation Quotable (Binder Raw) Raw where
  quotedTy = `(Binder Raw)
  quote = quoteRawBinderRaw

implementation Quotable ErrorReportPart TT where
  quotedTy = `(ErrorReportPart)
  quote (TextPart x) = `(TextPart ~(quote x))
  quote (NamePart n) = `(NamePart ~(quote n))
  quote (TermPart tm) = `(TermPart ~(quote tm))
  quote (RawPart tm) = `(RawPart ~(quote tm))
  quote (SubReport xs) = `(SubReport ~(assert_total $ quote xs))

implementation Quotable ErrorReportPart Raw where
  quotedTy = `(ErrorReportPart)
  quote (TextPart x) = `(TextPart ~(quote x))
  quote (NamePart n) = `(NamePart ~(quote n))
  quote (TermPart tm) = `(TermPart ~(quote tm))
  quote (RawPart tm) = `(RawPart ~(quote tm))
  quote (SubReport xs) = `(SubReport ~(assert_total $ quote xs))

implementation Quotable Tactic TT where
  quotedTy = `(Tactic)
  quote (Try tac tac') = `(Try ~(quote tac) ~(quote tac'))
  quote (GoalType x tac) = `(GoalType ~(quote x) ~(quote tac))
  quote (Refine n) = `(Refine ~(quote n))
  quote (Claim n ty) = `(Claim ~(quote n) ~(quote ty))
  quote Unfocus = `(Unfocus)
  quote (Seq tac tac') = `(Seq ~(quote tac) ~(quote tac'))
  quote Trivial = `(Trivial)
  quote (Search x) = `(Search ~(quote x))
  quote Implementation = `(Implementation)
  quote Solve = `(Solve)
  quote Intros = `(Intros)
  quote (Intro n) = `(Intro ~(quote n))
  quote (ApplyTactic tm) = `(ApplyTactic ~(quote tm))
  quote (Reflect tm) = `(Reflect ~(quote tm))
  quote (ByReflection tm) = `(ByReflection ~(quote tm))
  quote (Fill tm) = `(Fill ~(quote tm))
  quote (Exact tm) = `(Exact ~(quote tm))
  quote (Focus n) = `(Focus ~(quote n))
  quote (Rewrite tm) = `(Rewrite ~(quote tm))
  quote (Induction tm) = `(Induction ~(quote tm))
  quote (Case tm) = `(Case ~(quote tm))
  quote (LetTac n tm) = `(LetTac ~(quote n) ~(quote tm))
  quote (LetTacTy n tm tm') = `(LetTacTy ~(quote n) ~(quote tm) ~(quote tm'))
  quote Compute = `(Compute)
  quote Skip = `(Skip)
  quote (Fail xs) = `(Fail ~(quote xs))
  quote SourceFC = `(SourceFC)

implementation Quotable Tactic Raw where
  quotedTy = `(Tactic)
  quote (Try tac tac') = `(Try ~(quote tac) ~(quote tac'))
  quote (GoalType x tac) = `(GoalType ~(quote x) ~(quote tac))
  quote (Refine n) = `(Refine ~(quote n))
  quote (Claim n ty) = `(Claim ~(quote n) ~(quote ty))
  quote Unfocus = `(Unfocus)
  quote (Seq tac tac') = `(Seq ~(quote tac) ~(quote tac'))
  quote Trivial = `(Trivial)
  quote (Search x) = `(Search ~(quote x))
  quote Implementation = `(Implementation)
  quote Solve = `(Solve)
  quote Intros = `(Intros)
  quote (Intro n) = `(Intro ~(quote n))
  quote (ApplyTactic tm) = `(ApplyTactic ~(quote tm))
  quote (Reflect tm) = `(Reflect ~(quote tm))
  quote (ByReflection tm) = `(ByReflection ~(quote tm))
  quote (Fill tm) = `(Fill ~(quote tm))
  quote (Exact tm) = `(Exact ~(quote tm))
  quote (Focus n) = `(Focus ~(quote n))
  quote (Rewrite tm) = `(Rewrite ~(quote tm))
  quote (Induction tm) = `(Induction ~(quote tm))
  quote (Case tm) = `(Case ~(quote tm))
  quote (LetTac n tm) = `(LetTac ~(quote n) ~(quote tm))
  quote (LetTacTy n tm tm') = `(LetTacTy ~(quote n) ~(quote tm) ~(quote tm'))
  quote Compute = `(Compute)
  quote Skip = `(Skip)
  quote (Fail xs) = `(Fail ~(quote xs))
  quote SourceFC = `(SourceFC)

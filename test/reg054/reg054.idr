-- Catch typecase

data Ty = MInt | Str

eval : Ty -> Type
eval MInt = Maybe Int 
eval Str = String

tcok : (x : Ty) -> eval x -> Int
tcok MInt (Just x) = x
tcok Str "foo" = 42
tcok Str x = 100

data Infer : Type where
     MkInfer : (a : Type) -> a -> Infer

inf : Infer -> Bool
inf (MkInfer _ Z) = True
inf (MkInfer _ (S k)) = False

data InfView : Infer -> Type where
     INat : (x : Nat) -> InfView (MkInfer Nat x)

foo : (i : Infer) -> InfView i -> Nat
foo (MkInfer _ _) (INat Z) = Z
foo (MkInfer _ _) (INat (S k)) = k

data Weird : Type -> Type where
     WInt : Int -> Weird Int
     WStr : String -> Weird String
     WBot : Weird Void

weird : Weird x -> x
weird {x = Char} y = '5'

weird' : Weird x -> x
weird' {x = Prelude.Nat.Nat} y = Z

tctrick : a -> Int
tctrick (Just x) = x
tctrick Nothing = 42


> %default total
> %auto_implicits off

> postulate decLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
> postulate last : Nat

> LTB : Nat -> Type
> LTB b = DPair Nat (\ n  => LT n b)

> Foo : (t : Nat) -> Type
> Foo t = LTB (S last)

> Bar : {t : Nat} -> (n : Nat) -> Foo t -> Type
> Bar  Z    _ = Unit
> Bar (S n) x with (decLT (fst x) last)
>   | (Yes _) = Unit
>   | (No  _) = Void

> lemma : {t : Nat} -> {m : Nat} -> {x : Foo t} -> 
>         (fst x) `LT` last -> Bar (S m) x = Unit
> lemma {m} {x} prf with (decLT (fst x) last)
>   | (Yes _) = Refl
>   | (No contra) = void (contra prf)


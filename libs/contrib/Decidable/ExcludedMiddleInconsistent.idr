||| A port of Chung-Kil Hur's Agda proof that type constructor
||| injectivity is incompatible with LEM.
|||
||| See https://lists.chalmers.se/pipermail/agda/2010/001526.html
||| and its follow-ups for a good discussion.
module AntiClassical

%default total

-- Law of the excluded middle, with an appropriately classical name
parameters (TertiumNonDatur : (a : Type) -> Dec a)
  
  ||| This thing is injective, but with a size problem.
  data I : (Type -> Type) -> Type where {}
  
  Iinj : {x, y : Type -> Type} -> I x = I y -> x = y
  Iinj Refl = Refl
  
  data InverseImageOfI : Type -> Type where
    InverseI : (x : _) -> AntiClassical.I x = y -> InverseImageOfI y
  
  -- have to manually desugar with block from original proof for some reason
  J' : (a : Type) -> Dec (InverseImageOfI a) -> (Type -> Type)
  J' a (Yes (InverseI x prf)) = x
  J' a (No contra) = \x => Void
  
  J : Type -> (Type -> Type)
  J a = J' a (TertiumNonDatur (InverseImageOfI a))
  
  data InverseImageOfJ : (Type -> Type) -> Type where
    InverseJ : (a : _) -> J a = x -> InverseImageOfJ x
  
  IJIEqualsI : (x : _) -> I (J (I x)) = I x
  IJIEqualsI x with (TertiumNonDatur (InverseImageOfI (I x)))
    IJIEqualsI x | Yes (InverseI f prf) = prf
    IJIEqualsI x | No contra = absurd $ contra (InverseI x Refl)
  
  JSurjective : (x : Type -> Type) -> InverseImageOfJ x
  JSurjective x = InverseJ (I x) (Iinj (IJIEqualsI x))
  
  cantor : Type -> Type
  cantor a with (TertiumNonDatur (J a a = Void))
    cantor a | Yes prf = ()
    cantor a | No contra = Void
  
  unitNotVoid : Not (the Type () = Void)
  unitNotVoid Refl impossible
  
  cantorUnit : J a a = Void -> cantor a = ()
  cantorUnit {a} prf with (TertiumNonDatur (J a a = Void))
    cantorUnit prf | Yes x = Refl
    cantorUnit prf | No contra = absurd $ contra prf
  
  cantorVoid : (J a a = Void -> Void) -> cantor a = Void
  cantorVoid {a} prf with (TertiumNonDatur (J a a = Void))
    cantorVoid {a} prf | Yes yep   = absurd $ prf yep
    cantorVoid {a} prf | No contra = Refl
  
  congF : {f, g : Type -> Type} -> (a : Type) -> f = g -> f a = g a
  congF a Refl = Refl
  
  cantorCase : cantor = (J a) -> Void
  cantorCase {a} prf with (TertiumNonDatur (J a a = Void))
    cantorCase {a} prf | Yes a' =
      unitNotVoid $ (trans (trans (sym (cantorUnit {a=a} a')) (congF a prf)) a')
    cantorCase {a} prf | No contra =
      contra $ trans (sym $ congF a prf) (cantorVoid {a=a} contra)
  
  idrisIsAntiClassical : Void
  idrisIsAntiClassical = case JSurjective cantor of
                           InverseJ a y => cantorCase (sym y)
  

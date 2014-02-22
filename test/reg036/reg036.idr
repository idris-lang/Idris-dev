import Data.HVect
    
using (m : Nat, ts : Vect m Type)
      
  data HV : Vect n Type -> Type where
    MkHV : HVect ts -> HV ts

  showHV : Shows m ts => HV ts -> String
  showHV (MkHV v) = show v

  instance Shows m ts => Show (HV ts) where
    show = showHV

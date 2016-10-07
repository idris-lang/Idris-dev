import Data.HVect
    
using (m : Nat, ts : Vect m Type)
      
  data HV : Vect n Type -> Type where
    MkHV : HVect ts -> HV ts

  showHV : Shows ts => HV ts -> String
  showHV (MkHV v) = show v

  implementation Shows ts => Show (HV ts) where
    show = showHV

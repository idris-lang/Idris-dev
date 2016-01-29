module Effect.Default

import Data.Vect

%access public export

interface Default a where
    default : a

implementation Default Int where
    default = 0

implementation Default Integer where
    default = 0

implementation Default Double where
    default = 0

implementation Default Nat where
    default = 0

implementation Default Char where
    default = '\0'

implementation Default String where
    default = ""

implementation Default Bool where
    default = False

implementation Default () where
    default = ()

implementation (Default a, Default b) => Default (a, b) where
    default = (default, default)

implementation Default (Maybe a) where
    default = Nothing

implementation Default (List a) where
    default = []

implementation Default a => Default (Vect n a) where
    default = mkDef _ where
      mkDef : (n : Nat) -> Vect n a
      mkDef Z = []
      mkDef (S k) = default :: mkDef k

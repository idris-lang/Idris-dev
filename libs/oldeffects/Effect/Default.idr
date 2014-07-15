module Default

class Default a where
    default : a

instance Default Int where
    default = 0

instance Default Integer where
    default = 0

instance Default Float where
    default = 0

instance Default Nat where
    default = 0

instance Default Char where
    default = '\0'

instance Default String where
    default = ""

instance Default Bool where
    default = False

instance Default () where
    default = ()

instance (Default a, Default b) => Default (a, b) where
    default = (default, default)

instance Default (Maybe a) where
    default = Nothing

instance Default (List a) where
    default = []

instance Default a => Default (Vect n a) where
    default = mkDef _ where
      mkDef : (n : Nat) -> Vect n a
      mkDef Z = []
      mkDef (S k) = default :: mkDef k


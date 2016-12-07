%language UniquenessTypes

data BadList : UniqueType -> Type where
     Nil : {a : UniqueType} -> BadList a
     (::) : {a : UniqueType} -> a -> BadList a -> BadList a

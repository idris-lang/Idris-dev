%language UniquenessTypes

steal : {a : UniqueType} -> Borrowed a -> a
steal (Read x) = x

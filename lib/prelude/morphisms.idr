module prelude.morphisms

data Morphism : Set -> Set -> Set where
    Homo : (a -> b) -> Morphism a b

($) : Morphism a b -> a -> b
(Homo f) $ a = f a

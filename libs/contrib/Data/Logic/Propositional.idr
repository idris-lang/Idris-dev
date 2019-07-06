module Data.Logic.Propositional

%default total
%access public export

-- Idris uses intuitionistic logic, so it does not validate the
-- principle of excluded middle (PEM) or similar theorems of classical
-- logic. But it does validate certain relations among these
-- propositions, and that's what's in this file.

||| The principle of excluded middle
PEM : Type -> Type
PEM p = Either p (Not p)

||| Double negation elimination
DNE : Type -> Type
DNE p = Not $ Not p -> p

||| The consensus theorem (at least, the interesting part)
Consensus : Type -> Type -> Type -> Type
Consensus p q r = (q, r) -> Either (p, q) (Not p, r)

||| Peirce's law
Peirce : Type -> Type -> Type
Peirce p q = ((p -> q) -> p) -> p

||| Not sure if this one has a name, so call it Frege's law
Frege : Type -> Type -> Type -> Type
Frege p q r = (p -> r) -> (q -> r) -> ((p -> q) -> q) -> r

||| The converse of contraposition: (p -> q) -> Not q -> Not p
Transposition : Type -> Type -> Type
Transposition p q = (Not q -> Not p) -> p -> q

||| This isn't a good name.
Switch : Type -> Type
Switch p = (Not p -> p) -> p

-- PEM and the others can't be proved outright, but it is possible to
-- prove the double negations (DN) of all of them.

||| The double negation of a proposition
DN : Type -> Type
DN p = Not $ Not p

pemDN : DN $ PEM p
pemDN f = f $ Right $ \x => f $ Left x

dneDN : DN $ DNE p
dneDN f = f $ \g => void $ g $ \x => f $ \_ => x

consensusDN : DN $ Consensus p q r
consensusDN f = f $ \(y, z) => Right (\x => f $ \(_, _) => Left (x, y), z)

peirceDN : DN $ Peirce p q
peirceDN f = f $ \g => g $ \x => void $ f $ \_ => x

fregeDN : DN $ Frege p q r
fregeDN f = f $ \g, h, i => h $ i $ \x => void $ f $ \_, _, _ => g x

transpositionDN : DN $ Transposition p q
transpositionDN f = f $ \g, x => void $ g (\y => f $ \_, _ => y) x

switchDN : DN $ Switch p
switchDN f = f $ \g => g $ \x => f $ \_ => x

-- It's easy to prove all these theorems assuming PEM.

dnePEM : PEM p -> DNE p
dnePEM (Left l) _ = l
dnePEM (Right r) f = void $ f r

consensusPEM : PEM p -> Consensus p q r
consensusPEM (Left l) (y, _) = Left (l, y)
consensusPEM (Right r) (_, z) = Right (r, z)

peircePEM : PEM p -> Peirce p q
peircePEM (Left l) _ = l
peircePEM (Right r) f = f $ \x => void $ r x

fregePEM : PEM p -> Frege p q r
fregePEM (Left l) f _ _ = f l
fregePEM (Right r) _ g h = g $ h $ \x => void $ r x

transpositionPEM : PEM p -> Transposition q p
transpositionPEM (Left l) _ _ = l
transpositionPEM (Right r) f x = void $ f r x

switchPEM : PEM p -> Switch p
switchPEM (Left l) _ = l
switchPEM (Right r) f = f r

-- It's trivial to prove these theorems assuming double negation
-- elimination (DNE), since their double negations can all be proved.

||| Eliminate double negations
EDN : DN p -> DNE p -> p
EDN f g = g f

pemDNE : DNE $ PEM p -> PEM p
pemDNE = EDN pemDN

-- It's possible to prove the theorems assuming Peirce's law, but some
-- thought must be given to choosing the right instances. Peirce's law
-- is therefore weaker than PEM on an instance-by-instance basis, but
-- all the instances together are equivalent.

pemPeirce : Peirce (PEM p) Void -> PEM p
pemPeirce f = f $ \g => Right $ \x => g $ Left x

dnePeirce : Peirce p Void -> DNE p
dnePeirce f g = f $ \h => void $ g h

consensusPeirce : Peirce (Consensus p q r) Void -> Consensus p q r
consensusPeirce f (y, z) =
  f (\g, (_, _) => Right (\x => g (\_ => Left (x, y)), z)) (y, z)

fregePeirce : Peirce (Frege p q r) Void -> Frege p q r
fregePeirce f g h i =
  f (\j, _, _, _ => h $ i $ \x => void $ j $ \_, _, _ => g x) g h i

transpositionPeirce : Peirce (Transposition p q) Void -> Transposition p q
transpositionPeirce f g x =
  f (\h, _, _ => void $ g (\y => h $ \_, _ => y) x) (\j, _ => g j x) x

-- There are a variety of single axioms sufficient for deriving all of
-- classical logic. The earliest of these is known as Nicod's axiom,
-- but it is written using only nand operators and doesn't lend itself
-- to Idris's type system. Meredith's axiom, on the other hand, is
-- written using implication and negation.

||| Meredith's axiom, sufficient for deriving all of classical logic
Meredith : (p, q, r, s, t : Type) -> Type
Meredith p q r s t =
  ((((p -> q) -> Not r -> Not s) -> r) -> t) -> (t -> p) -> s -> p

-- The Meredith axiom implies all of classical logic, and so in
-- particular it implies PEM, and therefore cannot be proved in
-- intuitionistic logic. As usual, however, its double negation can be
-- proved.

meredithDN : DN $ Meredith p q r s t
meredithDN f =
  f $ \g, h, x =>
    h $ g $ \i =>
      void $ i
        (\y => void $ f $ \_, _, _ => y)
        (\z => f $ \_, _, _ => h $ g $ \_ => z)
        x

-- Meredith can be proved assuming PEM, since the type system itself
-- takes care of the rest.

meredithPEM : PEM p -> Meredith p q r s t
meredithPEM (Left l) _ _ _ = l
meredithPEM (Right r) f g x =
  g $ f $ \h =>
    void $ h
      (\y => void $ r y)
      (\z => r $ g $ f (\_ => z))
      x

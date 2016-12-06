||| Ported from Haskell:
||| https://hackage.haskell.org/package/base-4.9.0.0/docs/src/Data.Monoid.html
module Data.Monoid

%access public export
%default total

-- TODO: These instances exist, but can't be named the same.
-- Decide on names for these

-- [all] Semigroup Bool where
--   a <+> b = a && b
--
-- [all] Monoid Bool where
--   neutral = True
--
-- [any] Semigroup Bool where
--   a <+> b = a || b
--
-- [any] Monoid Bool where
--   neutral = False

Semigroup () where
  (<+>) _ _ = ()

Monoid () where
  neutral = ()

(Semigroup m, Semigroup n) => Semigroup (m, n) where
  (a, b) <+> (c, d) = (a <+> c, b <+> d)

(Monoid m, Monoid n) => Monoid (m, n) where
  neutral = (neutral, neutral)

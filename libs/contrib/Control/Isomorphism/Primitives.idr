module Control.Isomorphism.Primitives

import Control.Isomorphism
import Data.ZZ

%default total
%access public export

-- This module contains isomorphisms between convenient inductive types and
-- Idris primitives.  Because primitives lack a convenient structure, these
-- arguments typically end with "really_believe_me". This is why they are in a
-- separate module.

integerIsoZZ : Iso Integer ZZ
integerIsoZZ = MkIso toZZ fromZZ fromToZZ toFromZZ
  where toZZ : Integer -> ZZ
        toZZ n = cast n

        fromZZ : ZZ -> Integer
        fromZZ n = cast n

        toFromZZ : (n : Integer) -> fromZZ (toZZ n) = n
        toFromZZ n = really_believe_me {a = n=n} {b = fromZZ (toZZ n) = n} Refl

        fromToZZ : (n : ZZ) -> toZZ (fromZZ n) = n
        fromToZZ n = really_believe_me {a = n=n} {b = toZZ (fromZZ n) = n} Refl


packUnpackIso : Iso (List Char) String
packUnpackIso = MkIso pack
                      unpack
                      (\str => really_believe_me {a = str=str} {b = pack (unpack str) = str} Refl)
                      (\cs  => really_believe_me {a = cs=cs}   {b = unpack (pack cs) = cs}   Refl)



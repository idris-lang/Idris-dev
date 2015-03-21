module Data.Polyhedra

import Data.Vect
import Data.Graph

data Face f = MkFace (Vect n f)

data Polyhedron : Nat -> Nat -> Nat -> Type -> Type where
  MkPolyhedron : Vect k v -> Vect m (Edge v) -> Vect n (Face v) -> Polyhedron k m n v

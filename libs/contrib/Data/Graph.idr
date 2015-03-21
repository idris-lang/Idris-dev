module Data.Graph

import Data.Vect

data Edge e = MkEdge e e

data Graph : Nat −> Nat −> Type −> Type −> Type where
  MkGraph : Vect m v −> Vect n (Edge k) −> Graph m n v k

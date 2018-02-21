module Data.Chain

import Data.Vect
import Control.Isomorphism

%default total
%access public export

||| Repeated function application
Chain : Nat -> (i, o : Type) -> Type
Chain Z     _ o = o
Chain (S k) i o = i -> Chain k i o

||| Repeated endofunction application
EndoChain : Nat -> Type -> Type
EndoChain n t = Chain n t t

||| (.) generalized to any number of arguments.
after : (o -> o') -> (Chain n i o) -> (Chain n i o')
after {n=Z} f x = f x
after {n=S k} f fs = after f . fs

||| `on` generalized to any number of arguments
before : (i -> i') -> (Chain n i' o) -> (Chain n i o)
before {n=Z}   _ x  = x
before {n=S k} f fs = (f `before`) . (fs . f)

||| Fill in the same argument for all items (available for a single argument as
||| Data.Combinators.reflex)
reflexes : (Chain n i o) -> (i -> o)
reflexes {n=Z} x _ = x
reflexes {n=S k} fs y = reflexes (fs y) y

||| Create a vect of a given length from the arguments given.
packVect : Chain n i (Vect n i)
packVect {n=Z}   = []
packVect {n=S k} = (`after` packVect) . Data.Vect.(::)
-- For some reason we get a can't disambiguate name: Prelude.List.::,
-- Prelude.Stream.::, Data.Vect.:: if we leave out the Data.Vect specification

||| Apply a function over a vector to our new type
fromVectFunc : (Vect n i -> o) -> (Chain n i o)
fromVectFunc f = (f `after` packVect)

withIso : Iso t t' -> EndoChain n t -> EndoChain n t'
withIso (MkIso to from _ _) = (from `before`) . (to `after`)

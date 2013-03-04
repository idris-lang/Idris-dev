module Relation.Binary

%access public
%default total

Rel : Type -> Type
Rel a = a -> a -> Type

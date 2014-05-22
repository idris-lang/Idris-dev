module Prelude.Pairs

%access public
%default total

||| Dependent pair where the first field is erased.
data Exists : {a : Type} -> (P : a -> Type) -> Type where
    witness : .{P : a -> Type} -> .{x : a} -> (pf : P x) -> Exists P

||| Dependent pair where the second field is erased. 
data Subset : (a : Type) -> (P : a -> Type) -> Type where
    element : .{P : a -> Type} -> (x : a) -> .(pf : P x) -> Subset a P

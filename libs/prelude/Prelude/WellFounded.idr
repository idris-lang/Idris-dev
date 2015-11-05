||| Well-founded recursion
module WellFounded

import Builtins

%access public
%default total

||| An element is accessible for a relation
||| @ R The relation
||| @ x The element that is accessible for `R`
data Accessible : (R : a -> a -> Type) -> (x : a) -> Type where
  ||| An element is accessible if every element that relates to it is accessible
  MkAccessible : ((y : _) -> r y x -> Accessible r y) -> Accessible r x

||| The type of well-founded relations
||| @ R The relation that is well-founded
wellFounded : (R : a -> a -> Type) -> Type
wellFounded r = (x : _) -> Accessible r x

||| Recurse over a well-founded relation
recurse : (wellFounded r) ->
          .{p : a -> Type} ->
          ((x : a) -> ((y : a) -> r y x -> p y) -> p x) ->
          (x : a) -> p x
recurse {r} {p} wf rec x = recurse' x (wf x) where
  recurse' : (x : a) ->
             (Accessible r x) ->
             p x
  recurse' x (MkAccessible base) = rec x (\y => \r => recurse' y (base y r))

||| Prove one term smaller than another over a relation
|||
||| If used to satisfy the termination checker, all recursive calls must go through
||| `prove_smaller` with the same relation.
prove_smaller : .(wellFounded r) -> .(x : a) -> (y : a) -> .(r y x) -> a
prove_smaller _ _ y _ = y

||| Automatically prove one term smaller than another over a relation
smaller : .(wellFounded r) -> .(x : a) -> (y : a) -> .{auto pf : r y x} -> a
smaller wf x y {pf} = prove_smaller wf x y pf

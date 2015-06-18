module Syntax

syntax "fnord" [y] = y + y + y

foo : Nat
foo = fnord "argh"



module Bar

import Foo

bar_private : Nat -> Nat
bar_private n = n

export
bar_visible : Nat -> Nat
bar_visible n = n

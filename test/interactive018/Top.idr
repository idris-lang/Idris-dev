module Top

import Imported1
import public Public1

top_private : a -> a
top_private = imported1_visible

export
top_visible : a -> a
top_visible = public2_visible

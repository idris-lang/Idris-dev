module Top

import Imported1
import public Public1

top_private : a -> a
top_private a = a

export
top_visible : a -> a
top_visible a = a

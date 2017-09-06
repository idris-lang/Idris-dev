module Imported1

import Imported2

imported1_private : a -> a
imported1_private a = a

export
imported1_visible : a -> a
imported1_visible a = a

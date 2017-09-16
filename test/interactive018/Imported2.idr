module Imported1

imported2_private : a -> a
imported2_private a = a

export
imported2_visible : a -> a
imported2_visible a = a

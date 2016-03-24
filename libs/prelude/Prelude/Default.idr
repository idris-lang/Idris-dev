module Prelude.Default

import Builtins

import Prelude.Basics
import Prelude.Bool
import Prelude.Interfaces
import Prelude.Nat
import Prelude.Maybe
import Prelude.List

%access public export

interface Default a where
    default : a

implementation Default Int where
    default = 0

implementation Default Integer where
    default = 0

implementation Default Double where
    default = 0

implementation Default Nat where
    default = 0

implementation Default Char where
    default = '\0'

implementation Default String where
    default = ""

implementation Default Bool where
    default = False

implementation Default () where
    default = ()

implementation (Default a, Default b) => Default (a, b) where
    default = (default, default)

implementation Default (Maybe a) where
    default = Nothing

implementation Default (List a) where
    default = []

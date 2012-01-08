module checkall

-- This file just exists to typecheck all the prelude modules
-- Add imports here 

import builtins
import prelude
import io
import system

import prelude.cast
import prelude.nat
import prelude.fin
import prelude.list
import prelude.maybe
import prelude.either
import prelude.vect
import prelude.strings
import prelude.char

import network.cgi 

private dummy : Int
dummy = 42

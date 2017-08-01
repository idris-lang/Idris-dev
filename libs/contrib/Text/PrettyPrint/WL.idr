||| A revised Idris port of the Wadler-Leijen pretty-printer.
|||
||| This port of the Wadler-Leijen Pretty-Printer is based upon the
||| port originally created by Shayan Najd [1]. We have changed the
||| render function to be total using a technique based on
||| continuations proposed by gallais [2], and fix minor errors in the
||| original Idris port.
|||
||| [1] https://github.com/shayan-najd/wl-pprint
||| [2] https://gallais.github.io/blog/termination-tricks.html
module Text.PrettyPrint.WL

import public Text.PrettyPrint.WL.Core
import public Text.PrettyPrint.WL.Characters
import public Text.PrettyPrint.WL.Combinators

%default total
%access export

||| The JSON language, as described at http://json.org/
module Language.JSON

import Language.JSON.Lexer
import Language.JSON.Parser

import public Language.JSON.Data

%access export
%default total

||| Parse a JSON string.
parse : String -> Maybe JSON
parse x = parseJSON !(lexJSON x)

module Language.JSON.Data

import Data.String.Extra

%access private
%default total

public export
data JSON
   = JNull
   | JBoolean Bool
   | JNumber Double
   | JString String
   | JArray (List JSON)
   | JObject (List (String, JSON))

%name JSON json

showChar : Char -> String
showChar c
  = case c of
         '\b' => "\\b"
         '\f' => "\\f"
         '\n' => "\\n"
         '\r' => "\\r"
         '\t' => "\\t"
         '\\' => "\\\\"
         '"'  => "\\\""
         c => if isControl c || c >= '\127'
                 then "\\u" ++ b16ToHexString (fromInteger (cast (ord c)))
                 else singleton c

showString : String -> String
showString x = "\"" ++ concatMap showChar (unpack x) ++ "\""

||| Convert a JSON value into its string representation.
||| No whitespace is added.
stringify : JSON -> String
stringify JNull = "null"
stringify (JBoolean x) = if x then "true" else "false"
stringify (JNumber x) = show x
stringify (JString x) = showString x
stringify (JArray xs) = "[" ++ stringifyValues xs ++ "]"
  where
    stringifyValues : List JSON -> String
    stringifyValues [] = ""
    stringifyValues (x :: xs) = stringify x
                             ++ if isNil xs
                                   then ""
                                   else "," ++ stringifyValues xs
stringify (JObject xs) = "{" ++ stringifyProps xs ++ "}"
  where
    stringifyProp : (String, JSON) -> String
    stringifyProp (key, value) = showString key ++ ":" ++ stringify value

    stringifyProps : List (String, JSON) -> String
    stringifyProps [] = ""
    stringifyProps (x :: xs) = stringifyProp x
                            ++ if isNil xs
                                  then ""
                                  else "," ++ stringifyProps xs

export
Show JSON where
  show = stringify

||| Format a JSON value, indenting by `n` spaces per nesting level.
|||
||| @curr The current indentation amount, measured in spaces.
||| @n The amount of spaces to indent per nesting level.
export
format : {default 0 curr : Nat} -> (n : Nat) -> JSON -> String
format {curr} n json = indent curr $ formatValue curr n json
  where
    formatValue : (curr, n : Nat) -> JSON -> String
    formatValue _ _ (JArray []) = "[]"
    formatValue curr n (JArray xs@(_ :: _)) = "[\n" ++ formatValues xs
                                           ++ indent curr "]"
      where
        formatValues : (xs : List JSON) -> {auto ok : NonEmpty xs} -> String
        formatValues (x :: xs) = format {curr=(curr + n)} n x
                              ++ case nonEmpty xs of
                                      Yes ok => ",\n" ++ formatValues xs
                                      No _ => "\n"
    formatValue _ _ (JObject []) = "{}"
    formatValue curr n (JObject xs@(_ :: _)) = "{\n" ++ formatProps xs
                                            ++ indent curr "}"
      where
        formatProp : (String, JSON) -> String
        formatProp (key, value) = indent (curr + n) (showString key ++ ": ")
                               ++ formatValue (curr + n) n value

        formatProps : (xs : List (String, JSON)) -> {auto ok : NonEmpty xs} -> String
        formatProps (x :: xs) = formatProp x
                             ++ case nonEmpty xs of
                                     Yes ok => ",\n" ++ formatProps xs
                                     No _ => "\n"
    formatValue _ _ x = stringify x

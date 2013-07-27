module JSON

import Data.SortedMap

data JSONType : Type where
  JSONArray  : (n : Nat) -> Vect JSONType n -> JSONType
  JSONString : JSONType
  JSONNumber : JSONType
  JSONBool   : JSONType
  JSONObject : SortedMap String JSONType -> JSONType
  JSONNull   : JSONType

mutual
  using (ts : Vect JSONType n, fs : SortedMap String JSONType)
    namespace JArray
      data JArray : (n : Nat) -> Vect JSONType n -> Type where
        Nil  : JArray 0 []
        (::) : JSON t -> JArray n ts -> JArray (S n) (t :: ts)

    namespace JObject
      data JObject : SortedMap String JSONType -> Type where
        Nil  : JObject empty
        (::) : (f : (String, JSON t)) ->
               JObject fs ->
               JObject (insert (fst f) t fs)

    data JSON : JSONType -> Type where
      JSString : String -> JSON JSONString
      JSNumber : Float -> JSON JSONNumber
      JSBool   : Bool -> JSON JSONBool
      JSNull   : JSON JSONNull
      JSArray  : JArray n ts -> JSON (JSONArray n ts)
      JSObject : JObject fs -> JSON (JSONObject fs)

index : (i : Fin n) -> JSON (JSONArray n ts) -> JSON (index i ts)
index fZ     (JSArray (x :: xs)) = x
index (fS i) (JSArray (x :: xs)) = index i (JSArray xs)

infixl 8 ++

(++) : JSON (JSONArray m ts1) ->
       JSON (JSONArray n ts2) ->
       JSON (JSONArray (m + n) (ts1 ++ ts2))
(++) (JSArray [])        ys = ys
(++) (JSArray (x :: xs)) ys with ((JSArray xs) ++ ys)
   | (JSArray as) = JSArray (x :: as)

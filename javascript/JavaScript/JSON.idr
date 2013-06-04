module JSON

import Data.SortedMap

data JSONType : Type where
  JSONArray  : Vect JSONType n -> JSONType
  JSONString : JSONType
  JSONNumber : JSONType
  JSONBool   : JSONType
  JSONObject : SortedMap String JSONType -> JSONType
  JSONNull   : JSONType

mutual
  using (ts : Vect JSONType n, fs : SortedMap String JSONType)
    namespace JArray
      data JArray : Vect JSONType n -> Type where
        Nil  : JArray []
        (::) : JSON t -> JArray ts -> JArray (t :: ts)

    namespace JObject
      data JObject : SortedMap String JSONType -> Type where
        Nil  : JObject empty
        (::) : (f : (String, JSON t)) -> JObject fs -> JObject (insert (fst f) t fs) 

    data JSON : JSONType -> Type where
      JSString : String -> JSON JSONString
      JSNumber : Float -> JSON JSONNumber
      JSBool   : Bool -> JSON JSONBool
      JSNull   : JSON JSONNull
      JSArray  : JArray ts -> JSON (JSONArray ts)
      JSObject : JObject fs -> JSON (JSONObject fs)

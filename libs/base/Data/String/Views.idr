module Data.String.Views

%access public export

||| View for traversing a String one character at a time
data StrList : String -> Type where
     SNil  : StrList ""
     SCons : (x : Char) -> (rec : StrList xs) -> StrList (strCons x xs)

||| Covering function for `StrList`
strList : (x : String) -> StrList x
strList x with (strM x)
  strList "" | StrNil = SNil
  strList (strCons y xs) | (StrCons y xs) 
          = assert_total $ SCons y (strList xs)

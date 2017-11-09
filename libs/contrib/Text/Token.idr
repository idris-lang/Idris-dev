module Text.Token

%access public export
%default total

||| For a type `kind`, specify a way of converting the recognised
||| string into a value.
|||
||| ```idris example
||| data SimpleKind = SKString | SKInt | SKComma
|||
||| TokenKind SimpleKind where
|||   tokType SKString = String
|||   tokType SKInt = Int
|||   tokType SKComma = ()
|||
|||   tokValue SKString x = x
|||   tokValue SKInt x = cast x
|||   tokValue SKComma x = ()
||| ```
interface TokenKind (k : Type) where
  ||| The type that a token of this kind converts to.
  tokType : k -> Type

  ||| Convert a recognised string into a value. The type is determined
  ||| by the kind of token.
  tokValue : (kind : k) -> String -> tokType kind

||| A token of a particular kind and the text that was recognised.
record Token k where
  constructor Tok
  kind : k
  text : String

||| Get the value of a `Token k`. The resulting type depends upon
||| the kind of token.
value : TokenKind k => (t : Token k) -> tokType (kind t)
value (Tok k x) = tokValue k x

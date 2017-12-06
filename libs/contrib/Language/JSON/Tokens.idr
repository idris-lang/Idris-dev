module Language.JSON.Tokens

import Language.JSON.String
import Text.Token

%access public export
%default total

strTrue : String
strTrue = "true"

strFalse : String
strFalse = "false"

data Bracket = Open | Close

Eq Bracket where
  (==) Open Open = True
  (==) Close Close = True
  (==) _ _ = False

data Punctuation
  = Comma
  | Colon
  | Square Bracket
  | Curly Bracket

Eq Punctuation where
  (==) Comma Comma = True
  (==) Colon Colon = True
  (==) (Square b1) (Square b2) = b1 == b2
  (==) (Curly b1) (Curly b2) = b1 == b2
  (==) _ _ = False

data JSONTokenKind
  = JTBoolean
  | JTNumber
  | JTString
  | JTNull
  | JTPunct Punctuation
  | JTIgnore

JSONToken : Type
JSONToken = Token JSONTokenKind

Eq JSONTokenKind where
  (==) JTBoolean JTBoolean = True
  (==) JTNumber JTNumber = True
  (==) JTString JTString = True
  (==) JTNull JTNull = True
  (==) (JTPunct p1) (JTPunct p2) = p1 == p2
  (==) _ _ = False

TokenKind JSONTokenKind where
  TokType JTBoolean = Bool
  TokType JTNumber = Double
  TokType JTString = Maybe String
  TokType JTNull = ()
  TokType (JTPunct _) = ()
  TokType JTIgnore = ()

  tokValue JTBoolean x = x == strTrue
  tokValue JTNumber x = cast x
  tokValue JTString x = stringValue x
  tokValue JTNull _ = ()
  tokValue (JTPunct _) _ = ()
  tokValue JTIgnore _ = ()

export
ignored : JSONToken -> Bool
ignored (Tok JTIgnore _) = True
ignored _ = False

module Language.JSON.String.Tokens

import Data.String.Extra
import Text.Token

%access public export
%default total

data JSONStringTokenKind
  = JSTQuote
  | JSTChar
  | JSTSimpleEscape
  | JSTUnicodeEscape

JSONStringToken : Type
JSONStringToken = Token JSONStringTokenKind

Eq JSONStringTokenKind where
  (==) JSTQuote JSTQuote = True
  (==) JSTChar JSTChar = True
  (==) JSTSimpleEscape JSTSimpleEscape = True
  (==) JSTUnicodeEscape JSTUnicodeEscape = True
  (==) _ _ = False

private
charValue : String -> Char
charValue x = case index 0 x of
                   Nothing => '\NUL'
                   Just c  => c

private
simpleEscapeValue : String -> Char
simpleEscapeValue x
  = case index 1 x of
         Nothing => '\NUL'
         Just c => case c of
                        '"'  => '"'
                        '\\' => '\\'
                        '/'  => '/'
                        'b'  => '\b'
                        'f'  => '\f'
                        'n'  => '\n'
                        'r'  => '\r'
                        't'  => '\t'
                        _    => '\NUL'

private
unicodeEscapeValue : String -> Char
unicodeEscapeValue x = chr $ cast ("0x" ++ drop 2 x)

TokenKind JSONStringTokenKind where
  TokType JSTQuote = ()
  TokType JSTChar = Char
  TokType JSTSimpleEscape = Char
  TokType JSTUnicodeEscape = Char

  tokValue JSTQuote = const ()
  tokValue JSTChar = charValue
  tokValue JSTSimpleEscape = simpleEscapeValue
  tokValue JSTUnicodeEscape = unicodeEscapeValue

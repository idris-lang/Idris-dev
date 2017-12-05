module Language.JSON.String.Lexer

import Language.JSON.String.Tokens
import Text.Lexer

%access private
%default total

export
quo : Lexer
quo = is '"'

export
esc : Lexer -> Lexer
esc = escape '\\'

unicodeEscape : Lexer
unicodeEscape = esc $ is 'u' <+> count (exactly 4) hexDigit

simpleEscape : Lexer
simpleEscape = esc $ oneOf "\"\\/bfnrt"

legalChar : Lexer
legalChar = non (quo <|> is '\\' <|> control)

jsonStringTokenMap : TokenMap JSONStringToken
jsonStringTokenMap = toTokenMap $
  [ (quo, JSTQuote)
  , (unicodeEscape, JSTUnicodeEscape)
  , (simpleEscape, JSTSimpleEscape)
  , (legalChar, JSTChar)
  ]

export
lexString : String -> Maybe (List JSONStringToken)
lexString x = case lex jsonStringTokenMap x of
                   (toks, _, _, "") => Just $ map TokenData.tok toks
                   _ => Nothing

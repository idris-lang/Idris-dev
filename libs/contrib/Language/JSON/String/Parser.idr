module Language.JSON.String.Parser

import Language.JSON.String.Tokens
import Text.Lexer
import Text.Parser

%access private
%default total

stringChar : Grammar JSONStringToken True Char
stringChar = match JSTChar
         <|> match JSTSimpleEscape
         <|> match JSTUnicodeEscape

quotedString : Grammar JSONStringToken True String
quotedString = let q = match JSTQuote in
                   do chars <- between q q (many stringChar)
                      eof
                      pure $ pack chars

export
parseString : List JSONStringToken -> Maybe String
parseString toks = case parse quotedString toks of
                        Right (str, []) => Just str
                        _ => Nothing

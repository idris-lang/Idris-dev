||| Commonly used characters
module Text.PrettyPrint.WL.Characters

import Text.PrettyPrint.WL.Core

%default total
%access export

lparen : Doc
lparen = char '('

rparen : Doc
rparen = char ')'

langle : Doc
langle = char '<'

rangle : Doc
rangle = char '>'

lbrace : Doc
lbrace = char '{'

rbrace : Doc
rbrace = char '}'

lbracket : Doc
lbracket = char '['

rbracket : Doc
rbracket = char ']'

squote : Doc
squote = char '\''

dquote : Doc
dquote = char '"'

semi : Doc
semi = char ';'

colon : Doc
colon = char ':'

comma : Doc
comma = char ','

space : Doc
space = char ' '

dot : Doc
dot = char '.'

backslash : Doc
backslash = char '\\'

forwardslash : Doc
forwardslash = char '/'

equals : Doc
equals = char '='

pipe : Doc
pipe = char '|'

bang : Doc
bang = char '!'

tick : Doc
tick = char '`'

tilde : Doc
tilde = char '~'

hash : Doc
hash = char '#'

asterix : Doc
asterix = char '*'

ampersand : Doc
ampersand = char '&'

dash : Doc
dash = char '-'

question : Doc
question = char '?'

dollar : Doc
dollar = char '$'

pound : Doc
pound = char '£'

euro : Doc
euro = char '€'

caret : Doc
caret = char '^'

percent : Doc
percent = char '%'

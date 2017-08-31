module Text.Lexer

%default total

||| A language of token recognisers.
||| The `consumes` flag is True is the recogniser is guaranteed to consume
||| at least one character
export
data Recognise : (consumes : Bool) -> Type where
     Empty : Recognise False
     Fail : Recognise c
     Pred : (Char -> Bool) -> Recognise True
     SeqEat : Recognise True -> Inf (Recognise e) -> Recognise True
     SeqEmpty : Recognise e1 -> Recognise e2 -> Recognise (e1 || e2)
     Alt : Recognise e1 -> Recognise e2 -> Recognise (e1 && e2)

||| A token recogniser. Guaranteed to consume at least one character.
public export
Lexer : Type
Lexer = Recognise True

public export
inf : Bool -> Type -> Type
inf True t = Inf t
inf False t = t

||| Sequence two recognisers. If either consumes a character, the sequence
||| is guaranteed to consume a character.
export %inline
(<+>) : {c1 : Bool} ->
        Recognise c1 -> inf c1 (Recognise c2) -> Recognise (c1 || c2)
(<+>) {c1 = False} = SeqEmpty
(<+>) {c1 = True} = SeqEat

||| Alternative recognisers. If both consume, the combination is guaranteed
||| to consumer a character.
export
(<|>) : Recognise c1 -> Recognise c2 -> Recognise (c1 && c2)
(<|>) = Alt

||| Recognise a specific character
export
is : Char -> Lexer
is x = Pred (==x)

||| Recognise anything but the given character
export
isNot : Char -> Lexer
isNot x = Pred (/=x)

||| Recognise a lexer or recognise no input. This is not guaranteed
||| to consume input
export
opt : Lexer -> Recognise False
opt l = l <|> Empty

||| Recognise a sequence of at least one sub-lexers
export
some : Lexer -> Lexer
some l = l <+> opt (some l)

||| Recognise a sequence of at zero or more sub-lexers. This is not
||| guaranteed to consume input
export
many : Lexer -> Recognise False
many l = opt (some l)

||| Recognise the first matching lexer from a non-empty list.
export
choice : (xs : List Lexer) -> {auto ok : NonEmpty xs} -> Lexer
choice (x :: [])          = x
choice (x :: xs@(_ :: _)) = x <|> choice xs

||| Recognise many instances of `l` until an instance of `end` is
||| encountered.
|||
||| Useful for defining comments.
export
manyTill : (l : Lexer) -> (end : Lexer) -> Recognise False
manyTill l end = end <|> opt (l <+> manyTill l end)

||| Recognise any character
export
any : Lexer
any = Pred (const True)

||| Recognise no input (doesn't consume any input)
export
empty : Recognise False
empty = Empty

||| Recognise a character that matches a predicate
export
pred : (Char -> Bool) -> Lexer
pred = Pred

||| Recognise any of the characters in the given string
export
oneOf : String -> Lexer
oneOf cs = pred (\x => x `elem` unpack cs)

data StrLen : Type where
     MkStrLen : String -> Nat -> StrLen

getString : StrLen -> String
getString (MkStrLen str n) = str

strIndex : StrLen -> Nat -> Maybe Char
strIndex (MkStrLen str len) i
    = if i >= len then Nothing
                  else Just (assert_total (prim__strIndex str (cast i)))

mkStr : String -> StrLen
mkStr str = MkStrLen str (length str)

strTail : Nat -> StrLen -> StrLen
strTail start (MkStrLen str len)
    = MkStrLen (substr start len str) (minus len start)

-- If the string is recognised, returns the index at which the token
-- ends
scan : Recognise c -> Nat -> StrLen -> Maybe Nat
scan Empty idx str = pure idx
scan Fail idx str = Nothing
scan (Pred f) idx str
    = do c <- strIndex str idx
         if f c
            then Just (idx + 1)
            else Nothing
scan (SeqEat r1 r2) idx str
    = do idx' <- scan r1 idx str
         -- TODO: Can we prove totality instead by showing idx has increased?
         assert_total (scan r2 idx' str)
scan (SeqEmpty r1 r2) idx str
    = do idx' <- scan r1 idx str
         scan r2 idx' str
scan (Alt r1 r2) idx str
    = case scan r1 idx str of
           Nothing => scan r2 idx str
           Just idx => Just idx

takeToken : Lexer -> StrLen -> Maybe (String, StrLen)
takeToken lex str
    = do i <- scan lex 0 str -- i must be > 0 if successful
         pure (substr 0 i (getString str), strTail i str)

||| Recognise a digit 0-9
export
digits : Lexer
digits = some (Pred isDigit)

||| Recognise a specific string
export
exact : String -> Lexer
exact str with (unpack str)
  exact str | [] = Fail -- Not allowed, Lexer has to consume
  exact str | (x :: xs)
      = foldl SeqEmpty (is x) (map is xs)

||| Recognise a whitespace character
export
space : Lexer
space = some (pred isSpace)

||| Recognise a non-alphanumeric, non-whitespace character
export
symbol : Lexer
symbol = some (pred (\x => not (isAlphaNum x) && not (isSpace x)))

||| Recognise zero or more occurrences of a sub-lexer between
||| delimiting lexers
export
surround : (start : Lexer) -> (end : Lexer) -> (l : Lexer) -> Lexer
surround start end l = start <+> manyTill l end

||| Recognise zero or more occurrences of a sub-lexer surrounded
||| by the same quote lexer on both sides (useful for strings)
export
quote : (q : Lexer) -> (l : Lexer) -> Lexer
quote q l = surround q q l

||| Recognise an escape character (such as `'\\'`) followed by a sub-lexer.
export
escape : (c : Char) -> Lexer -> Lexer
escape c l = is c <+> l

||| Recognise a sub-lexer escaped by `'\\'`.
||| Prefer using `escape` to changing the implicit argument of
||| this function.
||| @ c The escape character
export
escaped : {default '\\' c : Char} -> Lexer -> Lexer
escaped {c} l = escape c l

||| Recognise a string literal, including escape sequences.
||| Customisable using implicit arguments.
||| @ q   The quote character
||| @ ql  The quote lexer. Overrides quote character if passed
||| @ c   The escape character
||| @ esc Sub-lexer that can follow an escape character
export
stringLit : {default '"' q : Lexer} -> {default (is q) ql : Lexer} ->
            {default '\\' c : Char} -> {default any esc : Lexer} ->
            Lexer
stringLit {ql} {c} {esc} = quote ql (escape c esc <|> any)

||| Recognise a character literal, including escape sequences.
||| Customisable using implicit arguments.
||| @ q   The quote character
||| @ c   The escape character
||| @ esc Sub-lexer that can follow an escape character
export
charLit : {default '\'' q : Char} ->
          {default '\\' c : Char} -> {default any esc : Lexer} ->
          Lexer
charLit {q} {c} {esc} = is q <+> (escape c esc <|> isNot q) <+> is q

||| Recognise an integer literal preceded by an optional sign.
||| Customisable using implicit arguments.
||| @ sign A sign lexer that can optionally appear before the digits
export
intLit : {default (is '-') sign : Lexer} -> Lexer
intLit {sign} = opt sign <+> digits

||| A mapping from lexers to the tokens they produce.
||| This is a list of pairs `(Lexer, String -> tokenType)`
||| For each Lexer in the list, if a substring in the input matches, run
||| the associated function to produce a token of type `tokenType`
public export
TokenMap : (tokenType : Type) -> Type
TokenMap tokenType = List (Lexer, String -> tokenType)

||| A token, and the line and column where it was in the input
public export
record TokenData a where
  constructor MkToken
  line : Int
  col : Int
  tok : a

fspanEnd : Nat -> (Char -> Bool) -> String -> (Nat, String)
fspanEnd k p "" = (k, "")
fspanEnd k p xxs
    = assert_total $
      let x = prim__strHead xxs
          xs = prim__strTail xxs in
          if p x then fspanEnd (S k) p xs
                 else (k, xxs)

-- Faster version of 'span' from the prelude (avoids unpacking)
export
fspan : (Char -> Bool) -> String -> (String, String)
fspan p xs
    = let (end, rest) = fspanEnd 0 p xs in
          (substr 0 end xs, rest)

tokenise : (line : Int) -> (col : Int) ->
           List (TokenData a) -> TokenMap a ->
           StrLen -> (List (TokenData a), (Int, Int, StrLen))
tokenise line col acc tmap str
    = case getFirstToken tmap str of
           Just (tok, line', col', rest) =>
           -- assert total because getFirstToken must consume something
                assert_total (tokenise line' col' (tok :: acc) tmap rest)
           Nothing => (reverse acc, (line, col, str))
  where
    countNLs : List Char -> Nat
    countNLs str = List.length (filter (== '\n') str)

    getCols : String -> Int -> Int
    getCols x c
         = case fspan (/= '\n') (reverse x) of
                (incol, "") => c + cast (length incol)
                (incol, _) => cast (length incol)

    getFirstToken : TokenMap a -> StrLen -> Maybe (TokenData a, Int, Int, StrLen)
    getFirstToken [] str = Nothing
    getFirstToken ((lex, fn) :: ts) str
        = case takeToken lex str of
               Just (tok, rest) => Just (MkToken line col (fn tok),
                                         line + cast (countNLs (unpack tok)),
                                         getCols tok col, rest)
               Nothing => getFirstToken ts str

||| Given a mapping from lexers to token generating functions (the
||| TokenMap a) and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in the
||| string where there are no recognised tokens.
export
lex : TokenMap a -> String -> (List (TokenData a), (Int, Int, String))
lex tmap str = let (ts, (l, c, str')) = tokenise 0 0 [] tmap (mkStr str) in
                   (ts, (l, c, getString str'))

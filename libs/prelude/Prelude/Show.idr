module Prelude.Show

import Builtins

import Prelude.Basics
import Prelude.Bits
import Prelude.Bool
import Prelude.Cast
import Prelude.Chars
import Prelude.Classes
import Prelude.List
import Prelude.Maybe
import Prelude.Nat
import Prelude.Strings

%default total

||| The precedence of an Idris operator or syntactic context.
data Prec = Open | Eq | Dollar | Backtick | User Nat | PrefixMinus | App

||| Gives the constructor index of the Prec as a helper for writing instances.
precCon : Prec -> Integer
precCon Open        = 0
precCon Eq          = 1
precCon Dollar      = 2
precCon Backtick    = 3
precCon (User n)    = 4
precCon PrefixMinus = 5
precCon App         = 6

instance Eq Prec where
  (==) (User m) (User n) = m == n
  (==) x        y        = precCon x == precCon y

instance Ord Prec where
  compare (User m) (User n) = compare m n
  compare x        y        = compare (precCon x) (precCon y)

||| Things that have a canonical `String` representation.
class Show a where
  ||| Convert a value to its `String` representation.
  |||
  ||| @ a the value to convert
  partial
  show : (x : a) -> String
  show = showPrec Open

  ||| Convert a value to its `String` representation in a certain precedence
  ||| context.
  |||
  ||| A value should produce parentheses around itself if and only if the given
  ||| precedence context is greater than or equal to the precedence of the
  ||| outermost operation represented in the produced `String`. *This is
  ||| different from Haskell*, which requires it to be strictly greater. `Open`
  ||| should thus always produce *no* outermost parens, `App` should always
  ||| produce outermost parens except on atomic values and those that provide
  ||| their own bracketing, like `Pair` and `List`.
  |||
  ||| @ d the precedence context.
  ||| @ a the value to convert
  partial
  showPrec : (d : Prec) -> (x : a) -> String
  showPrec _ = show

||| Surround a `String` with parentheses depending on a condition.
|||
||| @ b whether to add parentheses
showParens : (b : Bool) -> String -> String
showParens False s = s
showParens True  s = "(" ++ s ++ ")"

||| A helper for the common case of showing a non-infix constructor with at
||| least one argument, for use with `showArg`.
|||
||| Apply `showCon` to the precedence context, the constructor name, and the
||| args shown with `showArg` and concatenated. Example:
||| ```
||| data Ann a = MkAnn String a
|||
||| instance Show a => Show (Ann a) where
|||   showPrec d (MkAnn s x) = showCon d "MkAnn" $ showArg s ++ showArg x
||| ```
showCon : (d : Prec) -> (conName : String) -> (shownArgs : String) -> String
showCon d conName shownArgs = showParens (d >= App) $ conName ++ shownArgs

||| A helper for the common case of showing a non-infix constructor with at
||| least one argument, for use with `showCon`.
|||
||| This adds a space to the front so the results can be directly
||| concatenated. See `showCon` for details and an example.
showArg : Show a => (x : a) -> String
showArg x = " " ++ showPrec App x

instance Show Int where
  show = prim__toStrInt

instance Show Integer where
  show = prim__toStrBigInt

instance Show Double where
  show = prim__floatToStr

firstCharIs : (Char -> Bool) -> String -> Bool
firstCharIs p s with (strM s)
  firstCharIs p ""             | StrNil = False
  firstCharIs p (strCons c cs) | StrCons c cs = p c

protectEsc : (Char -> Bool) -> String -> String -> String
protectEsc p f s = f ++ (if firstCharIs p s then "\\&" else "") ++ s

showLitChar : Char -> String -> String
showLitChar '\a'   = ("\\a" ++)
showLitChar '\b'   = ("\\b" ++)
showLitChar '\f'   = ("\\f" ++)
showLitChar '\n'   = ("\\n" ++)
showLitChar '\r'   = ("\\r" ++)
showLitChar '\t'   = ("\\t" ++)
showLitChar '\v'   = ("\\v" ++)
showLitChar '\SO'  = protectEsc (== 'H') "\\SO"
showLitChar '\DEL' = ("\\DEL" ++)
showLitChar '\\'   = ("\\\\" ++)
showLitChar c      = case getAt (cast (cast {to=Int} c)) asciiTab of
                          Just k => strCons '\\' . (k ++)
                          Nothing => if (c > '\DEL')
                                        then strCons '\\' . protectEsc isDigit (show (cast {to=Int} c))
                                        else strCons c
  where asciiTab : List String
        asciiTab = ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
                    "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI",
                    "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
                    "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US"]

        getAt : Nat -> List String -> Maybe String
        getAt Z     (x :: xs) = Just x
        getAt (S k) (x :: xs) = getAt k xs
        getAt _     []        = Nothing

showLitString : List Char -> String -> String
showLitString []        = id
showLitString ('"'::cs) = ("\\\"" ++) . showLitString cs
showLitString (c  ::cs) = showLitChar c . showLitString cs

instance Show Char where
  show '\'' = "'\\''"
  show c    = strCons '\'' (showLitChar c "'")

instance Show String where
  show cs = strCons '"' (showLitString (cast cs) "\"")

instance Show Nat where
    show n = show (the Integer (cast n))

instance Show Bool where
    show True = "True"
    show False = "False"

instance Show () where
  show () = "()"

instance Show Bits8 where
  show b = b8ToString b

instance Show Bits16 where
  show b = b16ToString b

instance Show Bits32 where
  show b = b32ToString b

instance Show Bits64 where
  show b = b64ToString b

instance (Show a, Show b) => Show (a, b) where
    show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

instance Show a => Show (List a) where
    show xs = "[" ++ show' "" xs ++ "]" where
        show' acc []        = acc
        show' acc [x]       = acc ++ show x
        show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

instance Show a => Show (Maybe a) where
  showPrec d Nothing  = "Nothing"
  showPrec d (Just x) = showCon d "Just" $ showArg x

instance (Show a, {y : a} -> Show (p y)) => Show (Sigma a p) where
    show (y ** prf) = "(" ++ show y ++ " ** " ++ show prf ++ ")"


module Prelude.Show

import Builtins

import Prelude.Basics
import Prelude.Bits
import Prelude.Bool
import Prelude.Cast
import Prelude.Chars
import Prelude.Interfaces
import Prelude.List
import Prelude.Maybe
import Prelude.Either
import Prelude.Nat
import Prelude.Strings

%access public export

%default total

||| The precedence of an Idris operator or syntactic context.
data Prec = Open | Eq | Dollar | Backtick | User Nat | PrefixMinus | App

||| Gives the constructor index of the Prec as a helper for writing implementations.
precCon : Prec -> Integer
precCon Open        = 0
precCon Eq          = 1
precCon Dollar      = 2
precCon Backtick    = 3
precCon (User n)    = 4
precCon PrefixMinus = 5
precCon App         = 6

Eq Prec where
  (==) (User m) (User n) = m == n
  (==) x        y        = precCon x == precCon y

Ord Prec where
  compare (User m) (User n) = compare m n
  compare x        y        = compare (precCon x) (precCon y)

||| Things that have a canonical `String` representation.
interface Show ty where
  ||| Convert a value to its `String` representation.
  |||
  ||| @ x the value to convert
  partial
  show : (x : ty) -> String
  show x = showPrec Open x -- Eta expand to help totality checker

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
  ||| @ x the value to convert
  partial
  showPrec : (d : Prec) -> (x : ty) -> String
  showPrec _ x = show x

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
||| Show a => Show (Ann a) where
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

firstCharIs : (Char -> Bool) -> String -> Bool
firstCharIs p s with (strM s)
  firstCharIs p ""             | StrNil = False
  firstCharIs p (strCons c cs) | StrCons c cs = p c

primNumShow : (a -> String) -> Prec -> a -> String
primNumShow f d x = let str = f x in showParens (d >= PrefixMinus && firstCharIs (== '-') str) str

Show Int where
  showPrec = primNumShow prim__toStrInt

Show Integer where
  showPrec = primNumShow prim__toStrBigInt

Show Double where
  showPrec = primNumShow prim__floatToStr

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

Show Char where
  show '\'' = "'\\''"
  show c    = strCons '\'' (showLitChar c "'")

Show String where
  show cs = strCons '"' (showLitString (cast cs) "\"")

Show Nat where
    show n = show (the Integer (cast n))

Show Bool where
    show True = "True"
    show False = "False"

Show () where
  show () = "()"

Show Bits8 where
  show b = b8ToHexString b

Show Bits16 where
  show b = b16ToHexString b

Show Bits32 where
  show b = b32ToHexString b

Show Bits64 where
  show b = b64ToHexString b

(Show a, Show b) => Show (a, b) where
    show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

Show a => Show (List a) where
    show xs = "[" ++ show' "" xs ++ "]" where
        show' acc []        = acc
        show' acc [x]       = acc ++ show x
        show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

Show a => Show (Maybe a) where
  showPrec d Nothing  = "Nothing"
  showPrec d (Just x) = showCon d "Just" $ showArg x

(Show a, Show b) => Show (Either a b) where
  showPrec d (Left x)  = showCon d "Left" $ showArg x
  showPrec d (Right x) = showCon d "Right" $ showArg x

(Show a, {y : a} -> Show (p y)) => Show (DPair a p) where
    show (y ** prf) = "(" ++ show y ++ " ** " ++ show prf ++ ")"

||| Common combinators.
module Text.PrettyPrint.WL.Combinators

import Text.PrettyPrint.WL.Core
import Text.PrettyPrint.WL.Characters

%default total
%access export

-- --------------------------------------------------- [ Alignment Combinators ]

||| The document `(align x)` renders document `x` with the nesting
||| level set to the current column. It is used for example to
||| implement 'hang'.
align : Doc -> Doc
align d = column (\k => nesting (\i => nest (k - i) d))

||| The hang combinator implements hanging indentation. The document
||| `(hang i x)` renders document `x` with a nesting level set to the
||| current column plus `i`.
hang : Int -> Doc -> Doc
hang i d = align (nest i d)

||| The document `(indent i x)` indents document `x` with `i` spaces.
indent : Int -> Doc -> Doc
indent i d = hang i (text (spaces i) <+> d)

-- -------------------------------------------------- [ High-Level Combinators ]

||| The document `softLine` behaves like `space` if the resulting
||| output fits the page, otherwise it behaves like `line`.
softLine : Doc
softLine = group line

||| The document `softbreak` behaves like `empty` if the resulting
||| output fits the page, otherwise it behaves like 'line'.
softBreak : Doc
softBreak = group breakLine

infixr 5 |/|, |//|, |$|, |$$|
infixr 6 |+|, |++|

private
concatDoc : Doc -> Doc -> Doc -> Doc
concatDoc sep x y = x `beside` (sep `beside` y)

||| The document `(x |+| y)` concatenates document `x` and document
||| `y`. It is an associative operation having 'empty' as a left and
||| right unit.
(|+|) : Doc -> Doc -> Doc
(|+|) = (<+>)

||| The document `(x |++| y)` concatenates document `x` and `y` with a
||| `space` in between.
(|++|) : Doc -> Doc -> Doc
(|++|) = concatDoc space

||| The document `(x |/| y)` concatenates document `x` and `y` with a
||| 'softline' in between. This effectively puts `x` and `y` either
||| next to each other (with a `space` in between) or underneath each
||| other.
(|/|) : Doc -> Doc -> Doc
(|/|) = concatDoc softLine

||| The document `(x |//| y)` concatenates document `x` and `y` with
||| a 'softbreak' in between. This effectively puts `x` and `y` either
||| right next to each other or underneath each other.
(|//|) : Doc -> Doc -> Doc
(|//|) = concatDoc softBreak

||| The document `(x |$| y)` concatenates document `x` and `y` with a
||| `line` in between.
(|$|) : Doc -> Doc -> Doc
(|$|) = concatDoc line

||| The document `(x |$$| y)` concatenates document `x` and `y` with
||| a `linebreak` in between.
(|$$|) : Doc -> Doc -> Doc
(|$$|) = concatDoc breakLine

||| The document `(vsep xs)` concatenates all documents `xs`
||| vertically with `(|$|)`. If a 'group' undoes the line breaks
||| inserted by `vsep`, all documents are separated with a space.
vsep : List Doc -> Doc
vsep = fold (|$|)

||| The document `(sep xs)` concatenates all documents `xs` either
||| horizontally with `(|++|)`, if it fits the page, or vertically with
||| `(|$|)`.
sep : List Doc -> Doc
sep = group . vsep


||| The document `(fillSep xs)` concatenates documents `xs`
||| horizontally with `(|++|)` as long as its fits the page, than
||| inserts a `line` and continues doing that for all documents in
||| `xs`.
fillSep : List Doc -> Doc
fillSep = fold (|/|)

||| The document `(hsep xs)` concatenates all documents `xs`
||| horizontally with `(|++|)`.
hsep : List Doc -> Doc
hsep = fold (|++|)

||| The document `(hcat xs)` concatenates all documents `xs`
||| horizontally with `(|+|)`.
hcat : List Doc -> Doc
hcat = fold (<+>)

||| The document `(vcat xs)` concatenates all documents `xs`
||| vertically with `(|$$|)`. If a `group` undoes the line breaks
||| inserted by `vcat`, all documents are directly concatenated.
vcat : List Doc -> Doc
vcat = fold (|$$|)

||| The document `(cat xs)` concatenates all documents `xs` either
||| horizontally with `(|+|)`, if it fits the page, or vertically with
||| `(|$$|)`.
cat : List Doc -> Doc
cat = group . vcat

||| The document `(fillCat xs)` concatenates documents `xs`
||| horizontally with `(|+|)` as long as its fits the page, than inserts
||| a `linebreak` and continues doing that for all documents in `xs`.
fillCat : List Doc -> Doc
fillCat = fold (|//|)

||| The document `(enclose l r x)` encloses document `x` between
||| documents `l` and `r` using `(|+|)`.
enclose : Doc -> Doc -> Doc -> Doc
enclose l r x = concatDoc x l r

squotes : Doc -> Doc
squotes = enclose squote squote

dquotes : Doc -> Doc
dquotes = enclose dquote dquote

braces : Doc -> Doc
braces = enclose lbrace rbrace

parens : Doc -> Doc
parens = enclose lparen rparen

angles : Doc -> Doc
angles = enclose langle rangle

brackets : Doc -> Doc
brackets = enclose lbracket rbracket

-- ----------------------------------------------------- [ Lists, Sets, Tuples ]

||| The document `(encloseSep l r sep xs)` concatenates the documents
||| `xs` separated by `sep` and encloses the resulting document by `l`
||| and `r`. The documents are rendered horizontally if that fits the
||| page. Otherwise they are aligned vertically. All separators are put
||| in front of the elements.
encloseSep : (l   : Doc)
          -> (r   : Doc)
          -> (sep : Doc)
          -> (xs  : List Doc)
          -> Doc
encloseSep l r s []  = l <+> r
encloseSep l r s [x] = l <+> x <+> r
encloseSep l r s xs  = align (cat (zipWith (<+>) (l :: replicate (length xs) s) xs) <+> r)

||| The document `(list xs)` comma separates the documents `xs` and
||| encloses them in square brackets. The documents are rendered
||| horizontally if that fits the page. Otherwise they are aligned
||| vertically. All comma separators are put in front of the
||| elements.
list : List Doc -> Doc
list = encloseSep lbracket rbracket comma

||| The document `(tupled xs)` comma separates the documents `xs`
||| and encloses them in parenthesis. The documents are rendered
||| horizontally if that fits the page. Otherwise they are aligned
||| vertically. All comma separators are put in front of the
||| elements.
tupled : List Doc -> Doc
tupled = encloseSep lparen rparen comma

||| The document `(set xs)` separates the documents `xs` with
||| commas and encloses them in braces. The documents are
||| rendered horizontally if that fits the page. Otherwise they are
||| aligned vertically. All comma's are put in front of the
||| elements.
set : List Doc -> Doc
set = encloseSep lbrace rbrace comma

||| The document `(semiBraces xs)` separates the documents `xs` with
||| semi-colon and encloses them in braces. The documents are
||| rendered horizontally if that fits the page. Otherwise they are
||| aligned vertically. All semi-colons's are put in front of the
||| elements.
semiBrace : List Doc -> Doc
semiBrace = encloseSep lbrace rbrace semi

||| `(punctuate p xs)` concatenates all documents in `xs` with
||| document `p` except for the last document.
punctuate : Doc -> List Doc -> List Doc
punctuate p []  = []
punctuate p [x] = [x]
punctuate p (x :: xs) = (x <+> p) :: punctuate p xs

-- ------------------------------------------------------------------- [ Fills ]

width : Doc -> (Int -> Doc) -> Doc
width doc f = column (\k => doc <+> column (\k' => f (k' - k)))

||| The document `(fillBreak i x)` first renders document `x`. It
||| than appends `space`s until the width is equal to `i`. If the
||| width of `x` is already larger than `i`, the nesting level is
||| increased by `i` and a `line` is appended.
fillBreak : (i : Int) -> (x : Doc) -> Doc
fillBreak f x =
  width x (\w => if (w > f)
                  then nest f breakLine
                  else text (spaces (f - w)))

||| The document `(fill i x)` renders document `x`. It than appends
||| `space`s until the width is equal to `i`. If the width of `x` is
||| already larger, nothing is appended. This combinator is quite
||| useful in practice to output a list of bindings.
fill : (i : Int) -> (x : Doc) -> Doc
fill f d =
  width d (\w => if (w >= f)
                    then empty
                    else text (spaces (f - w)))

-- -------------------------------------------------------------- [ Primatives ]

||| The document `(literal s)` concatenates all characters in `s`
||| using `line` for newline characters and `char` for all other
||| characters. It is used instead of 'text' whenever the text contains
||| newline characters.
literal : (str : String) -> Doc
literal str = mkLiteral (unpack str)
  where
    mkLiteral : List Char -> Doc
    mkLiteral Nil         = empty
    mkLiteral ('\n':: ss) = line <+> mkLiteral ss
    mkLiteral (c :: ss)   = char c <+> mkLiteral ss

bool : Bool -> Doc
bool b = text (show b)

nat : Nat -> Doc
nat n = text (show n)

int : Int -> Doc
int i = text (show i)

integer : Integer -> Doc
integer i = text (show i)

double : Double -> Doc
double d = text (show d)

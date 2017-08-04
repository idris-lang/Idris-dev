||| Core definitions and primitives.
module Text.PrettyPrint.WL.Core

%default total
%access export

-- -------------------------------------------------------------------- [ Core ]

||| The abstract data type `Doc` represents pretty documents.
|||
data Doc : Type where
  Empty : Doc
  Chara : (c : Char) -> Doc
  Text  : (len : Int) -> (str : String) -> Doc
  Line : (undone : Bool) -> Doc

  Cat     : (x : Doc) -> (y : Doc) -> Doc
  Nest    : (lvl : Int) -> (x : Doc) -> Doc
  Union   : (x : Doc) -> (y : Doc) -> Doc

  Column  : (f : Int -> Doc) -> Doc
  Nesting : (f : Int -> Doc) -> Doc

-- -------------------------------------------------------------- [ Primitives ]

||| The empty document is, indeed, empty.
empty : Doc
empty = Empty

||| The `line` document advances to the next line and indents to the
||| current nesting level. Document `line` behaves like `(text " ")`
||| if the line break is undone by 'group'.
line : Doc
line = Line False

||| The document `(char c)` contains the literal character `c`. If the
||| character is a newline (`'\n'`) the function returns a line
||| document. Ideally, the function 'line' should be used for line
||| breaks.
char : (c : Char) -> Doc
char '\n' = line
char c    = Chara c

||| The document `(text s)` contains the literal string `s`. The
||| string shouldn't contain any newline (`'\n'`) characters. If the
||| string contains newline characters, the function 'literal' should be
||| used.
text : (str : String) -> Doc
text ""  = empty
text str = Text (cast $ length str) str

||| The `breakLine` document advances to the next line and indents to
||| the current nesting level. Document `breakLine` behaves like
||| 'empty' if the line break is undone by 'group'.
breakLine : Doc
breakLine = Line True

||| Horizontal concatenation of documents
beside : Doc -> Doc -> Doc
beside = Cat

||| The document `(nest lvl x)` renders document `x` with the current
||| indentation level increased by lvl.
nest : (lvl : Int)
    -> (x   : Doc)
    -> Doc
nest = Nest

column : (f : Int -> Doc) -> Doc
column = Column

nesting : (f : Int -> Doc) -> Doc
nesting = Nesting

private %inline
flatten : Doc -> Doc
flatten (Line break)  = if break then Empty else Text 1 " "

flatten (Cat x y)    = Cat (flatten x) (flatten y)
flatten (Nest lvl x) = Nest lvl (flatten x)
flatten (Union x _)  = flatten x
flatten (Column f)   = Column  (\i => flatten $ f i)
flatten (Nesting f)  = Nesting (\i => flatten $ f i)

flatten other = other

||| The `group` combinator is used to specify alternative
||| layouts. The document `(group x)` undoes all line breaks in
||| document `x`. The resulting line is added to the current line if
||| that fits the page. Otherwise, the document `x` is rendered without
||| any changes.
group : Doc -> Doc
group x = Union (flatten x) x

Semigroup Doc where
  (<+>) x y = beside x y

Monoid Doc where
  neutral = empty

fold : (f : Doc -> Doc -> Doc) -> (ds : List Doc) -> Doc
fold _ Nil     = empty
fold f (x::xs) = foldl f x xs

-- --------------------------------------------------------------- [ Renderers ]

namespace PrettyDoc

  ||| The data type `PrettyDoc` represents rendered documents and is
  ||| used by the display functions.
  data PrettyDoc : Type where
    Empty : PrettyDoc
    Chara : (c : Char) -> (rest : PrettyDoc) -> PrettyDoc
    Text  : (len : Int) -> (str : String) -> (rest : PrettyDoc) -> PrettyDoc
    Line  : (lvl : Int) -> (rest : PrettyDoc) -> PrettyDoc

||| Helper function to construct spaces.
spaces : (n : Int) -> String
spaces n = if n <= 0 then "" else pack $ replicate (cast n) ' '

private
indentation : Int -> String
indentation n = spaces n

||| `(showPrettyDoc doc)` takes the output `PrettyDoc` from a
||| rendering function and transforms it to a String for printing.
showPrettyDoc : (doc : PrettyDoc) -> String
showPrettyDoc doc = showPrettyDocS doc ""
  where
    showPrettyDocS : (doc : PrettyDoc) -> (acc : String) -> String
    showPrettyDocS Empty               acc = acc
    showPrettyDocS (Chara c rest)      acc = strCons c (showPrettyDocS rest acc)
    showPrettyDocS (Text len str rest) acc = str ++ (showPrettyDocS rest acc)
    showPrettyDocS (Line lvl rest)     acc = (strCons '\n' (indentation lvl)) ++ showPrettyDocS rest acc

private
fits : (w : Int) -> (x : PrettyDoc) -> Bool
fits w Empty               = if w < 0 then False else True
fits w (Chara c rest)      = if w < 0 then False else fits (w - 1) rest

fits w (Text len str rest) = if w < 0 then False else fits (w - len) rest

fits w (Line _ _)          = if w < 0 then False else True


||| Use the Wadler-Leijen algorithm to pretty print the `doc`.
||| The algorithm uses a page width of `width` and a ribbon
||| width of `(ribbonfrac * width)` characters. The ribbon width is
||| the maximal amount of non-indentation characters on a line. The
||| parameter `ribbonfrac` should be between `0.0` and `1.0`. If it is
||| lower or higher, the ribbon width will be 0 or `width`
||| respectively.
render : (rfrac : Double)
      -> (width : Int)
      -> (doc : Doc)
      -> PrettyDoc
render rfrac w doc = best w 0 0 doc (const Empty)
  where
    rwidth : Int
    rwidth = max 0 $ min w (cast (cast w * rfrac))

    nicest : (lvl : Int)
          -> (col : Int)
          -> (x : PrettyDoc)
          -> (y : PrettyDoc)
          -> PrettyDoc
    nicest n k x y =
      let width = min (w - k) (rwidth - k + n)
       in if fits width x then x else y

    best : (lvl : Int)
        -> (col : Int)
        -> (curr : Int)
        -> (doc  : Doc)
        -> (k : Int -> PrettyDoc)
        -> PrettyDoc
    best lvl col curr Empty          k = k col
    best lvl col curr (Chara c)      k = Chara c $ k (col + 1)
    best lvl col curr (Text len str) k = Text len str $ k (col + len)
    best lvl col curr (Line undone)  k = Line curr $ k curr

    best lvl col curr (Cat x y) k =
        best lvl col curr x (\curr' => best lvl curr' curr y k)

    best lvl col curr (Nest x y) k = best lvl col (curr+x) y k

    best lvl col curr (Union x y) k =
        nicest lvl col (best lvl col curr x k)
                       (best lvl col curr y k)

    best lvl col curr (Column f)  k = best lvl col curr (f col) k
    best lvl col curr (Nesting f) k = best lvl col curr (f curr) k

||| Print the document to a string using the given ribbon fraction
||| and page width.
toString : (rfrac : Double)
        -> (width : Int)
        -> (doc : Doc)
        -> String
toString rfrac width doc = showPrettyDoc (render rfrac width doc)

writeDoc : (fname : String)
        -> (rfrac : Double)
        -> (width : Int)
        -> (doc : Doc)
        -> IO (Either FileError ())
writeDoc fname rfrac width doc = writeFile fname $ toString rfrac width doc

namespace Default

  ||| Render the document with a default ribbon fraction of 0.4 and page width of 120 characters.
  render : (doc : Doc) -> PrettyDoc
  render = render 0.4 120

  ||| Print the document to a string using a default ribbon fraction
  ||| of 0.4 and page width of 120 characters.
  toString : (doc : Doc) -> String
  toString = toString 0.4 120

  ||| Write the doc to `fname` using a default ribbon fraction of 0.4
  ||| and page width of 120 characters.
  writeDoc : (fname : String)
          -> (doc : Doc)
          -> IO (Either FileError ())
  writeDoc fname doc = writeFile fname $ Default.toString doc

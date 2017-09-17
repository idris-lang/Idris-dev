||| A simple module to process 'literate' documents.
|||
||| The module uses a lexer to split the document into code blocks,
||| delineated by user-defined markers, and code lines that are
||| indicated be a line marker. The lexer returns a document stripped
||| of non-code elements but preserving the original document's line
||| count. Column numbering of code lines are not preserved.
|||
||| The underlying tokeniser is greedy.
|||
||| Once it identifies a line marker it reads a prettifying space then
||| consumes until the end of line. Once identifies a starting code
||| block marker, the lexer will consume input until the next
||| identifiable end block is encountered. Any other content is
||| treated as part of the original document.
|||
||| Thus, the input literate files *must* be well-formed w.r.t
||| to code line markers and code blocks.
|||
||| A further restriction is that literate documents cannot contain
||| the markers within the document's main text: This will confuse the
||| lexer.
|||
module Text.Literate

import Text.Lexer

import Data.List.Views

%default total

untilEOL : Recognise False
untilEOL = manyUntil (is '\n') any

line : String -> Lexer
line s = exact s <+> space <+> untilEOL

block : String -> String -> Lexer
block s e = exact s <+> manyUntil (exact e) any 

data Token = CodeBlock String String String
           | Any String
           | CodeLine String String

Show Token where
  showPrec d (CodeBlock l r x) = showCon d "CodeBlock" $ showArg l ++ showArg r ++ showArg x
  showPrec d (Any x)           = showCon d "Any" $ showArg x
  showPrec d (CodeLine m x)    = showCon d "CodeLine" $ showArg m ++ showArg x

rawTokens : (delims  : List (String, String))
         -> (markers : List String)
         -> TokenMap (Token)
rawTokens delims ls =
          map (\(l,r) => (block l r, CodeBlock l r)) delims
       ++ map (\m => (line m, CodeLine m)) ls
       ++ [(any, Any)]

||| Merge the tokens into a single source file.
reduce : List (TokenData Token) -> String -> String
reduce [] acc = acc
reduce (MkToken _ _ (Any x) :: rest) acc = reduce rest (acc ++ blank_content)
  where
    -- Preserve the original document's line count.
    blank_content : String
    blank_content = if elem '\n' (unpack x)
      then concat $ replicate (length (lines x)) "\n"
      else ""
reduce (MkToken _ _ (CodeLine m src) :: rest) acc =
    reduce rest (acc ++ (substr
                           (length m + 1) -- remove space to right of marker.
                           (length src)
                           src))

reduce (MkToken _ _ (CodeBlock l r src) :: rest) acc with (lines src) -- Strip the deliminators surrounding the block.
  reduce (MkToken _ _ (CodeBlock l r src) :: rest) acc | [] = reduce rest acc -- 1
  reduce (MkToken _ _ (CodeBlock l r src) :: rest) acc | (s :: ys) with (snocList ys)
    reduce (MkToken _ _ (CodeBlock l r src) :: rest) acc | (s :: []) | Empty = reduce rest acc -- 2
    reduce (MkToken _ _ (CodeBlock l r src) :: rest) acc | (s :: (srcs ++ [f])) | (Snoc rec) =
        reduce rest (acc ++ "\n" ++ unlines srcs ++ "\n")

-- [ NOTE ] 1 & 2 shouldn't happen as code blocks are well formed i.e. have two deliminators.


public export
record LiterateError where
  constructor MkLitErr
  line   : Int
  column : Int
  input  : String

||| Description of literate styles.
|||
||| A 'literate' style comprises of
|||
||| + a list of code block deliminators (`deliminators`);
||| + a list of code line markers (`line_markers`); and
||| + a list of known file extensions `file_extensions`.
|||
||| Some example specifications:
|||
||| + Bird Style
|||
|||```
|||MkLitStyle Nil [">", "<"] Nil
|||```
|||
||| + Literate Haskell (for LaTeX)
|||
|||```
|||MkLitStyle [("\\begin{code}", "\\end{code}"),("\\begin{spec}","\\end{spec}")]
|||           Nil
|||           ["lhs", "tex"]
|||```
|||
||| + OrgMode
|||
|||```
|||MkLitStyle [("#+BEGIN_SRC idris","#+END_SRC"), ("#+COMMENT idris","#+END_COMMENT")]
|||           ["#+IDRIS:"]
|||           ["org"]
|||```
|||
public export
record LiterateStyle where
  constructor MkLitStyle
  ||| The pairs of start and end tags for code blocks.
  deliminators : List (String, String)

  ||| Line markers that indicate a line contains code.
  line_markers : List String

  ||| Recognised file extensions. Not used by the module, but will be
  ||| of use when connecting to code that reads in the original source
  ||| files.
  file_extensions : List String

||| Given a 'literate specification' extract the code from the
||| literate source file (`litStr`) that follows the presented style.
|||
||| @specification The literate specification to use.
||| @litStr  The literate source file.
|||
||| Returns a `LiterateError` if the literate file contains malformed
||| code blocks or code lines.
|||
export
extractCode : (specification : LiterateStyle)
           -> (litStr        : String)
           -> Either LiterateError String
extractCode (MkLitStyle delims markers exts) str =
      case lex (rawTokens delims markers) str of
        (toks, (_,_,"")) => Right $ reduce toks ""
        (_, (l,c,i))     => Left (MkLitErr l c i)

-- --------------------------------------------------------------------- [ EOF ]

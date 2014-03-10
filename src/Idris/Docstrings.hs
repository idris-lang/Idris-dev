-- | Wrapper around Markdown library
module Idris.Docstrings (
    Docstring, parseDocstring, renderDocstring, emptyDocstring, nullDocstring, noDocs
  ) where

import qualified Cheapskate as C
import qualified Cheapskate.Types as CT

import Util.Pretty

import Idris.Core.TT (OutputAnnotation, Name)

import qualified Data.Text as T
import qualified Data.Foldable as F
import qualified Data.Sequence as S

type Docstring = CT.Doc

parseDocstring :: T.Text -> CT.Doc
parseDocstring = C.markdown options


options = CT.Options { CT.sanitize = True
                     , CT.allowRawHtml = False
                     , CT.preserveHardBreaks = True
                     , CT.debug = False
                     }

renderDocstring ::  Docstring -> Doc OutputAnnotation
renderDocstring (CT.Doc _ blocks) = renderBlocks blocks

renderBlocks ::  CT.Blocks -> Doc OutputAnnotation
renderBlocks blocks  | S.length blocks > 1  = F.foldr1 (\b1 b2 -> b1 <> line <> line <> b2) $
                                              fmap renderBlock blocks
                     | S.length blocks == 1 = renderBlock (S.index blocks 0)
                     | otherwise            = empty

renderBlock :: CT.Block -> Doc OutputAnnotation
renderBlock (CT.Para inlines) = renderInlines inlines
renderBlock (CT.Header lvl inlines) = renderInlines inlines <+> parens (text (show lvl))
renderBlock (CT.Blockquote blocks) = indent 8 $ renderBlocks blocks
renderBlock (CT.List b ty blockss) = renderList b ty blockss
renderBlock (CT.CodeBlock attr src) = indent 8 $ text (T.unpack src)
renderBlock (CT.HtmlBlock txt) = text "<html block>" -- TODO
renderBlock CT.HRule = text "----------------------"

renderList :: Bool -> CT.ListType -> [CT.Blocks] -> Doc OutputAnnotation
renderList b (CT.Bullet c) blockss = vsep $ map (hang 4 . (char c <+>) . renderBlocks) blockss
renderList b (CT.Numbered nw i) blockss =
  vsep $
  zipWith3 (\n p txt -> hang 4 $ text (show n) <> p <+> txt)
           [i..] (repeat punc) (map renderBlocks blockss)
  where punc = case nw of
                 CT.PeriodFollowing -> char '.'
                 CT.ParenFollowing  -> char '('

renderInlines :: CT.Inlines -> Doc OutputAnnotation
renderInlines = F.foldr (<>) empty . fmap renderInline

renderInline :: CT.Inline -> Doc OutputAnnotation
renderInline (CT.Str s) = text $ T.unpack s
renderInline CT.Space = space
renderInline CT.SoftBreak = softline
renderInline CT.LineBreak = line
renderInline (CT.Emph txt) = renderInlines txt -- TODO
renderInline (CT.Strong txt) = renderInlines txt -- TODO
renderInline (CT.Code txt) = text $ T.unpack txt
renderInline (CT.Link body url title) = renderInlines body <+> parens (text $ T.unpack url)
renderInline (CT.Image body url title) = text "<image>" -- TODO
renderInline (CT.Entity a) = text $ "<entity " ++ T.unpack a ++ ">" -- TODO
renderInline (CT.RawHtml txt) = text "<html content>" --TODO

emptyDocstring :: Docstring
emptyDocstring = CT.Doc options S.empty

nullDocstring :: Docstring -> Bool
nullDocstring (CT.Doc _ blocks) = S.null blocks

noDocs :: (Docstring, [(Name, Docstring)])
noDocs = (emptyDocstring, [])

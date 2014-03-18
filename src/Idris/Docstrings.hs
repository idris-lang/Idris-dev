-- | Wrapper around Markdown library
module Idris.Docstrings (
    Docstring, parseDocstring, renderDocstring, emptyDocstring, nullDocstring, noDocs,
    overview, containsText
  ) where

import qualified Cheapskate as C
import qualified Cheapskate.Types as CT

import Util.Pretty

import Idris.Core.TT (OutputAnnotation, Name)

import qualified Data.Text as T
import qualified Data.Foldable as F
import qualified Data.Sequence as S

-- | Representation of Idris's inline documentation
type Docstring = CT.Doc

-- | Construct a docstring from a Text that contains Markdown-formatted docs
parseDocstring :: T.Text -> CT.Doc
parseDocstring = C.markdown options


options = CT.Options { CT.sanitize = True
                     , CT.allowRawHtml = False
                     , CT.preserveHardBreaks = True
                     , CT.debug = False
                     }

-- | Convert a docstring to be shown by the pretty-printer
renderDocstring ::  Docstring -> Doc OutputAnnotation
renderDocstring (CT.Doc _ blocks) = renderBlocks blocks

-- | Construct a docstring consisting of the first block-level element of the
-- argument docstring, for use in summaries.
overview :: Docstring -> Docstring
overview (CT.Doc opts blocks) = CT.Doc opts (S.take 1 blocks)

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

-- | The empty docstring
emptyDocstring :: Docstring
emptyDocstring = CT.Doc options S.empty

-- | Check whether a docstring is emtpy
nullDocstring :: Docstring -> Bool
nullDocstring (CT.Doc _ blocks) = S.null blocks

-- | Empty documentation for a definition
noDocs :: (Docstring, [(Name, Docstring)])
noDocs = (emptyDocstring, [])

-- | Does a string occur in the docstring?
containsText ::  T.Text -> Docstring -> Bool
containsText str (CT.Doc _ blocks) = F.any (blockContains str) blocks
  where blockContains :: T.Text -> CT.Block -> Bool
        blockContains str (CT.Para inlines) = F.any (inlineContains str) inlines
        blockContains str (CT.Header lvl inlines) = F.any (inlineContains str) inlines
        blockContains str (CT.Blockquote blocks) = F.any (blockContains str) blocks
        blockContains str (CT.List b ty blockss) = F.any (F.any (blockContains str)) blockss
        blockContains str (CT.CodeBlock attr src) = T.isInfixOf str src
        blockContains str (CT.HtmlBlock txt) = False -- TODO
        blockContains str CT.HRule = False

        inlineContains :: T.Text -> CT.Inline -> Bool
        inlineContains str (CT.Str s) = T.isInfixOf str s
        inlineContains str CT.Space = False
        inlineContains str CT.SoftBreak = False
        inlineContains str CT.LineBreak = False
        inlineContains str (CT.Emph txt) = F.any (inlineContains str) txt
        inlineContains str (CT.Strong txt) = F.any (inlineContains str) txt
        inlineContains str (CT.Code txt) = T.isInfixOf str txt
        inlineContains str (CT.Link body url title) = F.any (inlineContains str) body
        inlineContains str (CT.Image body url title) = False
        inlineContains str (CT.Entity a) = False
        inlineContains str (CT.RawHtml txt) = T.isInfixOf str txt

{-# LANGUAGE DeriveFunctor, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Wrapper around Markdown library
module Idris.Docstrings (
    Docstring(..), Block(..), Inline(..), parseDocstring, renderDocstring, emptyDocstring, nullDocstring, noDocs,
    overview, containsText, renderHtml, annotCode
  ) where

import qualified Cheapskate as C
import qualified Cheapskate.Types as CT
import Cheapskate.Html (renderDoc)

import Util.Pretty

import Idris.Core.TT (OutputAnnotation(..), TextFormatting(..), Name, Term)

import qualified Data.Text as T
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import qualified Data.Sequence as S

import Control.DeepSeq (NFData(..))

import Text.Blaze.Html (Html)

-- | Representation of Idris's inline documentation. The type paramter
-- represents the type of terms that are associated with code blocks.
data Docstring a = DocString CT.Options (Blocks a)
  deriving (Show, Functor, Foldable, Traversable)

type Blocks a = S.Seq (Block a)

-- | Block-level elements.
data Block a = Para (Inlines a)
             | Header Int (Inlines a)
             | Blockquote (Blocks a)
             | List Bool CT.ListType [Blocks a]
             | CodeBlock CT.CodeAttr T.Text a
             | HtmlBlock T.Text
             | HRule
             deriving (Show, Functor, Foldable, Traversable)

data Inline a = Str T.Text
              | Space
              | SoftBreak
              | LineBreak
              | Emph (Inlines a)
              | Strong (Inlines a)
              | Code T.Text a
              | Link (Inlines a) T.Text T.Text
              | Image (Inlines a) T.Text T.Text
              | Entity T.Text
              | RawHtml T.Text
              deriving (Show, Functor, Foldable, Traversable)

type Inlines a = S.Seq (Inline a)


-- | Construct a docstring from a Text that contains Markdown-formatted docs
parseDocstring :: T.Text -> Docstring ()
parseDocstring = toDocstring . C.markdown options
  where toDocstring :: CT.Doc -> Docstring ()
        toDocstring (CT.Doc opts blocks) = DocString opts (fmap toBlock blocks)

        toBlock :: CT.Block -> Block ()
        toBlock (CT.Para inlines)         = Para (fmap toInline inlines)
        toBlock (CT.Header i inlines)     = Header i (fmap toInline inlines)
        toBlock (CT.Blockquote blocks)    = Blockquote (fmap toBlock blocks)
        toBlock (CT.List b t blocks)      = List b t (fmap (fmap toBlock) blocks)
        toBlock (CT.CodeBlock attrs text) = CodeBlock attrs text ()
        toBlock (CT.HtmlBlock src)        = HtmlBlock src
        toBlock CT.HRule                  = HRule

        toInline :: CT.Inline -> Inline ()
        toInline (CT.Str t)              = Str t
        toInline CT.Space                = Space
        toInline CT.SoftBreak            = SoftBreak
        toInline CT.LineBreak            = LineBreak
        toInline (CT.Emph is)            = Emph (fmap toInline is)
        toInline (CT.Strong is)          = Strong (fmap toInline is)
        toInline (CT.Code src)           = Code src ()
        toInline (CT.Link is url title)  = Link (fmap toInline is) url title
        toInline (CT.Image is url title) = Image (fmap toInline is) url title
        toInline (CT.Entity txt)         = Entity txt
        toInline (CT.RawHtml src)        = RawHtml src


options = CT.Options { CT.sanitize = True
                     , CT.allowRawHtml = False
                     , CT.preserveHardBreaks = True
                     , CT.debug = False
                     }

-- | Convert a docstring to be shown by the pretty-printer
renderDocstring :: (a -> Doc OutputAnnotation) -> Docstring (Maybe a) -> Doc OutputAnnotation
renderDocstring pp (DocString _ blocks) = renderBlocks pp blocks

-- | Construct a docstring consisting of the first block-level element of the
-- argument docstring, for use in summaries.
overview :: Docstring a -> Docstring a
overview (DocString opts blocks) = DocString opts (S.take 1 blocks)

renderBlocks :: (a -> Doc OutputAnnotation) -> Blocks (Maybe a) -> Doc OutputAnnotation
renderBlocks pp blocks  | S.length blocks > 1  = F.foldr1 (\b1 b2 -> b1 <> line <> line <> b2) $
                                                  fmap (renderBlock pp) blocks
                        | S.length blocks == 1 = renderBlock pp (S.index blocks 0)
                        | otherwise            = empty

renderBlock :: (a -> Doc OutputAnnotation) -> Block (Maybe a) -> Doc OutputAnnotation
renderBlock pp (Para inlines) = renderInlines pp inlines
renderBlock pp (Header lvl inlines) = renderInlines pp inlines <+> parens (text (show lvl))
renderBlock pp (Blockquote blocks) = indent 8 $ renderBlocks pp blocks
renderBlock pp (List b ty blockss) = renderList pp b ty blockss
renderBlock pp (CodeBlock attr src Nothing) = indent 8 $ text (T.unpack src)
renderBlock pp (CodeBlock attr src (Just tm)) = indent 8 $ pp tm
renderBlock pp (HtmlBlock txt) = text "<html block>" -- TODO
renderBlock pp HRule = text "----------------------"

renderList :: (a -> Doc OutputAnnotation) -> Bool -> CT.ListType -> [Blocks (Maybe a)] -> Doc OutputAnnotation
renderList pp b (CT.Bullet c) blockss = vsep $ map (hang 4 . (char c <+>) . renderBlocks pp) blockss
renderList pp b (CT.Numbered nw i) blockss =
  vsep $
  zipWith3 (\n p txt -> hang 4 $ text (show n) <> p <+> txt)
           [i..] (repeat punc) (map (renderBlocks pp) blockss)
  where punc = case nw of
                 CT.PeriodFollowing -> char '.'
                 CT.ParenFollowing  -> char '('

renderInlines :: (a -> Doc OutputAnnotation) -> Inlines (Maybe a) -> Doc OutputAnnotation
renderInlines pp = F.foldr (<>) empty . fmap (renderInline pp)

renderInline :: (a -> Doc OutputAnnotation) -> Inline (Maybe a) -> Doc OutputAnnotation
renderInline pp (Str s) = text $ T.unpack s
renderInline pp Space = softline
renderInline pp SoftBreak = softline
renderInline pp LineBreak = line
renderInline pp (Emph txt) = annotate (AnnTextFmt ItalicText) $ renderInlines pp txt
renderInline pp (Strong txt) = annotate (AnnTextFmt BoldText) $ renderInlines pp txt
renderInline pp (Code txt Nothing) = text $ T.unpack txt
renderInline pp (Code txt (Just tm)) = pp tm
renderInline pp (Link body url title) = annotate (AnnTextFmt UnderlineText) (renderInlines pp body) <+>
                                        parens (text $ T.unpack url)
renderInline pp (Image body url title) = text "<image>" -- TODO
renderInline pp (Entity a) = text $ "<entity " ++ T.unpack a ++ ">" -- TODO
renderInline pp (RawHtml txt) = text "<html content>" --TODO

-- | The empty docstring
emptyDocstring :: Docstring a
emptyDocstring = DocString options S.empty

-- | Check whether a docstring is emtpy
nullDocstring :: Docstring a -> Bool
nullDocstring (DocString _ blocks) = S.null blocks

-- | Empty documentation for a definition
noDocs :: (Docstring a, [(Name, Docstring a)])
noDocs = (emptyDocstring, [])

-- | Does a string occur in the docstring?
containsText ::  T.Text -> Docstring a -> Bool
containsText str (DocString _ blocks) = F.any (blockContains (T.toLower str)) blocks
  -- blockContains and inlineContains should always be called with a lower-case search string
  where blockContains :: T.Text -> Block a -> Bool
        blockContains str (Para inlines) = F.any (inlineContains str) inlines
        blockContains str (Header lvl inlines) = F.any (inlineContains str) inlines
        blockContains str (Blockquote blocks) = F.any (blockContains str) blocks
        blockContains str (List b ty blockss) = F.any (F.any (blockContains str)) blockss
        blockContains str (CodeBlock attr src _) = T.isInfixOf str (T.toLower src)
        blockContains str (HtmlBlock txt) = False -- TODO
        blockContains str HRule = False

        inlineContains :: T.Text -> Inline a -> Bool
        inlineContains str (Str s) = T.isInfixOf str (T.toLower s)
        inlineContains str Space = False
        inlineContains str SoftBreak = False
        inlineContains str LineBreak = False
        inlineContains str (Emph txt) = F.any (inlineContains str) txt
        inlineContains str (Strong txt) = F.any (inlineContains str) txt
        inlineContains str (Code txt _) = T.isInfixOf str (T.toLower txt)
        inlineContains str (Link body url title) = F.any (inlineContains str) body
        inlineContains str (Image body url title) = False
        inlineContains str (Entity a) = False
        inlineContains str (RawHtml txt) = T.isInfixOf str (T.toLower txt)


renderHtml :: Docstring (Maybe Term) -> Html
renderHtml = renderDoc . fromDocstring
  where
    fromDocstring :: Docstring (Maybe Term) -> CT.Doc
    fromDocstring (DocString opts blocks) = CT.Doc opts (fmap fromBlock blocks)

    fromBlock :: Block (Maybe Term) -> CT.Block
    fromBlock (Para inlines)           = CT.Para (fmap fromInline inlines)
    fromBlock (Header i inlines)       = CT.Header i (fmap fromInline inlines)
    fromBlock (Blockquote blocks)      = CT.Blockquote (fmap fromBlock blocks)
    fromBlock (List b t blocks)        = CT.List b t (fmap (fmap fromBlock) blocks)
    fromBlock (CodeBlock attrs text _) = CT.CodeBlock attrs text
    fromBlock (HtmlBlock src)          = CT.HtmlBlock src
    fromBlock HRule                    = CT.HRule

    fromInline :: Inline (Maybe Term) -> CT.Inline
    fromInline (Str t)              = CT.Str t
    fromInline Space                = CT.Space
    fromInline SoftBreak            = CT.SoftBreak
    fromInline LineBreak            = CT.LineBreak
    fromInline (Emph is)            = CT.Emph (fmap fromInline is)
    fromInline (Strong is)          = CT.Strong (fmap fromInline is)
    fromInline (Code src _)         = CT.Code src
    fromInline (Link is url title)  = CT.Link (fmap fromInline is) url title
    fromInline (Image is url title) = CT.Image (fmap fromInline is) url title
    fromInline (Entity txt)         = CT.Entity txt
    fromInline (RawHtml src)        = CT.RawHtml src


-- | Annotate the code samples in a docstring
annotCode :: forall a b. (String -> b) -- ^ How to annotate code samples
          -> Docstring a
          -> Docstring b
annotCode annot (DocString opts blocks)
    = DocString opts $ fmap annotCodeBlock blocks
  where
    annotCodeBlock :: Block a -> Block b
    annotCodeBlock (Para inlines)          = Para (fmap annotCodeInline inlines)
    annotCodeBlock (Header i inlines)      = Header i (fmap annotCodeInline inlines)
    annotCodeBlock (Blockquote blocks)     = Blockquote (fmap annotCodeBlock blocks)
    annotCodeBlock (List b t blocks)       = List b t (fmap (fmap annotCodeBlock) blocks)
    annotCodeBlock (CodeBlock attrs src _) = CodeBlock attrs src (annot (T.unpack src))
    annotCodeBlock (HtmlBlock src)         = HtmlBlock src
    annotCodeBlock HRule                   = HRule

    annotCodeInline :: Inline a -> Inline b
    annotCodeInline (Str t)              = Str t
    annotCodeInline Space                = Space
    annotCodeInline SoftBreak            = SoftBreak
    annotCodeInline LineBreak            = LineBreak
    annotCodeInline (Emph is)            = Emph (fmap annotCodeInline is)
    annotCodeInline (Strong is)          = Strong (fmap annotCodeInline is)
    annotCodeInline (Code src _)         = Code src (annot (T.unpack src))
    annotCodeInline (Link is url title)  = Link (fmap annotCodeInline is) url title
    annotCodeInline (Image is url title) = Image (fmap annotCodeInline is) url title
    annotCodeInline (Entity txt)         = Entity txt
    annotCodeInline (RawHtml src)        = RawHtml src

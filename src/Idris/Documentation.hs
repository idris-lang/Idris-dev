{-|
Module      : Idris.Documentation
Description : Internal representation of documentation for Idris terms.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable,
             ScopedTypeVariables #-}
module Idris.Documentation
  ( IDoc(..)
  , getIDocDesc
  , setIDocDesc
  , renderIDocDesc
  , overviewIDoc
  , noIDocs
  , emptyIDoc, emptyConstructorDoc, emptyPlainDoc, emptyModuleDoc
  , moduleDoc, constructorDoc, paramDoc
  , doesIDocContain
  , isIDocEmpty
  , annotateIDoc
  ) where

import Idris.Core.TT (OutputAnnotation(..), Name(..))

import Idris.Docs.DocStrings

import Util.Pretty

import qualified Data.Foldable as F
import qualified Data.Sequence as S
import qualified Data.Text as T

import GHC.Generics (Generic)

data IDoc a =
  ModuleDoc
    { mod_desc    :: DocString a -- ^ description
    , mod_brief   :: DocString a -- ^ overview
    , mod_tooltip :: DocString a -- ^ tooltip
    , mod_version :: DocString a -- ^ version
    , mod_date    :: DocString a -- ^ date
    , mod_cright  :: DocString a -- ^ copyright
    , mod_license :: DocString a -- ^ license
    , mod_stable  :: DocString a -- ^ stability
    , mod_port    :: DocString a -- ^ portability
    , mod_maintrs :: S.Seq (DocString a) -- ^ maintainers
    , mod_authors :: S.Seq (DocString a) -- ^ authors
    }
  | PlainDoc
    { plain_desc :: DocString a
    , plain_brief :: DocString a
    }
  | ConstructorDoc
    { con_desc :: DocString a             -- ^ description
    , con_tooltip :: DocString a         -- ^ tooltip
    , con_brief   :: DocString a         -- ^ brief
    , con_since   :: DocString a         -- ^ since
    , con_notes   :: S.Seq (DocString a) -- ^ notes
    , con_rmarks  :: S.Seq (DocString a) -- ^ remarks
    }
  | EmptyDoc
  deriving (Show, Functor, Foldable, Traversable, Generic)


getIDocDesc :: IDoc a -> DocString a
getIDocDesc doc@ModuleDoc{}      = mod_desc doc
getIDocDesc doc@PlainDoc{}       = plain_desc doc
getIDocDesc doc@ConstructorDoc{} = con_desc doc
getIDocDesc EmptyDoc             = emptyDocString

setIDocDesc :: DocString a -> IDoc a -> IDoc a
setIDocDesc desc doc@ModuleDoc{}      = doc {mod_desc = desc}
setIDocDesc desc doc@PlainDoc{}       = doc {plain_desc = desc}
setIDocDesc desc doc@ConstructorDoc{} = doc {con_desc = desc}
setIDocDesc desc EmptyDoc             = PlainDoc desc emptyDocString

renderIDocDesc :: (a -> String -> Doc OutputAnnotation)
               -> IDoc a
               -> Doc OutputAnnotation
renderIDocDesc pp doc =
  renderDocString pp (getIDocDesc doc)



overviewIDoc :: IDoc a -> DocString a
overviewIDoc doc@ModuleDoc{}      = mod_brief   doc
overviewIDoc doc@PlainDoc{}       = plain_brief doc
overviewIDoc doc@ConstructorDoc{} = con_brief   doc
overviewIDoc EmptyDoc = emptyDocString

noIDocs :: (DocString a, [(Name, IDoc a)])
noIDocs = (emptyDocString, [])


emptyIDoc :: IDoc a
emptyIDoc = EmptyDoc

emptyModuleDoc :: IDoc a
emptyModuleDoc = ModuleDoc
  emptyDocString
  emptyDocString
  emptyDocString
  emptyDocString
  emptyDocString
  emptyDocString
  emptyDocString
  emptyDocString
  emptyDocString
  S.empty
  S.empty

emptyPlainDoc :: IDoc a
emptyPlainDoc = PlainDoc emptyDocString emptyDocString

paramDoc :: DocString a -> IDoc a
paramDoc d = PlainDoc d (overview d)

emptyConstructorDoc :: IDoc a
emptyConstructorDoc = ConstructorDoc
  emptyDocString
  emptyDocString
  emptyDocString
  emptyDocString
  S.empty
  S.empty

constructorDoc :: DocString a -> IDoc a
constructorDoc body = let doc = setIDocDesc body emptyConstructorDoc
  in doc {con_brief = overview body}

moduleDoc :: DocString a -> IDoc a
moduleDoc body = let doc = setIDocDesc body emptyModuleDoc
  in doc {mod_brief = overview body}


isIDocEmpty :: IDoc a -> Bool
isIDocEmpty EmptyDoc = True
isIDocEmpty (ModuleDoc d b t v r c l s p ms as) =
  and [ nullDocString d
      , nullDocString b
      , nullDocString t
      , nullDocString v
      , nullDocString r
      , nullDocString c
      , nullDocString l
      , nullDocString s
      , nullDocString p
      , S.null ms
      , S.null as]
isIDocEmpty (PlainDoc d b) = and [nullDocString d, nullDocString b]
isIDocEmpty (ConstructorDoc d t b s ns rs) =
  and [ nullDocString d
      , nullDocString t
      , nullDocString b
      , nullDocString s
      , S.null ns
      , S.null rs]

annotateIDoc :: forall a b. (String -> b)
             -> IDoc a
             -> IDoc b
annotateIDoc _ EmptyDoc = EmptyDoc
annotateIDoc f (PlainDoc d b) =
  PlainDoc (annotCode f d) (annotCode f b)
annotateIDoc f (ConstructorDoc d t b s ns rs) =
  ConstructorDoc (annotCode f d)
                 (annotCode f t)
                 (annotCode f b)
                 (annotCode f d)
                 (fmap (annotCode f) ns)
                 (fmap (annotCode f) rs)

annotateIDoc f (ModuleDoc d b t v r c l s p ms as) =
  ModuleDoc (annotCode f d)
            (annotCode f b)
            (annotCode f t)
            (annotCode f v)
            (annotCode f r)
            (annotCode f c)
            (annotCode f l)
            (annotCode f s)
            (annotCode f p)
            (fmap (annotCode f) ms)
            (fmap (annotCode f) as)

doesIDocContain ::  T.Text -> IDoc a -> Bool
doesIDocContain _ EmptyDoc = False
doesIDocContain term (PlainDoc d b) =
  or [containsText term d, containsText term b]
doesIDocContain term (ModuleDoc d b t v r c l s p ms as) =
  or [  containsText term d
      , containsText term b
      , containsText term t
      , containsText term v
      , containsText term r
      , containsText term c
      , containsText term l
      , containsText term s
      , containsText term p
      , F.any (containsText term) ms
      , F.any (containsText term) as
      ]
doesIDocContain term (ConstructorDoc d t b s ns rs) =
  or [ containsText term d
     , containsText term t
     , containsText term b
     , containsText term s
     , F.any (containsText term) ns
     , F.any (containsText term) rs]

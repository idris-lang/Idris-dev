{-|
Module      : Idris.Parser.Documentation
Description : Parse IdrisDoc.

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts, MultiParamTypeClasses #-}
module Idris.Parser.Documentation
  ( docComment
  , docModule
  , docPlain
  , docConstructor
  , docConstructorNoArgs
  )
where

import Idris.Core.TT
import Idris.Docs.DocStrings
import Idris.Documentation

import Idris.Parser.Helpers

import Control.Applicative

import Data.Char

import Data.List

import qualified Data.Sequence as S
import qualified Data.Text as T

import Text.Megaparsec ((<?>))
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P

{-| Parses a documentation comment

@
  DocComment_t ::=   '|||' ~EOL_t* EOL_t
                 ;
@
 -}
docComment :: IdrisParser (DocString (), [(Name, IDoc ())])
docComment = do
     dc <- pushIndent *> docCommentLine
     rest <- many (indented docCommentLine)
     args <- many $ do
       (name, first) <- indented argDocCommentLine
       rest <- many (indented docCommentLine)
       return (name, intercalate "\n" (first:rest))
     popIndent
     return ( fromStrings (dc:rest)
            , map (\(n, d) -> (n, paramDoc $ parseDocString (T.pack d))) args)
  <?> "IdrisDoc Comment"

docPlain :: IdrisParser (IDoc ())
docPlain = do
      firstLine <- pushIndent *> docCommentLine
      rest  <- many (indented docCommentLine)
      brief <- P.option emptyDocString (mdata "brief")
      popIndent
      return (PlainDoc (fromStrings (firstLine:rest)) brief)
  <?> "IdrisDoc Plain"

docConstructorNoArgs :: IdrisParser (IDoc ())
docConstructorNoArgs = do
      firstLine <- pushIndent *> docCommentLine
      body <- many (indented docCommentLine)
      brief   <- P.option emptyDocString (mdata "brief")
      tooltip <- P.option emptyDocString (mdata "tooltip")
      since   <- P.option emptyDocString (mdata "since")
      ns <- many $ mdata "note"
      rs <- many $ mdata "remark"
      popIndent
      let ns' = S.fromList ns
          rs' = S.fromList rs
          desc = firstLine : body
          doc = ConstructorDoc (fromStrings desc) brief tooltip since ns' rs'

      return doc
    <?> "Constructor Documentation"

docConstructor :: IdrisParser (IDoc (), [(Name, IDoc ())])
docConstructor = do
      firstLine <- pushIndent *> docCommentLine
      body <- many (indented docCommentLine)
      brief   <- P.option emptyDocString (mdata "brief")
      tooltip <- P.option emptyDocString (mdata "tooltip")
      since   <- P.option emptyDocString (mdata "since")
      ns <- many $ mdata "note"
      rs <- many $ mdata "remark"
      args <- many $ do
        (name, argdocFirst) <- indented paramDocComment
                           <|> indented argDocCommentLine
        rest <- many (indented docCommentLine)
        return (name, paramDoc $ fromStrings (argdocFirst:rest))
      popIndent
      let ns' = S.fromList ns
          rs' = S.fromList rs
          desc = firstLine : body
          doc = ConstructorDoc (fromStrings desc) brief tooltip since ns' rs'

      return (doc, args)
    <?> "Constructor Documentation"

docModule :: IdrisParser (IDoc ())
docModule = do
      firstLine <- pushIndent *> docCommentLine
      body <- many (indented docCommentLine)
      brief   <- P.option emptyDocString (mdata "brief")
      tooltip <- P.option emptyDocString (mdata "tooltip")
      version <- P.option emptyDocString (mdata "version")
      date    <- P.option emptyDocString (mdata "date")
      cright  <- P.option emptyDocString (mdata "copyright")
      license <- P.option emptyDocString (mdata "license")
      stable  <- P.option emptyDocString (mdata "stability")
      port    <- P.option emptyDocString (mdata "portability")
      ms      <- many $ mdata "maintainer"
      as      <- many $ mdata "author"
      popIndent
      let ms' = S.fromList ms
      let as' = S.fromList as
      let desc = firstLine : body
      return (ModuleDoc (fromStrings desc) brief tooltip version date cright license stable port ms' as')
    <?> "Module Documentation"

mdata :: String -> IdrisParser (DocString ())
mdata str = do
   first <- indented $ mdataDocComment str
   rest  <- many $ indented docCommentLine
   return (fromStrings (first:rest))
 <?> ("IdrisDoc Metadata:" ++ str)

docCommentLine :: Parsing m => m String
docCommentLine =
  (P.try $ do string "|||"
              many (P.satisfy (==' '))
              contents <- P.option "" (do first <- P.satisfy (\c -> not (isEol c || c == '@'))
                                          res <- many (P.satisfy (not . isEol))
                                          return $ first:res)
              eol ; someSpace
              return contents)
 <?> "Doc Comment Line"

argDocCommentLine :: IdrisParser (Name, String)
argDocCommentLine = (P.try $ do
     P.string "|||"
     P.many (P.satisfy isSpace)
     fc <- extent $ P.char '@'
     P.many (P.satisfy isSpace)
     n <- name
     P.many (P.satisfy isSpace)
     docs <- P.many (P.satisfy (not . isEol))
     P.eol
     someSpace
     parserWarning fc Nothing (Msg (msg n docs))
     return (n, docs))
    <?> "IdrisDoc Old style parameter"
  where
    msg n docs = unlines [ "Old style parameter documentation declarations are to be deprecated in future releases of Idris."
                         , "Please use the new style:"
                         , "||| @param " ++ show n ++ " " ++ docs]

paramDocComment :: IdrisParser (Name, String)
paramDocComment = (P.try $ do
   P.string "|||"
   P.many (P.satisfy isSpace)
   P.string "@param"
   P.many (P.satisfy isSpace)
   n <- name
   P.many (P.satisfy isSpace)
   docs <- P.many (P.satisfy (not . isEol))
   P.eol
   someSpace
   return (n, docs))
 <?> "IdrisDoc Parameter"

mdataDocComment :: Parsing m => String -> m String
mdataDocComment str = (P.try $ do
   P.string "|||"
   P.many (P.satisfy isSpace)
   P.string ('@':str)
   P.many (P.satisfy isSpace)
   docs <- P.many (P.satisfy (not . isEol))
   P.eol
   someSpace
   return docs)
 <?> "IdrisDoc Metadata"

fromStrings :: [String] -> DocString ()
fromStrings strs = parseDocString $ T.pack (intercalate "\n" strs)

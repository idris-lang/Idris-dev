{-|
Module      : IRTS.CodegenJavaScript
Description : The JavaScript code generator.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE OverloadedStrings, PatternGuards #-}
module IRTS.CodegenJavaScript (codegenJavaScript
                             , codegenNode
                             , JSTarget(..)
                             ) where

import IRTS.CodegenCommon
import IRTS.JavaScript.Codegen
import System.Directory
import System.FilePath
import Data.Char
import Data.Text (Text)
import qualified Data.Text as T


data JSTarget = Node | JavaScript deriving Eq


htmlHeader :: Text
htmlHeader =
  T.concat [ "<html>\n"
           , " <head>\n"
           , "  <meta charset='utf-8'>\n"
           , " </head>\n"
           , " <body>\n"
           , "  <script type='text/javascript'>\n"
           ]

htmlFooter :: Text
htmlFooter =
  T.concat [ "\n  </script>\n"
           , " </body>\n"
           , "</html>"
           ]

codegenJavaScript :: CodeGenerator
codegenJavaScript ci =
  let (h, f) = if (map toLower $ takeExtension $ outputFile ci) == ".html" then
                  (htmlHeader, htmlFooter)
                  else ("","")
  in codegenJs (CGConf { header = h
                       , footer = f
                       , initialization = const ""
                       , writeStrTemplate = "console.log(%0)"
                       }
               )
               ci

codegenNode :: CodeGenerator
codegenNode ci =
  do
    codegenJs (CGConf { header = "#!/usr/bin/env node\n"
                      , footer = ""
                      , initialization = \x -> if usedWriteStr x then "var fs = require('fs');\n" else ""
                      , writeStrTemplate = "fs.writeSync(1,%0)"
                      }
              )
              ci
    setPermissions (outputFile ci) (emptyPermissions { readable   = True
                                                     , executable = True
                                                     , writable   = True
                                                     })

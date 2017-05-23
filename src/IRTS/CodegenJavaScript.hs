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

import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import IRTS.CodegenCommon
import IRTS.JavaScript.Codegen
import System.Directory
import System.FilePath


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

nodeReadLine :: Text
nodeReadLine =
  T.concat [ "var js_idris_readStr = function() {\n"
           , "   var ret = '';"
           , "   var b = new Buffer(1024);"
           , "   var i = 0;\n"
           , "   while(true) {\n"
           , "     fs.readSync(0, b, i, 1 )\n"
           , "     if (b[i] == 10) {\n"
           , "       ret = b.toString('utf8', 0, i);\n"
           , "       break;\n"
           , "     }\n"
           , "     i++;\n"
           , "     if (i == b.length) {\n"
           , "       nb = new Buffer (b.length*2);\n"
           , "       b.copy(nb)\n"
           , "       b = nb;\n"
           , "     }\n"
           , "   }\n"
           , "   return ret;\n"
           , " };\n"
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
                       , readStrTemplate = "prompt('Prelude.getLine')"
                       , jsbnPath = "jsbn/jsbn-browser.js"
                       , extraRunTime = "Runtime-javascript.js"
                       }
               )
               ci

initializationNode :: CGStats -> Text
initializationNode x =
  T.concat [ if usedWriteStr x || usedReadStr x then "var fs = require('fs');\n" else ""
           , if usedReadStr x then nodeReadLine else ""
           ]

codegenNode :: CodeGenerator
codegenNode ci =
  do
    codegenJs (CGConf { header = "#!/usr/bin/env node\n"
                      , footer = ""
                      , initialization = initializationNode
                      , writeStrTemplate = "process.stdout.write(%0)"
                      , readStrTemplate = "js_idris_readStr()"
                      , jsbnPath = "jsbn/jsbn-node.js"
                      , extraRunTime = "Runtime-node.js"
                      }
              )
              ci
    setPermissions (outputFile ci) (emptyPermissions { readable   = True
                                                     , executable = True
                                                     , writable   = True
                                                     })

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


data JSTarget = Node | JavaScript deriving Eq


codegenJavaScript :: CodeGenerator
codegenJavaScript ci =
  codegenJs (CGConf { header = ""
                    , initialization = const ""
                    , writeStrTemplate = "console.log(%0)"
                    }
            )
            ci

codegenNode :: CodeGenerator
codegenNode ci =
  do
    codegenJs (CGConf { header = "#!/usr/bin/env node\n"
                      , initialization = \x -> if usedWriteStr x then "var fs = require('fs');\n" else ""
                      , writeStrTemplate = "fs.writeSync(1,%0)"
                      }
              )
              ci
    setPermissions (outputFile ci) (emptyPermissions { readable   = True
                                                     , executable = True
                                                     , writable   = True
                                                     })

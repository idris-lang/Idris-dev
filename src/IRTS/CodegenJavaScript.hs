module IRTS.CodegenJavaScript (codegenJavaScript ) where

import Idris.AbsSyntax
import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import IRTS.CodegenCommon
import Core.TT
import Paths_idris
import Util.System

import Data.Char
import Data.List
import System.IO

codegenJavaScript
  :: [(Name, SDecl)]
  -> FilePath
  -> OutputType
  -> IO ()
codegenJavaScript definitions filename outputType = do
  let body = concat $ map (translateDeclaration . snd) definitions
      output = concat [header, body, footer]
  writeFile filename output


header :: String
header =
  concat $ map (\line -> line ++ "\n")
    ["define(function(require) {",
     "var m = {};"]


footer :: String
footer =
  concat $ map (\line -> line ++ "\n")
    ["return m;",
     "});"]


translateName :: Name -> String
translateName = show


translateDeclaration :: SDecl -> String
translateDeclaration (SFun name parameterNames stackSize body) =
  concat ["m[\"", translateName name, "\"] = function(s) { ",
          translateExpression body, " ",
          intercalate " " $ take (length parameterNames) $ repeat "s.pop();",
          " };\n"]


translateExpression :: SExp -> String
translateExpression (SLet name value body) =
  intercalate " "
    $ [translateExpression value,
       translateExpression body,
       "s.pop();", "s.pop();"]
translateExpression _ = "..."

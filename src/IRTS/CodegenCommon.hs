module IRTS.CodegenCommon where

import Idris.Core.TT
import IRTS.Simplified
import IRTS.Defunctionalise
import IRTS.Lang

import Data.Word

data DbgLevel = NONE | DEBUG | TRACE deriving Eq
data OutputType = Raw | Object | Executable | MavenProject deriving (Eq, Show)

-- Everything which might be needed in a code generator - a CG can choose which
-- level of Decls to generate code from (simplified, defunctionalised or merely
-- lambda lifted) and has access to the list of object files, libraries, etc.

data CodegenInfo = CodegenInfo { outputFile :: String,
                                 outputType :: OutputType,
                                 targetTriple :: String,
                                 targetCPU :: String,
                                 includes :: [FilePath],
                                 importDirs :: [FilePath],
                                 compileObjs :: [String],
                                 compileLibs :: [String],
                                 compilerFlags :: [String],
                                 debugLevel :: DbgLevel,
                                 simpleDecls :: [(Name, SDecl)],
                                 defunDecls :: [(Name, DDecl)],
                                 liftDecls :: [(Name, LDecl)],
                                 interfaces :: Bool,
                                 exportDecls :: [ExportIFace]
                               } 

type CodeGenerator = CodegenInfo -> IO ()

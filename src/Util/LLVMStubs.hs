{--

Things needed to build without LLVM
Replaces stuff from LLVM.General.Target and IRTS.CodegenLLVM.

--}

module Util.LLVMStubs where

import qualified Idris.Core.TT as TT
import IRTS.Simplified
import IRTS.CodegenCommon

import Data.Word (Word)

getDefaultTargetTriple :: IO String
getDefaultTargetTriple = return ""

getHostCPUName :: IO String
getHostCPUName = return ""


codegenLLVM :: CodeGenerator
codegenLLVM _ = fail "This Idris was compiled without the LLVM backend."

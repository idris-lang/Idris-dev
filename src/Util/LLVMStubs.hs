{-- 

Things needed to build without LLVM 
Replaces stuff from LLVM.General.Target and IRTS.CodegenLLVM.

--}

module Util.LLVMStubs where

import qualified Core.TT as TT
import IRTS.Simplified
import IRTS.CodegenCommon


getDefaultTargetTriple :: IO String
getDefaultTargetTriple = return ""

getHostCPUName :: IO String
getHostCPUName = return ""


codegenLLVM :: [(TT.Name, SDecl)] ->
               String -> -- target triple
               String -> -- target CPU
               Int -> -- Optimization degree
               FilePath -> -- output file name
               OutputType ->
               IO ()

codegenLLVM _ _ _ _ _ _ = fail "This Idris was compiled without the LLVM backend."

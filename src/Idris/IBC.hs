{-# LANGUAGE TypeSynonymInstances, TemplateHaskell #-}

module Idris.IBC where

import Core.Evaluate
import Core.TT
import Core.CaseTree
import Idris.Compiler
import Idris.AbsSyntax

import Data.Binary
import Data.List
import Data.DeriveTH
import Control.Monad

ibcVersion :: Word8
ibcVersion = 1

data IBCFile = IBCFile { ver :: Word8,
                         ibc_imports :: [FilePath],
                         ibc_fixes :: [FixDecl],
                         ibc_statics :: [(Name, [Bool])],
                         ibc_classes :: [(Name, ClassInfo)],
                         ibc_syntax :: [Syntax],
                         ibc_keywords :: [String],
                         ibc_objs :: [FilePath],
                         ibc_libs :: [String],
                         ibc_hdrs :: [String],
                         ibc_defs :: [(Name, Def)] }

initIBC :: IBCFile
initIBC = IBCFile ibcVersion [] [] [] [] [] [] [] [] [] []

loadIBC :: FilePath -> Idris ()
loadIBC fp = fail "Not implemented"

writeIBC :: FilePath -> Idris ()
writeIBC f 
    = do iLOG $ "Writing ibc " ++ show f
         i <- getIState
         case idris_metavars i \\ primDefs of
                (_:_) -> fail "Can't write ibc when there are unsolve metavariables"
                [] -> return ()
         return ()

$( derive makeBinary ''IBCFile )
$( derive makeBinary ''PTerm )
$( derive makeBinary ''Raw )
$( derive makeBinary ''PTactic' )
$( derive makeBinary ''PDo' )
$( derive makeBinary ''PArg' )
$( derive makeBinary ''ClassInfo )
$( derive makeBinary ''Plicity )
$( derive makeBinary ''FC )
$( derive makeBinary ''Syntax )
$( derive makeBinary ''SynContext )
$( derive makeBinary ''SSymbol )
$( derive makeBinary ''Static )
$( derive makeBinary ''Fixity )
$( derive makeBinary ''FixDecl )

$( derive makeBinary ''Def )
$( derive makeBinary ''SC )
$( derive makeBinary ''CaseAlt )
$( derive makeBinary ''NameType )
$( derive makeBinary ''Name )
$( derive makeBinary ''Binder )
$( derive makeBinary ''TT )
$( derive makeBinary ''Const )

-- We need this for serialising Def. Fortunately, it never gets used because
-- we'll never serialise a primitive operator

instance Binary (a -> b) where
    put x = return ()
    get = undefined

-- We assume that universe levels have been checked, so anything external
-- can just have the same universe variable and we won't get any new
-- cycles.

instance Binary UExp where
    put x = return ()
    get = return (UVar (-1))


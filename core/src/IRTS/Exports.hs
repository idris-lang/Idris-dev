{-|
Module      : IRTS.Exports
Description : Deal with external things.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module IRTS.Exports(findExports, getExpNames) where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Error
import IRTS.Lang

import Data.Maybe

findExports :: Idris [ExportIFace]
findExports = do exps <- getExports
                 es <- mapM toIFace exps
                 logCodeGen 2 $ "Exporting " ++ show es
                 return es

getExpNames :: [ExportIFace] -> [Name]
getExpNames = concatMap expNames

expNames :: ExportIFace -> [Name]
expNames (Export _ _ es) = mapMaybe fnames es
  where fnames (ExportData _) = Nothing
        fnames (ExportFun n _ _ _) = Just n

toIFace :: Name -> Idris ExportIFace
toIFace n = do i <- getIState
               let ctxt = tt_ctxt i
               def <- case lookupDefExact n ctxt of
                           Just (CaseOp _ _ _ _ _ cs)
                              -> getExpList (snd (cases_compiletime cs))
                           Nothing -> ifail "Can't happen [toIFace]"
               case lookupTyExact n ctxt of
                    Just ty -> toIFaceTyVal ty def
                    Nothing -> ifail "Can't happen [toIFace]"
  where
    getExpList (STerm t) = return t
    getExpList _ = ifail "Badly formed export list"

toIFaceTyVal :: Type -> Term -> Idris ExportIFace
toIFaceTyVal ty tm
   | (P _ exp _, [P _ ffi _, Constant (Str hdr), _]) <- unApply ty
         = do tm' <- toIFaceVal tm
              return $ Export ffi hdr tm'

toIFaceVal :: Term -> Idris [Export]
toIFaceVal tm
   | (P _ end _, _) <- unApply tm,
     end == sNS (sUN "End") ["FFI_Export"] = return []
   | (P _ fun _, [_,_,_,_,(P _ fn _),extnm,prf,rest]) <- unApply tm,
     fun == sNS (sUN "Fun") ["FFI_Export"]
       = do rest' <- toIFaceVal rest
            return $
              ExportFun fn (toFDesc extnm) (toFDescRet prf) (toFDescArgs prf)
                  : rest'
   | (P _ dat _, [_,_,_,_,d,rest]) <- unApply tm,
     dat == sNS (sUN "Data") ["FFI_Export"]
       = do rest' <- toIFaceVal rest
            return $ ExportData (toFDesc d) : rest'
   | otherwise = ifail $ "Badly formed export list " ++ show tm

toFDesc :: Term -> FDesc
toFDesc (Constant (Str str)) = FStr str
toFDesc tm
   | (P _ n _, []) <- unApply tm = FCon (deNS n)
   | (P _ n _, as) <- unApply tm = FApp (deNS n) (map toFDesc as)
toFDesc _ = FUnknown

toFDescRet :: Term -> FDesc
toFDescRet tm
   | (P _ ret _, [_,_,_,b]) <- unApply tm,
     ret == sNS (sUN "FFI_Ret") ["FFI_Export"]
       = toFDescBase b
   | (P _ io _, [_,_,_,b]) <- unApply tm,
     io == sNS (sUN "FFI_IO") ["FFI_Export"]
       = FIO $ toFDescBase b
   | (P _ fun _, [_,_,_,_,_,t]) <- unApply tm,
     fun == sNS (sUN "FFI_Fun") ["FFI_Export"]
       = toFDescRet t
   | otherwise = error "Badly formed export proof"

toFDescBase :: Term -> FDesc
toFDescBase tm
   | (P _ prim _, [_, _, _, pdesc]) <- unApply tm,
     prim == sNS (sUN "FFI_Prim") ["FFI_Export"]
       = toFDescPrim pdesc
   | (P _ prim _, [_, _, _, ddesc, _]) <- unApply tm,
     prim == sNS (sUN "FFI_ExpType") ["FFI_Export"]
       = toFDescPrim ddesc
   | otherwise = error "Badly formed export type"

toFDescArgs :: Term -> [FDesc]
toFDescArgs tm
   | (P _ fun _, [_,_,_,_,b,t]) <- unApply tm,
     fun == sNS (sUN "FFI_Fun") ["FFI_Export"]
       = toFDescBase b : toFDescArgs t
   | otherwise = []

toFDescPrim (Constant (Str str)) = FStr str
toFDescPrim tm
   | (P _ n _, []) <- unApply tm = FCon (deNS n)
   | (P _ n _, as) <- unApply tm = FApp (deNS n) (map toFDescPrim as)
toFDescPrim _ = FUnknown

deNS (NS n _) = n
deNS n = n

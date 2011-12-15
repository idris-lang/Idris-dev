{-# LANGUAGE TypeSynonymInstances #-}

module Idris.IBC where

import Core.Evaluate
import Core.TT
import Core.CaseTree
import Idris.Compiler
import Idris.AbsSyntax
import Idris.Imports

import Data.Binary
import Data.List
import Data.ByteString.Lazy as B hiding (length, elem)
-- import Data.DeriveTH
import Control.Monad
import Control.Monad.State hiding (get, put)
import System.FilePath
import System.Directory
import System.Posix.Files

import Paths_idris

ibcVersion :: Word8
ibcVersion = 3

data IBCFile = IBCFile { ver :: Word8,
                         sourcefile :: FilePath,
                         ibc_imports :: [FilePath],
                         ibc_implicits :: [(Name, [PArg])],
                         ibc_fixes :: [FixDecl],
                         ibc_statics :: [(Name, [Bool])],
                         ibc_classes :: [(Name, ClassInfo)],
                         ibc_syntax :: [Syntax],
                         ibc_keywords :: [String],
                         ibc_objs :: [FilePath],
                         ibc_libs :: [String],
                         ibc_hdrs :: [String],
                         ibc_defs :: [(Name, Def)] }
{-! 
deriving instance Binary IBCFile 
!-}

initIBC :: IBCFile
initIBC = IBCFile ibcVersion "" [] [] [] [] [] [] [] [] [] [] []

loadIBC :: FilePath -> Idris ()
loadIBC fp = do iLOG $ "Loading ibc " ++ fp
                ibcf <- lift $ (decodeFile fp :: IO IBCFile)
                process ibcf fp

writeIBC :: FilePath -> FilePath -> Idris ()
writeIBC src f 
    = do iLOG $ "Writing ibc " ++ show f
         i <- getIState
         case idris_metavars i \\ primDefs of
                (_:_) -> fail "Can't write ibc when there are unsolved metavariables"
                [] -> return ()
         ibcf <- mkIBC (ibc_write i) (initIBC { sourcefile = src }) 
         lift $ encodeFile f ibcf
         iLOG $ "Written"
         return ()

mkIBC :: [IBCWrite] -> IBCFile -> Idris IBCFile
mkIBC [] f = return f
mkIBC (i:is) f = do ist <- getIState
                    logLvl 5 $ show i ++ " " ++ show (Data.List.length is)
                    f' <- ibc ist i f
                    mkIBC is f'

ibc i (IBCFix d) f = return f { ibc_fixes = d : ibc_fixes f } 
ibc i (IBCImp n) f = case lookupCtxt Nothing n (idris_implicits i) of
                        [v] -> return f { ibc_implicits = (n,v): ibc_implicits f     }
                        _ -> fail "IBC write failed"
ibc i (IBCStatic n) f 
                   = case lookupCtxt Nothing n (idris_statics i) of
                        [v] -> return f { ibc_statics = (n,v): ibc_statics f     }
                        _ -> fail "IBC write failed"
ibc i (IBCClass n) f 
                   = case lookupCtxt Nothing n (idris_classes i) of
                        [v] -> return f { ibc_classes = (n,v): ibc_classes f     }
                        _ -> fail "IBC write failed"
ibc i (IBCSyntax n) f = return f { ibc_syntax = n : ibc_syntax f }
ibc i (IBCKeyword n) f = return f { ibc_keywords = n : ibc_keywords f }
ibc i (IBCImport n) f = return f { ibc_imports = n : ibc_imports f }
ibc i (IBCObj n) f = return f { ibc_objs = n : ibc_objs f }
ibc i (IBCLib n) f = return f { ibc_libs = n : ibc_libs f }
ibc i (IBCHeader n) f = return f { ibc_hdrs = n : ibc_hdrs f }
ibc i (IBCDef n) f = case lookupDef Nothing n (tt_ctxt i) of
                        [v] -> return f { ibc_defs = (n,v): ibc_defs f     }
                        _ -> fail "IBC write failed"

process :: IBCFile -> FilePath -> Idris ()
process i fn
   | ver i /= ibcVersion = do iLOG "ibc out of date"
                              fail "Incorrect ibc version"
   | otherwise =  
            do lift $ timestampOlder (sourcefile i) fn
               pImports (ibc_imports i)
               pImps (ibc_implicits i)
               pFixes (ibc_fixes i)
               pStatics (ibc_statics i)
               pClasses (ibc_classes i)
               pSyntax (ibc_syntax i)
               pKeywords (ibc_keywords i)
               pObjs (ibc_objs i)
               pLibs (ibc_libs i)
               pHdrs (ibc_hdrs i)
               pDefs (ibc_defs i)

timestampOlder :: FilePath -> FilePath -> IO ()
timestampOlder src ibc = do srcok <- doesFileExist src
                            when srcok $ do
                                srcs <- getFileStatus src
                                ibcs <- getFileStatus ibc
                                if (modificationTime srcs > modificationTime ibcs)
                                    then fail "Needs reloading"
                                    else return ()

pImports :: [FilePath] -> Idris ()
pImports fs 
  = do datadir <- lift $ getDataDir
       mapM_ (\f -> do fp <- lift $ findImport [".", datadir] f
                       i <- getIState
                       if (f `elem` imported i)
                        then iLOG $ "Already read " ++ f
                        else do putIState (i { imported = f : imported i })
                                case fp of 
                                    LIDR fn -> do iLOG $ "Failed at " ++ fn
                                                  fail "Must be an ibc"
                                    IDR fn -> do iLOG $ "Failed at " ++ fn
                                                 fail "Must be an ibc"
                                    IBC fn src -> loadIBC fn) 
             fs

pImps :: [(Name, [PArg])] -> Idris ()
pImps imps = mapM_ (\ (n, imp) -> 
                        do i <- getIState
                           putIState (i { idris_implicits 
                                            = addDef n imp (idris_implicits i) }))
                   imps

pFixes :: [FixDecl] -> Idris ()
pFixes f = do i <- getIState
              putIState (i { idris_infixes = f ++ idris_infixes i })

pStatics :: [(Name, [Bool])] -> Idris ()
pStatics ss = mapM_ (\ (n, s) ->
                        do i <- getIState
                           putIState (i { idris_statics
                                           = addDef n s (idris_statics i) }))
                    ss

pClasses :: [(Name, ClassInfo)] -> Idris ()
pClasses cs = mapM_ (\ (n, c) ->
                        do i <- getIState
                           putIState (i { idris_classes
                                           = addDef n c (idris_classes i) }))
                    cs

pSyntax :: [Syntax] -> Idris ()
pSyntax s = do i <- getIState
               putIState (i { syntax_rules = s ++ syntax_rules i })

pKeywords :: [String] -> Idris ()
pKeywords k = do i <- getIState
                 putIState (i { syntax_keywords = k ++ syntax_keywords i })

pObjs :: [FilePath] -> Idris ()
pObjs os = mapM_ addObjectFile os

pLibs :: [String] -> Idris ()
pLibs ls = mapM_ addLib ls

pHdrs :: [String] -> Idris ()
pHdrs hs = mapM_ addHdr hs

pDefs :: [(Name, Def)] -> Idris ()
pDefs ds = mapM_ (\ (n, d) -> 
                     do i <- getIState
                        putIState (i { tt_ctxt = addCtxtDef n d (tt_ctxt i) }))
                 ds       
                            

----- Generated by 'derive'

 
instance Binary FC where
        put (FC x1 x2)
          = do put x1
               put x2
        get
          = do x1 <- get
               x2 <- get
               return (FC x1 x2)

 
instance Binary Name where
        put x
          = case x of
                UN x1 -> do putWord8 0
                            put x1
                NS x1 x2 -> do putWord8 1
                               put x1
                               put x2
                MN x1 x2 -> do putWord8 2
                               put x1
                               put x2
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (UN x1)
                   1 -> do x1 <- get
                           x2 <- get
                           return (NS x1 x2)
                   2 -> do x1 <- get
                           x2 <- get
                           return (MN x1 x2)
                   _ -> error "Corrupted binary data for Name"

 
instance Binary Const where
        put x
          = case x of
                I x1 -> do putWord8 0
                           put x1
                BI x1 -> do putWord8 1
                            put x1
                Fl x1 -> do putWord8 2
                            put x1
                Ch x1 -> do putWord8 3
                            put x1
                Str x1 -> do putWord8 4
                             put x1
                IType -> putWord8 5
                BIType -> putWord8 6
                FlType -> putWord8 7
                ChType -> putWord8 8
                StrType -> putWord8 9
                PtrType -> putWord8 10
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (I x1)
                   1 -> do x1 <- get
                           return (BI x1)
                   2 -> do x1 <- get
                           return (Fl x1)
                   3 -> do x1 <- get
                           return (Ch x1)
                   4 -> do x1 <- get
                           return (Str x1)
                   5 -> return IType
                   6 -> return BIType
                   7 -> return FlType
                   8 -> return ChType
                   9 -> return StrType
                   10 -> return PtrType
                   _ -> error "Corrupted binary data for Const"

 
instance Binary Raw where
        put x
          = case x of
                Var x1 -> do putWord8 0
                             put x1
                RBind x1 x2 x3 -> do putWord8 1
                                     put x1
                                     put x2
                                     put x3
                RApp x1 x2 -> do putWord8 2
                                 put x1
                                 put x2
                RSet -> putWord8 3
                RConstant x1 -> do putWord8 4
                                   put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Var x1)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (RBind x1 x2 x3)
                   2 -> do x1 <- get
                           x2 <- get
                           return (RApp x1 x2)
                   3 -> return RSet
                   4 -> do x1 <- get
                           return (RConstant x1)
                   _ -> error "Corrupted binary data for Raw"

 
instance (Binary b) => Binary (Binder b) where
        put x
          = case x of
                Lam x1 -> do putWord8 0
                             put x1
                Pi x1 -> do putWord8 1
                            put x1
                Let x1 x2 -> do putWord8 2
                                put x1
                                put x2
                NLet x1 x2 -> do putWord8 3
                                 put x1
                                 put x2
                Hole x1 -> do putWord8 4
                              put x1
                GHole x1 -> do putWord8 5
                               put x1
                Guess x1 x2 -> do putWord8 6
                                  put x1
                                  put x2
                PVar x1 -> do putWord8 7
                              put x1
                PVTy x1 -> do putWord8 8
                              put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Lam x1)
                   1 -> do x1 <- get
                           return (Pi x1)
                   2 -> do x1 <- get
                           x2 <- get
                           return (Let x1 x2)
                   3 -> do x1 <- get
                           x2 <- get
                           return (NLet x1 x2)
                   4 -> do x1 <- get
                           return (Hole x1)
                   5 -> do x1 <- get
                           return (GHole x1)
                   6 -> do x1 <- get
                           x2 <- get
                           return (Guess x1 x2)
                   7 -> do x1 <- get
                           return (PVar x1)
                   8 -> do x1 <- get
                           return (PVTy x1)
                   _ -> error "Corrupted binary data for Binder"

 
instance Binary NameType where
        put x
          = case x of
                Bound -> putWord8 0
                Ref -> putWord8 1
                DCon x1 x2 -> do putWord8 2
                                 put x1
                                 put x2
                TCon x1 x2 -> do putWord8 3
                                 put x1
                                 put x2
        get
          = do i <- getWord8
               case i of
                   0 -> return Bound
                   1 -> return Ref
                   2 -> do x1 <- get
                           x2 <- get
                           return (DCon x1 x2)
                   3 -> do x1 <- get
                           x2 <- get
                           return (TCon x1 x2)
                   _ -> error "Corrupted binary data for NameType"

 
instance (Binary n) => Binary (TT n) where
        put x
          = case x of
                P x1 x2 x3 -> do putWord8 0
                                 put x1
                                 put x2
                                 put x3
                V x1 -> do putWord8 1
                           put x1
                Bind x1 x2 x3 -> do putWord8 2
                                    put x1
                                    put x2
                                    put x3
                App x1 x2 -> do putWord8 3
                                put x1
                                put x2
                Constant x1 -> do putWord8 4
                                  put x1
                Set x1 -> do putWord8 5
                             put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (P x1 x2 x3)
                   1 -> do x1 <- get
                           return (V x1)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Bind x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           return (App x1 x2)
                   4 -> do x1 <- get
                           return (Constant x1)
                   5 -> do x1 <- get
                           return (Set x1)
                   _ -> error "Corrupted binary data for TT"

 
instance Binary SC where
        put x
          = case x of
                Case x1 x2 -> do putWord8 0
                                 put x1
                                 put x2
                STerm x1 -> do putWord8 1
                               put x1
                UnmatchedCase x1 -> do putWord8 2
                                       put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           return (Case x1 x2)
                   1 -> do x1 <- get
                           return (STerm x1)
                   2 -> do x1 <- get
                           return (UnmatchedCase x1)
                   _ -> error "Corrupted binary data for SC"

 
instance Binary CaseAlt where
        put x
          = case x of
                ConCase x1 x2 x3 x4 -> do putWord8 0
                                          put x1
                                          put x2
                                          put x3
                                          put x4
                ConstCase x1 x2 -> do putWord8 1
                                      put x1
                                      put x2
                DefaultCase x1 -> do putWord8 2
                                     put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (ConCase x1 x2 x3 x4)
                   1 -> do x1 <- get
                           x2 <- get
                           return (ConstCase x1 x2)
                   2 -> do x1 <- get
                           return (DefaultCase x1)
                   _ -> error "Corrupted binary data for CaseAlt"

 
instance Binary Def where
        put x
          = case x of
                Function x1 x2 -> do putWord8 0
                                     put x1
                                     put x2
                TyDecl x1 x2 -> do putWord8 1
                                   put x1
                                   put x2
                Operator x1 x2 x3 -> do putWord8 2
                                        put x1
                                        put x2
                                        put x3
                CaseOp x1 x2 x3 x4 x5 -> do putWord8 3
                                            put x1
                                            put x2
                                            put x3
                                            put x4
                                            put x5
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           return (Function x1 x2)
                   1 -> do x1 <- get
                           x2 <- get
                           return (TyDecl x1 x2)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Operator x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           x5 <- get
                           return (CaseOp x1 x2 x3 x4 x5)
                   _ -> error "Corrupted binary data for Def"


instance Binary IBCFile where
        put (IBCFile x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
          = do put x1
               put x2
               put x3
               put x4
               put x5
               put x6
               put x7
               put x8
               put x9
               put x10
               put x11
               put x12
               put x13
        get
          = do x1 <- get
               if x1 == ibcVersion then 
                 do x2 <- get
                    x3 <- get
                    x4 <- get
                    x5 <- get
                    x6 <- get
                    x7 <- get
                    x8 <- get
                    x9 <- get
                    x10 <- get
                    x11 <- get
                    x12 <- get
                    x13 <- get
                    return (IBCFile x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
                  else return (initIBC { ver = x1 })
 
instance Binary Fixity where
        put x
          = case x of
                Infixl x1 -> do putWord8 0
                                put x1
                Infixr x1 -> do putWord8 1
                                put x1
                InfixN x1 -> do putWord8 2
                                put x1
                PrefixN x1 -> do putWord8 3
                                 put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Infixl x1)
                   1 -> do x1 <- get
                           return (Infixr x1)
                   2 -> do x1 <- get
                           return (InfixN x1)
                   3 -> do x1 <- get
                           return (PrefixN x1)
                   _ -> error "Corrupted binary data for Fixity"

 
instance Binary FixDecl where
        put (Fix x1 x2)
          = do put x1
               put x2
        get
          = do x1 <- get
               x2 <- get
               return (Fix x1 x2)

 
instance Binary Static where
        put x
          = case x of
                Static -> putWord8 0
                Dynamic -> putWord8 1
        get
          = do i <- getWord8
               case i of
                   0 -> return Static
                   1 -> return Dynamic
                   _ -> error "Corrupted binary data for Static"

 
instance Binary Plicity where
        put x
          = case x of
                Imp x1 x2 -> do putWord8 0
                                put x1
                                put x2
                Exp x1 x2 -> do putWord8 1
                                put x1
                                put x2
                Constraint x1 x2 -> do putWord8 2
                                       put x1
                                       put x2
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           return (Imp x1 x2)
                   1 -> do x1 <- get
                           x2 <- get
                           return (Exp x1 x2)
                   2 -> do x1 <- get
                           x2 <- get
                           return (Constraint x1 x2)
                   _ -> error "Corrupted binary data for Plicity"

 
instance Binary PTerm where
        put x
          = case x of
                PQuote x1 -> do putWord8 0
                                put x1
                PRef x1 x2 -> do putWord8 1
                                 put x1
                                 put x2
                PLam x1 x2 x3 -> do putWord8 2
                                    put x1
                                    put x2
                                    put x3
                PPi x1 x2 x3 x4 -> do putWord8 3
                                      put x1
                                      put x2
                                      put x3
                                      put x4
                PLet x1 x2 x3 x4 -> do putWord8 4
                                       put x1
                                       put x2
                                       put x3
                                       put x4
                PApp x1 x2 x3 -> do putWord8 5
                                    put x1
                                    put x2
                                    put x3
                PTrue x1 -> do putWord8 6
                               put x1
                PFalse x1 -> do putWord8 7
                                put x1
                PRefl x1 -> do putWord8 8
                               put x1
                PResolveTC x1 -> do putWord8 9
                                    put x1
                PEq x1 x2 x3 -> do putWord8 10
                                   put x1
                                   put x2
                                   put x3
                PPair x1 x2 x3 -> do putWord8 11
                                     put x1
                                     put x2
                                     put x3
                PDPair x1 x2 x3 x4 -> do putWord8 12
                                         put x1
                                         put x2
                                         put x3
                                         put x4
                PAlternative x1 -> do putWord8 13
                                      put x1
                PHidden x1 -> do putWord8 14
                                 put x1
                PSet -> putWord8 15
                PConstant x1 -> do putWord8 16
                                   put x1
                Placeholder -> putWord8 17
                PDoBlock x1 -> do putWord8 18
                                  put x1
                PReturn x1 -> do putWord8 19
                                 put x1
                PMetavar x1 -> do putWord8 20
                                  put x1
                PProof x1 -> do putWord8 21
                                put x1
                PTactics x1 -> do putWord8 22
                                  put x1
                PElabError x1 -> do putWord8 23
                                    put x1
                PImpossible -> putWord8 24
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (PQuote x1)
                   1 -> do x1 <- get
                           x2 <- get
                           return (PRef x1 x2)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PLam x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PPi x1 x2 x3 x4)
                   4 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PLet x1 x2 x3 x4)
                   5 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PApp x1 x2 x3)
                   6 -> do x1 <- get
                           return (PTrue x1)
                   7 -> do x1 <- get
                           return (PFalse x1)
                   8 -> do x1 <- get
                           return (PRefl x1)
                   9 -> do x1 <- get
                           return (PResolveTC x1)
                   10 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PEq x1 x2 x3)
                   11 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            return (PPair x1 x2 x3)
                   12 -> do x1 <- get
                            x2 <- get
                            x3 <- get
                            x4 <- get
                            return (PDPair x1 x2 x3 x4)
                   13 -> do x1 <- get
                            return (PAlternative x1)
                   14 -> do x1 <- get
                            return (PHidden x1)
                   15 -> return PSet
                   16 -> do x1 <- get
                            return (PConstant x1)
                   17 -> return Placeholder
                   18 -> do x1 <- get
                            return (PDoBlock x1)
                   19 -> do x1 <- get
                            return (PReturn x1)
                   20 -> do x1 <- get
                            return (PMetavar x1)
                   21 -> do x1 <- get
                            return (PProof x1)
                   22 -> do x1 <- get
                            return (PTactics x1)
                   23 -> do x1 <- get
                            return (PElabError x1)
                   24 -> return PImpossible
                   _ -> error "Corrupted binary data for PTerm"

 
instance (Binary t) => Binary (PTactic' t) where
        put x
          = case x of
                Intro x1 -> do putWord8 0
                               put x1
                Focus x1 -> do putWord8 1
                               put x1
                Refine x1 x2 -> do putWord8 2
                                   put x1
                                   put x2
                Rewrite x1 -> do putWord8 3
                                 put x1
                LetTac x1 x2 -> do putWord8 4
                                   put x1
                                   put x2
                Exact x1 -> do putWord8 5
                               put x1
                Compute -> putWord8 6
                Trivial -> putWord8 7
                Solve -> putWord8 8
                Attack -> putWord8 9
                ProofState -> putWord8 10
                ProofTerm -> putWord8 11
                Undo -> putWord8 12
                Try x1 x2 -> do putWord8 13
                                put x1
                                put x2
                TSeq x1 x2 -> do putWord8 14
                                 put x1
                                 put x2
                Qed -> putWord8 15
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Intro x1)
                   1 -> do x1 <- get
                           return (Focus x1)
                   2 -> do x1 <- get
                           x2 <- get
                           return (Refine x1 x2)
                   3 -> do x1 <- get
                           return (Rewrite x1)
                   4 -> do x1 <- get
                           x2 <- get
                           return (LetTac x1 x2)
                   5 -> do x1 <- get
                           return (Exact x1)
                   6 -> return Compute
                   7 -> return Trivial
                   8 -> return Solve
                   9 -> return Attack
                   10 -> return ProofState
                   11 -> return ProofTerm
                   12 -> return Undo
                   13 -> do x1 <- get
                            x2 <- get
                            return (Try x1 x2)
                   14 -> do x1 <- get
                            x2 <- get
                            return (TSeq x1 x2)
                   15 -> return Qed
                   _ -> error "Corrupted binary data for PTactic'"

 
instance (Binary t) => Binary (PDo' t) where
        put x
          = case x of
                DoExp x1 x2 -> do putWord8 0
                                  put x1
                                  put x2
                DoBind x1 x2 x3 -> do putWord8 1
                                      put x1
                                      put x2
                                      put x3
                DoLet x1 x2 x3 -> do putWord8 2
                                     put x1
                                     put x2
                                     put x3
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           return (DoExp x1 x2)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (DoBind x1 x2 x3)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (DoLet x1 x2 x3)
                   _ -> error "Corrupted binary data for PDo'"

 
instance (Binary t) => Binary (PArg' t) where
        put x
          = case x of
                PImp x1 x2 x3 x4 -> do putWord8 0
                                       put x1
                                       put x2
                                       put x3
                                       put x4
                PExp x1 x2 x3 -> do putWord8 1
                                    put x1
                                    put x2
                                    put x3
                PConstraint x1 x2 x3 -> do putWord8 2
                                           put x1
                                           put x2
                                           put x3
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           x4 <- get
                           return (PImp x1 x2 x3 x4)
                   1 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PExp x1 x2 x3)
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (PConstraint x1 x2 x3)
                   _ -> error "Corrupted binary data for PArg'"

 
instance Binary ClassInfo where
        put (CI x1 x2 x3 x4)
          = do put x1
               put x2
               put x3
               put x4
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               x4 <- get
               return (CI x1 x2 x3 x4)

 
instance Binary SynContext where
        put x
          = case x of
                PatternSyntax -> putWord8 0
                TermSyntax -> putWord8 1
                AnySyntax -> putWord8 2
        get
          = do i <- getWord8
               case i of
                   0 -> return PatternSyntax
                   1 -> return TermSyntax
                   2 -> return AnySyntax
                   _ -> error "Corrupted binary data for SynContext"

 
instance Binary Syntax where
        put (Rule x1 x2 x3)
          = do put x1
               put x2
               put x3
        get
          = do x1 <- get
               x2 <- get
               x3 <- get
               return (Rule x1 x2 x3)

 
instance Binary SSymbol where
        put x
          = case x of
                Keyword x1 -> do putWord8 0
                                 put x1
                Symbol x1 -> do putWord8 1
                                put x1
                Expr x1 -> do putWord8 2
                              put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (Keyword x1)
                   1 -> do x1 <- get
                           return (Symbol x1)
                   2 -> do x1 <- get
                           return (Expr x1)
                   _ -> error "Corrupted binary data for SSymbol"

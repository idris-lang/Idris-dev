{-|
Module      : Idris.Core.Binary
Description : Binary instances for the core datatypes

License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Idris.Core.Binary where

import Idris.Core.TT

import Control.Applicative ((<$>), (<*>))
import Data.Binary
import Data.Binary.Get
import Data.Binary.Put

instance Binary ErrorReportPart
instance Binary Provenance
instance Binary UConstraint
instance Binary ConstraintFC
instance Binary a => Binary (Err' a) where
  put (Msg str) = do putWord8 0
                     put str
  put (InternalMsg str) = do putWord8 1
                             put str
  put (CantUnify x y z e ctxt i) = do putWord8 2
                                      put x
                                      put y
                                      put z
                                      put e
                                      put ctxt
                                      put i
  put (InfiniteUnify n t ctxt) = do putWord8 3
                                    put n
                                    put t
                                    put ctxt
  put (CantConvert x y ctxt) = do putWord8 4
                                  put x
                                  put y
                                  put ctxt
  put (CantSolveGoal x ctxt) = do putWord8 5
                                  put x
                                  put ctxt
  put (UnifyScope n1 n2 x ctxt) = do putWord8 6
                                     put n1
                                     put n2
                                     put x
                                     put ctxt
  put (CantInferType str) = do putWord8 7
                               put str
  put (NonFunctionType t1 t2) = do putWord8 8
                                   put t1
                                   put t2
  put (NotEquality t1 t2) = do putWord8 9
                               put t1
                               put t2
  put (TooManyArguments n) = do putWord8 10
                                put n
  put (CantIntroduce t) = do putWord8 11
                             put t
  put (NoSuchVariable n) = do putWord8 12
                              put n
  put (NoTypeDecl n) = do putWord8 13
                          put n
  put (NotInjective x y z) = do putWord8 14
                                put x
                                put y
                                put z
  put (CantResolve _ t u) = do putWord8 15
                               put t
                               put u
  put (CantResolveAlts ns) = do putWord8 16
                                put ns
  put (IncompleteTerm t) = do putWord8 17
                              put t
  put (UniverseError x1 x2 x3 x4 x5) = do putWord8 18
                                          put x1
                                          put x2
                                          put x3
                                          put x4
                                          put x5
  put (UniqueError u n) = do putWord8 19
                             put u
                             put n
  put (UniqueKindError u n) = do putWord8 20
                                 put u
                                 put n
  put ProgramLineComment = putWord8 21
  put (Inaccessible n) = do putWord8 22
                            put n
  put (NonCollapsiblePostulate n) = do putWord8 23
                                       put n
  put (AlreadyDefined n) = do putWord8 24
                              put n
  put (ProofSearchFail e) = do putWord8 25
                               put e
  put (NoRewriting l r t) = do putWord8 26
                               put l
                               put r
                               put t
  put (At fc e) = do putWord8 27
                     put fc
                     put e
  put (Elaborating str n ty e) = do putWord8 28
                                    put str
                                    put n
                                    put ty
                                    put e
  put (ElaboratingArg n1 n2 ns e) = do putWord8 29
                                       put n1
                                       put n2
                                       put ns
                                       put e
  put (ProviderError str) = do putWord8 30
                               put str
  put (LoadingFailed str e) = do putWord8 31
                                 put str
                                 put e
  put (ReflectionError parts e) = do putWord8 32
                                     put parts
                                     put e
  put (ReflectionFailed str e) = do putWord8 33
                                    put str
                                    put e
  put (WithFnType t) = do putWord8 34
                          put t
  put (CantMatch t) = do putWord8 35
                         put t
  put (ElabScriptDebug x1 x2 x3) = do putWord8 36
                                      put x1
                                      put x2
                                      put x3
  put (InvalidTCArg n t) = do putWord8 38
                              put n
                              put t
  put (ElabScriptStuck x1) = do putWord8 39
                                put x1
  put (UnknownImplicit n f) = do putWord8 40
                                 put n
                                 put f
  put (NoValidAlts ns) = do putWord8 41
                            put ns
  put (RunningElabScript e) = do putWord8 42
                                 put e
  put (ElabScriptStaging n) = do putWord8 43
                                 put n
  put (FancyMsg xs) = do putWord8 44
                         put xs
  get = do i <- getWord8
           case i of
             0 -> fmap Msg get
             1 -> fmap InternalMsg get
             2 -> do x <- get ; y <- get ; z <- get ; e <- get ; ctxt <- get ; i <- get
                     return $ CantUnify x y z e ctxt i
             3 -> do x <- get ; y <- get ; z <- get
                     return $ InfiniteUnify x y z
             4 -> do x <- get ; y <- get ; z <- get
                     return $ CantConvert x y z
             5 -> do x <- get ; y <- get
                     return $ CantSolveGoal x y
             6 -> do w <- get ; x <- get ; y <- get ; z <- get
                     return $ UnifyScope w x y z
             7 -> fmap CantInferType get
             8 -> do x <- get ; y <- get
                     return $ NonFunctionType x y
             9 -> do x <- get ; y <- get
                     return $ NotEquality x y
             10 -> fmap TooManyArguments get
             11 -> fmap CantIntroduce get
             12 -> fmap NoSuchVariable get
             13 -> fmap NoTypeDecl get
             14 -> do x <- get ; y <- get ; z <- get
                      return $ NotInjective x y z
             15 -> CantResolve False <$> get <*> get
             16 -> fmap CantResolveAlts get
             17 -> fmap IncompleteTerm get
             18 -> UniverseError <$> get <*> get <*> get <*> get <*> get
             19 -> do x <- get ; y <- get
                      return $ UniqueError x y
             20 -> do x <- get ; y <- get
                      return $ UniqueKindError x y
             21 -> return ProgramLineComment
             22 -> fmap Inaccessible get
             23 -> fmap NonCollapsiblePostulate get
             24 -> fmap AlreadyDefined get
             25 -> fmap ProofSearchFail get
             26 -> do l <- get; r <- get; t <- get
                      return $ NoRewriting l r t
             27 -> do x <- get ; y <- get
                      return $ At x y
             28 -> do w <- get; x <- get ; y <- get ; z <- get
                      return $ Elaborating w x y z
             29 -> do w <- get ; x <- get ; y <- get ; z <- get
                      return $ ElaboratingArg w x y z
             30 -> fmap ProviderError get
             31 -> do x <- get ; y <- get
                      return $ LoadingFailed x y
             32 -> do x <- get ; y <- get
                      return $ ReflectionError x y
             33 -> do x <- get ; y <- get
                      return $ ReflectionFailed x y
             34 -> fmap WithFnType get
             35 -> fmap CantMatch get
             36 -> do x1 <- get
                      x2 <- get
                      x3 <- get
                      return (ElabScriptDebug x1 x2 x3)
             38 -> do x1 <- get
                      x2 <- get
                      return (InvalidTCArg x1 x2)
             39 -> do x1 <- get
                      return (ElabScriptStuck x1)
             40 -> do x <- get ; y <- get
                      return $ UnknownImplicit x y
             41 -> fmap NoValidAlts get
             42 -> fmap RunningElabScript get
             43 -> fmap ElabScriptStaging get
             44 -> fmap FancyMsg get
             _ -> error "Corrupted binary data for Err'"
----- Generated by 'derive'

instance Binary FC
instance Binary FC'
instance Binary Name
instance Binary SpecialName
instance Binary Const where
        put x
          = case x of
                I x1 -> do putWord8 0
                           put x1
                BI x1 -> do putWord8 1
                            put x1
                Fl x1 -> do putWord8 2
                            putDoublele x1
                Ch x1 -> do putWord8 3
                            put x1
                Str x1 -> do putWord8 4
                             put x1
                B8 x1 -> putWord8 5 >> put x1
                B16 x1 -> putWord8 6 >> put x1
                B32 x1 -> putWord8 7 >> put x1
                B64 x1 -> putWord8 8 >> put x1

                (AType (ATInt ITNative)) -> putWord8 9
                (AType (ATInt ITBig)) -> putWord8 10
                (AType ATFloat) -> putWord8 11
                (AType (ATInt ITChar)) -> putWord8 12
                StrType -> putWord8 13
                Forgot -> putWord8 15
                (AType (ATInt (ITFixed ity))) -> putWord8 (fromIntegral (16 + fromEnum ity)) -- 16-19 inclusive
                VoidType -> putWord8 27
                WorldType -> putWord8 28
                TheWorld -> putWord8 29
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           return (I x1)
                   1 -> do x1 <- get
                           return (BI x1)
                   2 -> do x1 <- getDoublele
                           return (Fl x1)
                   3 -> do x1 <- get
                           return (Ch x1)
                   4 -> do x1 <- get
                           return (Str x1)
                   5 -> fmap B8 get
                   6 -> fmap B16 get
                   7 -> fmap B32 get
                   8 -> fmap B64 get

                   9 -> return (AType (ATInt ITNative))
                   10 -> return (AType (ATInt ITBig))
                   11 -> return (AType ATFloat)
                   12 -> return (AType (ATInt ITChar))
                   13 -> return StrType
                   15 -> return Forgot

                   16 -> return (AType (ATInt (ITFixed IT8)))
                   17 -> return (AType (ATInt (ITFixed IT16)))
                   18 -> return (AType (ATInt (ITFixed IT32)))
                   19 -> return (AType (ATInt (ITFixed IT64)))

                   27 -> return VoidType
                   28 -> return WorldType
                   29 -> return TheWorld
                   _ -> error "Corrupted binary data for Const"

instance Binary Raw
instance Binary RigCount
instance Binary ImplicitInfo where
        put x
          = case x of
                Impl x1 x2 x3 -> do put x1; put x2
        get
          = do x1 <- get
               x2 <- get
               return (Impl x1 x2 False)

instance (Binary b) => Binary (Binder b)
instance Binary Universe
instance Binary NameType
instance Binary UExp
instance Binary (TT Name) where
        put x
          = {-# SCC "putTT" #-}
            case x of
                P x1 x2 x3 -> do putWord8 0
                                 put x1
                                 put x2
--                                  put x3
                V x1 -> if (x1 >= 0 && x1 < 256)
                           then do putWord8 1
                                   putWord8 (toEnum (x1 + 1))
                           else do putWord8 9
                                   put x1
                Bind x1 x2 x3 -> do putWord8 2
                                    put x1
                                    put x2
                                    put x3
                App _ x1 x2 -> do putWord8 3
                                  put x1
                                  put x2
                Constant x1 -> do putWord8 4
                                  put x1
                Proj x1 x2 -> do putWord8 5
                                 put x1
                                 putWord8 (toEnum (x2 + 1))
                Erased -> putWord8 6
                TType x1 -> do putWord8 7
                               put x1
                Impossible -> putWord8 8
                Inferred x1 -> put x1 -- drop the 'Inferred'
                UType x1 -> do putWord8 10
                               put x1
        get
          = do i <- getWord8
               case i of
                   0 -> do x1 <- get
                           x2 <- get
--                            x3 <- get
                           return (P x1 x2 Erased)
                   1 -> do x1 <- getWord8
                           return (V ((fromEnum x1) - 1))
                   2 -> do x1 <- get
                           x2 <- get
                           x3 <- get
                           return (Bind x1 x2 x3)
                   3 -> do x1 <- get
                           x2 <- get
                           return (App Complete x1 x2)
                   4 -> do x1 <- get
                           return (Constant x1)
                   5 -> do x1 <- get
                           x2 <- getWord8
                           return (Proj x1 ((fromEnum x2)-1))
                   6 -> return Erased
                   7 -> do x1 <- get
                           return (TType x1)
                   8 -> return Impossible
                   9 -> do x1 <- get
                           return (V x1)
                   10 -> do x1 <- get
                            return (UType x1)
                   _ -> error "Corrupted binary data for TT"

{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module Idris.Primitives(elabPrims) where

import Idris.ElabDecls
import Idris.AbsSyntax

import Core.TT
import Core.Evaluate

import Epic.Epic hiding (Term, Type, Name, fn)
import qualified Epic.Epic as E

data Prim = Prim { p_name  :: Name,
                   p_type  :: Type,
                   p_arity :: Int,
                   p_def   :: [Value] -> Maybe Value,
                   p_epic  :: ([E.Name], E.Term)
                 }

ty []     x = Constant x
ty (t:ts) x = Bind (MN 0 "T") (Pi (Constant t)) (ty ts x)

type ETm = E.Term
type EOp = E.Op

fun = E.fn
ref = E.ref

eOp :: EOp -> ([E.Name], ETm)
eOp op = ([E.name "x", E.name "y"], E.op_ op (E.fn "x") (E.fn "y")) 

primitives =
  [Prim (UN ["prim__addInt"]) (ty [IType, IType] IType) 2 (iBin (+))
    (eOp E.plus_),
   Prim (UN ["prim__subInt"]) (ty [IType, IType] IType) 2 (iBin (-))
    (eOp E.minus_),
   Prim (UN ["prim__mulInt"]) (ty [IType, IType] IType) 2 (iBin (*))
    (eOp E.times_),
   Prim (UN ["prim__divInt"]) (ty [IType, IType] IType) 2 (iBin (div))
    (eOp E.divide_),
   Prim (UN ["prim__eqInt"])  (ty [IType, IType] IType) 2 (biBin (==))
    (eOp E.eq_),
   Prim (UN ["prim__ltInt"])  (ty [IType, IType] IType) 2 (biBin (<))
    (eOp E.lt_),
   Prim (UN ["prim__lteInt"]) (ty [IType, IType] IType) 2 (biBin (<=))
    (eOp E.lte_),
   Prim (UN ["prim__gtInt"])  (ty [IType, IType] IType) 2 (biBin (>))
    (eOp E.gt_),
   Prim (UN ["prim__gteInt"]) (ty [IType, IType] IType) 2 (biBin (>=))
    (eOp E.gte_),
   Prim (UN ["prim__addFloat"]) (ty [FlType, FlType] FlType) 2 (fBin (+))
    (eOp E.plusF_),
   Prim (UN ["prim__subFloat"]) (ty [FlType, FlType] FlType) 2 (fBin (-))
    (eOp E.minusF_),
   Prim (UN ["prim__mulFloat"]) (ty [FlType, FlType] FlType) 2 (fBin (*))
    (eOp E.timesF_),
   Prim (UN ["prim__divFloat"]) (ty [FlType, FlType] FlType) 2 (fBin (/))
    (eOp E.divideF_),
   Prim (UN ["prim__eqFloat"])  (ty [FlType, FlType] IType) 2 (bfBin (==))
    (eOp E.eqF_),
   Prim (UN ["prim__ltFloat"])  (ty [FlType, FlType] IType) 2 (bfBin (<))
    (eOp E.ltF_),
   Prim (UN ["prim__lteFloat"]) (ty [FlType, FlType] IType) 2 (bfBin (<=))
    (eOp E.lteF_),
   Prim (UN ["prim__gtFloat"])  (ty [FlType, FlType] IType) 2 (bfBin (>))
    (eOp E.gtF_),
   Prim (UN ["prim__gteFloat"]) (ty [FlType, FlType] IType) 2 (bfBin (>=))
    (eOp E.gteF_),
   Prim (UN ["prim__concat"]) (ty [StrType, StrType] StrType) 2 (sBin (++))
    ([E.name "x", E.name "y"], (fun "append") @@ fun "x" @@ fun "y")
  ]

iBin op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (op x y))
iBin _ _ = Nothing

biBin op = iBin (\x y -> if (op x y) then 1 else 0)

fBin op [VConstant (Fl x), VConstant (Fl y)] = Just $ VConstant (Fl (op x y))
fBin _ _ = Nothing

bfBin op [VConstant (Fl x), VConstant (Fl y)] = let i = (if op x y then 1 else 0) in
                                                Just $ VConstant (I i)
bfBin _ _ = Nothing

sBin op [VConstant (Str x), VConstant (Str y)] = Just $ VConstant (Str (op x y))
sBin _ _ = Nothing

elabPrim :: Prim -> Idris ()
elabPrim (Prim n ty i def epic) 
    = do updateContext (addOperator n ty i def)
         i <- getIState
         putIState i { idris_prims = (n, epic) : idris_prims i }

elabPrims :: Idris ()
elabPrims = do mapM_ (elabDecl toplevel) 
                     (map PData 
                         [inferDecl, unitDecl, falseDecl, pairDecl])
               mapM_ elabPrim primitives


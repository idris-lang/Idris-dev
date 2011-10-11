module Idris.Primitives(elabPrims) where

import Idris.ElabDecls
import Idris.AbsSyntax

import Core.TT
import Core.Evaluate

data Prim = Prim { p_name  :: Name,
                   p_type  :: Type,
                   p_arity :: Int,
                   p_def   :: [Value] -> Maybe Value
                 }

ty []     x = Constant x
ty (t:ts) x = Bind (MN 0 "T") (Pi (Constant t)) (ty ts x)

primitives =
  [Prim (UN ["prim__addInt"]) (ty [IType, IType] IType) 2 (iBin (+)),
   Prim (UN ["prim__subInt"]) (ty [IType, IType] IType) 2 (iBin (-)),
   Prim (UN ["prim__mulInt"]) (ty [IType, IType] IType) 2 (iBin (*)),
   Prim (UN ["prim__divInt"]) (ty [IType, IType] IType) 2 (iBin (div)),
   Prim (UN ["prim__eqInt"])  (ty [IType, IType] IType) 2 (biBin (==)),
   Prim (UN ["prim__ltInt"])  (ty [IType, IType] IType) 2 (biBin (<)),
   Prim (UN ["prim__lteInt"]) (ty [IType, IType] IType) 2 (biBin (<=)),
   Prim (UN ["prim__gtInt"])  (ty [IType, IType] IType) 2 (biBin (>)),
   Prim (UN ["prim__gteInt"]) (ty [IType, IType] IType) 2 (biBin (>=)),
   Prim (UN ["prim__addFloat"]) (ty [FlType, FlType] FlType) 2 (fBin (+)),
   Prim (UN ["prim__subFloat"]) (ty [FlType, FlType] FlType) 2 (fBin (-)),
   Prim (UN ["prim__mulFloat"]) (ty [FlType, FlType] FlType) 2 (fBin (*)),
   Prim (UN ["prim__divFloat"]) (ty [FlType, FlType] FlType) 2 (fBin (/)),
   Prim (UN ["prim__eqFloat"])  (ty [FlType, FlType] IType) 2 (bfBin (==)),
   Prim (UN ["prim__ltFloat"])  (ty [FlType, FlType] IType) 2 (bfBin (<)),
   Prim (UN ["prim__lteFloat"]) (ty [FlType, FlType] IType) 2 (bfBin (<=)),
   Prim (UN ["prim__gtFloat"])  (ty [FlType, FlType] IType) 2 (bfBin (>)),
   Prim (UN ["prim__gteFloat"]) (ty [FlType, FlType] IType) 2 (bfBin (>=))
  ]

iBin op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (op x y))
iBin _ _ = Nothing

biBin op = iBin (\x y -> if (op x y) then 1 else 0)

fBin op [VConstant (Fl x), VConstant (Fl y)] = Just $ VConstant (Fl (op x y))
fBin _ _ = Nothing

bfBin op [VConstant (Fl x), VConstant (Fl y)] = let i = (if op x y then 1 else 0) in
                                                Just $ VConstant (I i)
bfBin _ _ = Nothing

elabPrim :: Prim -> Idris ()
elabPrim (Prim n ty i def) = updateContext (addOperator n ty i def)

elabPrims :: Idris ()
elabPrims = do elabDecl (PData inferDecl) 
               mapM_ elabPrim primitives


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
  [Prim (UN ["prim__addInt"]) (ty [IType, IType] IType) 2 (vBin (+)),
   Prim (UN ["prim__subInt"]) (ty [IType, IType] IType) 2 (vBin (-)),
   Prim (UN ["prim__mulInt"]) (ty [IType, IType] IType) 2 (vBin (*)),
   Prim (UN ["prim__divInt"]) (ty [IType, IType] IType) 2 (vBin (div)),
   Prim (UN ["prim__eqInt"])  (ty [IType, IType] IType) 2 (bBin (==)),
   Prim (UN ["prim__ltInt"])  (ty [IType, IType] IType) 2 (bBin (<)),
   Prim (UN ["prim__lteInt"]) (ty [IType, IType] IType) 2 (bBin (<=)),
   Prim (UN ["prim__gtInt"])  (ty [IType, IType] IType) 2 (bBin (>)),
   Prim (UN ["prim__gteInt"]) (ty [IType, IType] IType) 2 (bBin (>=))
  ]

vBin op [VConstant (I x), VConstant (I y)] = Just $ VConstant (I (op x y))
vBin _ _ = Nothing

bBin op = vBin (\x y -> if (op x y) then 1 else 0)

elabPrim :: Prim -> Idris ()
elabPrim (Prim n ty i def) = updateContext (addOperator n ty i def)

elabPrims :: Idris ()
elabPrims = do elabDecl (PData inferDecl) 
               mapM_ elabPrim primitives


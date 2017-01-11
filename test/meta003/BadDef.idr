module BadDef

import Language.Reflection.Elab

%language ElabReflection

mkN : String -> TTName
mkN n = NS (UN n) ["BadDef"]

mkBadDef1 : Elab ()
mkBadDef1 = do declareType $ Declare (mkN "bad1") [] `(() -> ())
               defineFunction $ DefineFun (mkN "bad1") [MkFunClause `(():()) `("hi")]

%runElab mkBadDef1

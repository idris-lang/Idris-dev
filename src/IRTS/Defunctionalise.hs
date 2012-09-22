module IRTS.Defunctionalise where

import IRTS.Lang
import Core.TT

import Debug.Trace
import Data.Maybe
import Data.List

defunctionalise :: Int -> LDefs -> LDefs 
defunctionalise nexttag defs 
     = let all = toAlist defs
           -- sort newcons so that EVAL and APPLY cons get sequential tags
           newcons = sortBy conord $ concatMap toCons (getFn all)
           eval = mkEval newcons
           app = mkApply newcons
           condecls = declare nexttag newcons in
           addAlist (eval : app : condecls ++ (map (addApps defs) all)) emptyContext
   where conord (n, _, _) (n', _, _) = compare n n'

getFn :: [(Name, LDecl)] -> [(Name, Int)]
getFn xs = mapMaybe fnData xs
  where fnData (n, LFun _ args _) = Just (n, length args) 
        fnData _ = Nothing

-- To defunctionalise:
--
-- 1 Create a data constructor for each function
-- 2 Create a data constructor for each underapplication of a function
-- 3 Convert underapplications to their corresponding constructors
-- 4 Create an EVAL function which calls the appropriate function for data constructors
--   created as part of step 1
-- 5 Create an APPLY function which adds an argument to each underapplication (or calls
--   APPLY again for an exact application)
-- 6 Wrap overapplications in chains of APPLY
-- 7 Wrap unknown applications (i.e. applications of local variables) in chains of APPLY
-- 8 Add explicit EVAL to case, primitives, and foreign calls

addApps :: LDefs -> (Name, LDecl) -> (Name, LDecl)
addApps defs o@(n, LConstructor _ _ _) = o
addApps defs (n, LFun _ args e) = (n, LFun n args (aa args e))
  where
    aa env (LV (Glob n)) | n `elem` env = LV (Glob n)
                         | otherwise = aa env (LApp False (LV (Glob n)) [])
--     aa env e@(LApp tc (MN 0 "EVAL") [a]) = e
    aa env (LApp tc (LV (Glob n)) args)
       = let args' = map (aa env) args in
             case lookupCtxt Nothing n defs of
                [LConstructor _ i ar] -> LApp tc (LV (Glob n)) args'
                [LFun _ as _] -> let arity = length as in
                                     fixApply tc n args' arity
                [] -> chainAPPLY (LV (Glob n)) args'
    aa env (LLazyApp n args)
       = let args' = map (aa env) args in
             case lookupCtxt Nothing n defs of
                [LConstructor _ i ar] -> LApp False (LV (Glob n)) args'
                [LFun _ as _] -> let arity = length as in
                                     fixLazyApply n args' arity
                [] -> chainAPPLY (LV (Glob n)) args'
    aa env (LForce e) = eEVAL (aa env e)
    aa env (LLet n v sc) = LLet n (aa env v) (aa (n : env) sc)
    aa env (LCon i n args) = LCon i n (map (aa env) args)
    aa env (LCase e alts) = LCase (eEVAL (aa env e)) (map (aaAlt env) alts)
    aa env (LConst c) = LConst c
    aa env (LForeign l t n args) = LForeign l t n (map (aaF env) args)
    aa env (LOp LFork args) = LOp LFork (map (aa env) args)
    aa env (LOp f args) = LOp f (map (eEVAL . (aa env)) args)
    aa env (LError e) = LError e

    aaF env (t, e) = (t, eEVAL (aa env e))

    aaAlt env (LConCase i n args e) = LConCase i n args (aa (args ++ env) e)
    aaAlt env (LConstCase c e) = LConstCase c (aa env e)
    aaAlt env (LDefaultCase e) = LDefaultCase (aa env e)

    fixApply tc n args ar 
        | length args == ar = LApp tc (LV (Glob n)) args
        | length args < ar = LApp tc (LV (Glob (mkUnderCon n (ar - length args)))) args
        | length args > ar = chainAPPLY (LApp tc (LV (Glob n)) (take ar args)) (drop ar args)

    fixLazyApply n args ar 
        | length args == ar = LApp False (LV (Glob (mkFnCon n))) args
        | length args < ar = LApp False (LV (Glob (mkUnderCon n (ar - length args)))) args
        | length args > ar = chainAPPLY (LApp False (LV (Glob n)) (take ar args)) (drop ar args)
                                    
    chainAPPLY f [] = f
    chainAPPLY f (a : as) = chainAPPLY (LApp False (LV (Glob (MN 0 "APPLY"))) [f, a]) as

eEVAL x = LApp False (LV (Glob (MN 0 "EVAL"))) [x]

data EvalApply a = EvalCase a
                 | ApplyCase a
    deriving Show

-- For a function name, generate a list of
-- data constuctors, and whether to handle them in EVAL or APPLY

toCons :: (Name, Int) -> [(Name, Int, EvalApply LAlt)]
toCons (n, i) 
   = (mkFnCon n, i, 
        EvalCase (LConCase (-1) (mkFnCon n) (take i (genArgs 0))
                 (eEVAL (LApp False (LV (Glob n)) (map (LV . Glob) (take i (genArgs 0)))))))
        : mkApplyCase n 0 i

mkApplyCase fname n ar | n == ar = []
mkApplyCase fname n ar 
        = let nm = mkUnderCon fname (ar - n) in
              (nm, n, ApplyCase (LConCase (-1) nm (take n (genArgs 0))
                              (LApp False (LV (Glob (mkUnderCon fname (ar - (n + 1))))) 
                                          (map (LV . Glob) (take n (genArgs 0) ++ 
                                                                   [MN 0 "arg"])))))
                            : mkApplyCase fname (n + 1) ar

mkEval :: [(Name, Int, EvalApply LAlt)] -> (Name, LDecl)
mkEval xs = (MN 0 "EVAL", LFun (MN 0 "EVAL") [MN 0 "arg"]
                             (LCase (LV (Glob (MN 0 "arg")))
                                 (mapMaybe evalCase xs ++
                                   [LDefaultCase (LV (Glob (MN 0 "arg")))])))
  where
    evalCase (n, t, EvalCase x) = Just x
    evalCase _ = Nothing

mkApply :: [(Name, Int, EvalApply LAlt)] -> (Name, LDecl)
mkApply xs = (MN 0 "APPLY", LFun (MN 0 "APPLY") [MN 0 "fn", MN 0 "arg"]
                             (LCase (LApp False (LV (Glob (MN 0 "EVAL"))) 
                                            [LV (Glob (MN 0 "fn"))])
                                 (mapMaybe applyCase xs)))
  where
    applyCase (n, t, ApplyCase x) = Just x
    applyCase _ = Nothing

declare :: Int -> [(Name, Int, EvalApply LAlt)] -> [(Name, LDecl)]
declare t xs = dec' t xs [] where
   dec' t [] acc = reverse acc
   dec' t ((n, ar, _) : xs) acc = dec' (t + 1) xs ((n, LConstructor n t ar) : acc)


genArgs i = MN i "P_c" : genArgs (i + 1)

mkFnCon    n = MN 0 ("P_" ++ show n)
mkUnderCon n 0       = n
mkUnderCon n missing = MN missing ("U_" ++ show n)


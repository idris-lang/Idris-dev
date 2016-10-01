{-|
Module      : IRTS.Defunctionalise
Description : Defunctionalise Idris' IR.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.

To defunctionalise:

1. Create a data constructor for each function
2. Create a data constructor for each underapplication of a function
3. Convert underapplications to their corresponding constructors
4. Create an EVAL function which calls the appropriate function for data constructors
   created as part of step 1
5. Create an APPLY function which adds an argument to each underapplication (or calls
   APPLY again for an exact application)
6. Wrap overapplications in chains of APPLY
7. Wrap unknown applications (i.e. applications of local variables) in chains of APPLY
8. Add explicit EVAL to case, primitives, and foreign calls

-}
{-# LANGUAGE PatternGuards #-}
module IRTS.Defunctionalise(module IRTS.Defunctionalise
                          , module IRTS.Lang
                          ) where

import Idris.Core.CaseTree
import Idris.Core.TT
import IRTS.Lang

import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe
import Debug.Trace

data DExp = DV LVar
          | DApp Bool Name [DExp] -- True = tail call
          | DLet Name DExp DExp -- name just for pretty printing
          | DUpdate Name DExp -- eval expression, then update var with it
          | DProj DExp Int
          | DC (Maybe LVar) Int Name [DExp]
          | DCase CaseType DExp [DAlt]
          | DChkCase DExp [DAlt] -- a case where the type is unknown (for EVAL/APPLY)
          | DConst Const
          | DForeign FDesc FDesc [(FDesc, DExp)]
          | DOp PrimFn [DExp]
          | DNothing -- erased value, can be compiled to anything since it'll never
                     -- be inspected
          | DError String
  deriving Eq

data DAlt = DConCase Int Name [Name] DExp
          | DConstCase Const DExp
          | DDefaultCase DExp
  deriving (Show, Eq)

data DDecl = DFun Name [Name] DExp -- name, arg names, definition
           | DConstructor Name Int Int -- constructor name, tag, arity
  deriving (Show, Eq)

type DDefs = Ctxt DDecl

defunctionalise :: Int -> LDefs -> DDefs
defunctionalise nexttag defs
     = let all = toAlist defs
           -- sort newcons so that EVAL and APPLY cons get sequential tags
           (allD, (enames, anames)) = runState (mapM (addApps defs) all) ([], [])
           anames' = sort (nub anames)
           enames' = nub enames
           newecons = sortBy conord $ concatMap (toCons enames') (getFn all)
           newacons = sortBy conord $ concatMap (toConsA anames') (getFn all)
           eval = mkEval newecons
           app = mkApply newacons
           app2 = mkApply2 newacons
           condecls = declare nexttag (newecons ++ newacons) in
           addAlist (eval : app : app2 : condecls ++ allD) emptyContext
   where conord (n, _, _) (n', _, _) = compare n n'

getFn :: [(Name, LDecl)] -> [(Name, Int)]
getFn xs = mapMaybe fnData xs
  where fnData (n, LFun _ _ args _) = Just (n, length args)
        fnData _ = Nothing

addApps :: LDefs -> (Name, LDecl) -> State ([Name], [(Name, Int)]) (Name, DDecl)
addApps defs o@(n, LConstructor _ t a)
    = return (n, DConstructor n t a)
addApps defs (n, LFun _ _ args e)
    = do e' <- aa args e
         return (n, DFun n args e')
  where
    aa :: [Name] -> LExp -> State ([Name], [(Name, Int)]) DExp
    aa env (LV (Glob n)) | n `elem` env = return $ DV (Glob n)
                         | otherwise = aa env (LApp False (LV (Glob n)) [])
    aa env (LApp tc (LV (Glob n)) args)
       = do args' <- mapM (aa env) args
            case lookupCtxtExact n defs of
                Just (LConstructor _ i ar) -> return $ DApp tc n args'
                Just (LFun _ _ as _) -> let arity = length as in
                                               fixApply tc n args' arity
                Nothing -> return $ chainAPPLY (DV (Glob n)) args'
    aa env (LLazyApp n args)
       = do args' <- mapM (aa env) args
            case lookupCtxtExact n defs of
                Just (LConstructor _ i ar) -> return $ DApp False n args'
                Just (LFun _ _ as _) -> let arity = length as in
                                           fixLazyApply n args' arity
                Nothing -> return $ chainAPPLY (DV (Glob n)) args'
    aa env (LForce (LLazyApp n args)) = aa env (LApp False (LV (Glob n)) args)
    aa env (LForce e) = liftM eEVAL (aa env e)
    aa env (LLet n v sc) = liftM2 (DLet n) (aa env v) (aa (n : env) sc)
    aa env (LCon loc i n args) = liftM (DC loc i n) (mapM (aa env) args)
    aa env (LProj t@(LV (Glob n)) i)
        | n `elem` env = do t' <- aa env t
                            return $ DProj (DUpdate n t') i
    aa env (LProj t i) = do t' <- aa env t
                            return $ DProj t' i
    aa env (LCase up e alts) = do e' <- aa env e
                                  alts' <- mapM (aaAlt env) alts
                                  return $ DCase up e' alts'
    aa env (LConst c) = return $ DConst c
    aa env (LForeign t n args)
        = do args' <- mapM (aaF env) args
             return $ DForeign t n args'
    aa env (LOp LFork args) = liftM (DOp LFork) (mapM (aa env) args)
    aa env (LOp f args) = do args' <- mapM (aa env) args
                             return $ DOp f args'
    aa env LNothing = return DNothing
    aa env (LError e) = return $ DError e

    aaF env (t, e) = do e' <- aa env e
                        return (t, e')

    aaAlt env (LConCase i n args e)
         = liftM (DConCase i n args) (aa (args ++ env) e)
    aaAlt env (LConstCase c e) = liftM (DConstCase c) (aa env e)
    aaAlt env (LDefaultCase e) = liftM DDefaultCase (aa env e)

    fixApply tc n args ar
        | length args == ar
             = return $ DApp tc n args
        | length args < ar
             = do (ens, ans) <- get
                  let alln = map (\x -> (n, x)) [length args .. ar]
                  put (ens, alln ++ ans)
                  return $ DApp tc (mkUnderCon n (ar - length args)) args
        | length args > ar
             = return $ chainAPPLY (DApp tc n (take ar args)) (drop ar args)

    fixLazyApply n args ar
        | length args == ar
             = do (ens, ans) <- get
                  put (n : ens, ans)
                  return $ DApp False (mkFnCon n) args
        | length args < ar
             = do (ens, ans) <- get
                  let alln = map (\x -> (n, x)) [length args .. ar]
                  put (ens, alln ++ ans)
                  return $ DApp False (mkUnderCon n (ar - length args)) args
        | length args > ar
             = return $ chainAPPLY (DApp False n (take ar args)) (drop ar args)

    chainAPPLY f [] = f
--     chainAPPLY f (a : b : as)
--          = chainAPPLY (DApp False (sMN 0 "APPLY2") [f, a, b]) as
    chainAPPLY f (a : as) = chainAPPLY (DApp False (sMN 0 "APPLY") [f, a]) as

    -- if anything in the DExp is projected from, we'll need to evaluate it,
    -- but we only want to do it once, rather than every time we project.

    preEval [] t = t
    preEval (x : xs) t
       | needsEval x t = DLet x (DV (Glob x)) (preEval xs t)
       | otherwise = preEval xs t

    needsEval x (DApp _ _ args) = any (needsEval x) args
    needsEval x (DC _ _ _ args) = any (needsEval x) args
    needsEval x (DCase up e alts) = needsEval x e || any nec alts
      where nec (DConCase _ _ _ e) = needsEval x e
            nec (DConstCase _ e) = needsEval x e
            nec (DDefaultCase e) = needsEval x e
    needsEval x (DChkCase e alts) = needsEval x e || any nec alts
      where nec (DConCase _ _ _ e) = needsEval x e
            nec (DConstCase _ e) = needsEval x e
            nec (DDefaultCase e) = needsEval x e
    needsEval x (DLet n v e)
          | x == n = needsEval x v
          | otherwise = needsEval x v || needsEval x e
    needsEval x (DForeign _ _ args) = any (needsEval x) (map snd args)
    needsEval x (DOp op args) = any (needsEval x) args
    needsEval x (DProj (DV (Glob x')) _) = x == x'
    needsEval x _ = False

eEVAL x = DApp False (sMN 0 "EVAL") [x]

data EvalApply a = EvalCase (Name -> a)
                 | ApplyCase a
                 | Apply2Case a

-- For a function name, generate a list of
-- data constuctors, and whether to handle them in EVAL or APPLY

toCons :: [Name] -> (Name, Int) -> [(Name, Int, EvalApply DAlt)]
toCons ns (n, i)
    | n `elem` ns
      = (mkFnCon n, i,
          EvalCase (\tlarg ->
            (DConCase (-1) (mkFnCon n) (take i (genArgs 0))
              (dupdate tlarg
                (DApp False n (map (DV . Glob) (take i (genArgs 0))))))))
          : [] -- mkApplyCase n 0 i
    | otherwise = []
  where dupdate tlarg x = DUpdate tlarg x

toConsA :: [(Name, Int)] -> (Name, Int) -> [(Name, Int, EvalApply DAlt)]
toConsA ns (n, i)
    | Just ar <- lookup n ns
--       = (mkFnCon n, i,
--           EvalCase (\tlarg ->
--             (DConCase (-1) (mkFnCon n) (take i (genArgs 0))
--               (dupdate tlarg
--                 (DApp False n (map (DV . Glob) (take i (genArgs 0))))))))
          = mkApplyCase n ar i
    | otherwise = []
  where dupdate tlarg x = x

mkApplyCase fname n ar | n == ar = []
mkApplyCase fname n ar
        = let nm = mkUnderCon fname (ar - n) in
              (nm, n, ApplyCase (DConCase (-1) nm (take n (genArgs 0))
                  (DApp False (mkUnderCon fname (ar - (n + 1)))
                       (map (DV . Glob) (take n (genArgs 0) ++
                         [sMN 0 "arg"])))))
                            :
              if (ar - (n + 2) >=0 )
                 then (nm, n, Apply2Case (DConCase (-1) nm (take n (genArgs 0))
                      (DApp False (mkUnderCon fname (ar - (n + 2)))
                       (map (DV . Glob) (take n (genArgs 0) ++
                         [sMN 0 "arg0", sMN 0 "arg1"])))))
                            :
                            mkApplyCase fname (n + 1) ar
                 else mkApplyCase fname (n + 1) ar

mkEval :: [(Name, Int, EvalApply DAlt)] -> (Name, DDecl)
mkEval xs = (sMN 0 "EVAL", DFun (sMN 0 "EVAL") [sMN 0 "arg"]
               (mkBigCase (sMN 0 "EVAL") 256 (DV (Glob (sMN 0 "arg")))
                  (mapMaybe evalCase xs ++
                      [DDefaultCase (DV (Glob (sMN 0 "arg")))])))
  where
    evalCase (n, t, EvalCase x) = Just (x (sMN 0 "arg"))
    evalCase _ = Nothing

mkApply :: [(Name, Int, EvalApply DAlt)] -> (Name, DDecl)
mkApply xs = (sMN 0 "APPLY", DFun (sMN 0 "APPLY") [sMN 0 "fn", sMN 0 "arg"]
                             (case mapMaybe applyCase xs of
                                [] -> DNothing
                                cases ->
                                    mkBigCase (sMN 0 "APPLY") 256
                                               (DV (Glob (sMN 0 "fn")))
                                              (cases ++
                                    [DDefaultCase DNothing])))
  where
    applyCase (n, t, ApplyCase x) = Just x
    applyCase _ = Nothing

mkApply2 :: [(Name, Int, EvalApply DAlt)] -> (Name, DDecl)
mkApply2 xs = (sMN 0 "APPLY2", DFun (sMN 0 "APPLY2") [sMN 0 "fn", sMN 0 "arg0", sMN 0 "arg1"]
                             (case mapMaybe applyCase xs of
                                [] -> DNothing
                                cases ->
                                    mkBigCase (sMN 0 "APPLY") 256
                                               (DV (Glob (sMN 0 "fn")))
                                              (cases ++
                                    [DDefaultCase
                                       (DApp False (sMN 0 "APPLY")
                                       [DApp False (sMN 0 "APPLY")
                                              [DV (Glob (sMN 0 "fn")),
                                               DV (Glob (sMN 0 "arg0"))],
                                               DV (Glob (sMN 0 "arg1"))])
                                               ])))
  where
    applyCase (n, t, Apply2Case x) = Just x
    applyCase _ = Nothing


declare :: Int -> [(Name, Int, EvalApply DAlt)] -> [(Name, DDecl)]
declare t xs = dec' t xs [] where
   dec' t [] acc = reverse acc
   dec' t ((n, ar, _) : xs) acc = dec' (t + 1) xs ((n, DConstructor n t ar) : acc)


genArgs i = sMN i "P_c" : genArgs (i + 1)

mkFnCon    n = sMN 0 ("P_" ++ show n)
mkUnderCon n 0       = n
mkUnderCon n missing = sMN missing ("U_" ++ show n)

instance Show DExp where
   show e = show' [] e where
     show' env (DV (Loc i)) = "var " ++ env!!i
     show' env (DV (Glob n)) = "GLOB " ++ show n
     show' env (DApp _ e args) = show e ++ "(" ++
                                   showSep ", " (map (show' env) args) ++")"
     show' env (DLet n v e) = "let " ++ show n ++ " = " ++ show' env v ++ " in " ++
                               show' (env ++ [show n]) e
     show' env (DUpdate n e) = "!update " ++ show n ++ "(" ++ show' env e ++ ")"
     show' env (DC loc i n args) = atloc loc ++ "CON " ++ show n ++ "(" ++ showSep ", " (map (show' env) args) ++ ")"
       where atloc Nothing = ""
             atloc (Just l) = "@" ++ show (LV l) ++ ":"
     show' env (DProj t i) = show t ++ "!" ++ show i
     show' env (DCase up e alts) = "case" ++ update ++ show' env e ++ " of {\n\t" ++
                                    showSep "\n\t| " (map (showAlt env) alts)
         where update = case up of
                           Shared -> " "
                           Updatable -> "! "
     show' env (DChkCase e alts) = "case' " ++ show' env e ++ " of {\n\t" ++
                                    showSep "\n\t| " (map (showAlt env) alts)
     show' env (DConst c) = show c
     show' env (DForeign ty n args)
           = "foreign " ++ show n ++ "(" ++ showSep ", " (map (show' env) (map snd args)) ++ ")"
     show' env (DOp f args) = show f ++ "(" ++ showSep ", " (map (show' env) args) ++ ")"
     show' env (DError str) = "error " ++ show str
     show' env DNothing = "____"

     showAlt env (DConCase _ n args e)
          = show n ++ "(" ++ showSep ", " (map show args) ++ ") => "
             ++ show' env e
     showAlt env (DConstCase c e) = show c ++ " => " ++ show' env e
     showAlt env (DDefaultCase e) = "_ => " ++ show' env e

-- | Divide up a large case expression so that each has a maximum of
-- 'max' branches
mkBigCase cn max arg branches
   | length branches <= max = DChkCase arg branches
   | otherwise = -- DChkCase arg branches -- until I think of something...
       -- divide the branches into groups of at most max (by tag),
       -- generate a new case and shrink, recursively
       let bs = sortBy tagOrd branches
           (all, def) = case (last bs) of
                    DDefaultCase t -> (init all, Just (DDefaultCase t))
                    _ -> (all, Nothing)
           bss = groupsOf max all
           cs = map mkCase bss in
           DChkCase arg branches

    where mkCase bs = DChkCase arg bs

          tagOrd (DConCase t _ _ _) (DConCase t' _ _ _) = compare t t'
          tagOrd (DConstCase c _) (DConstCase c' _) = compare c c'
          tagOrd (DDefaultCase _) (DDefaultCase _) = EQ

          tagOrd (DConCase _ _ _ _) (DDefaultCase _) = LT
          tagOrd (DConCase _ _ _ _) (DConstCase _ _) = LT
          tagOrd (DConstCase _ _) (DDefaultCase _) = LT

          tagOrd (DDefaultCase _) (DConCase _ _ _ _) = GT
          tagOrd (DConstCase _ _) (DConCase _ _ _ _) = GT
          tagOrd (DDefaultCase _) (DConstCase _ _) = GT

groupsOf :: Int -> [DAlt] -> [[DAlt]]
groupsOf x [] = []
groupsOf x xs = let (batch, rest) = span (tagLT (x + tagHead xs)) xs in
                    batch : groupsOf x rest
  where tagHead (DConstCase (I i) _ : _) = i
        tagHead (DConCase t _ _ _ : _) = t
        tagHead (DDefaultCase _ : _) = -1 -- must be the end

        tagLT i (DConstCase (I j) _) = i < j
        tagLT i (DConCase j _ _ _) = i < j
        tagLT i (DDefaultCase _) = False

dumpDefuns :: DDefs -> String
dumpDefuns ds = showSep "\n" $ map showDef (toAlist ds)
  where showDef (x, DFun fn args exp)
            = show fn ++ "(" ++ showSep ", " (map show args) ++ ") = \n\t" ++
              show exp ++ "\n"
        showDef (x, DConstructor n t a) = "Constructor " ++ show n ++ " " ++ show t

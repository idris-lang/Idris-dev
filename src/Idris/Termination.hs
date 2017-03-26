{-|
Module      : Idris.Termination
Description : The termination checker for Idris
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
{-# LANGUAGE PatternGuards #-}
module Idris.Termination where

import Idris.AbsSyntax
import Idris.Core.CaseTree
import Idris.Core.Evaluate
import Idris.Core.TT
import Idris.Delaborate
import Idris.Error
import Idris.Output (iWarn, iputStrLn)

import Control.Monad.State.Strict
import Data.Char
import Data.Either
import Data.List
import Data.Maybe
import Debug.Trace

-- | Check whether function and all descendants cover all cases
-- (partial is okay, as long as it's due to recursion)
checkAllCovering :: FC -> [Name] -> Name -> Name -> Idris ()
checkAllCovering fc done top n | not (n `elem` done)
   = do i <- get
        case lookupTotal n (tt_ctxt i) of
             [tot@(Partial NotCovering)] ->
                    do let msg = show top ++ " is " ++ show tot ++ " due to " ++ show n
                       putIState i { idris_totcheckfail = (fc, msg) : idris_totcheckfail i }
                       addIBC (IBCTotCheckErr fc msg)
             [Partial _] ->
                case lookupCtxt n (idris_callgraph i) of
                     [cg] -> mapM_ (checkAllCovering fc (n : done) top)
                                   (calls cg)
                     _ -> return ()
             x -> return () -- stop if total
checkAllCovering _ _ _ _ = return ()

-- | Check whether all 'Inf' arguments to the name end up guaranteed to be
-- guarded by constructors (conservatively... maybe this can do better later).
-- Essentially, all it does is check that every branch is a constructor application
-- with no other function applications.
--
-- If so, set the 'AllGuarded' flag which can be used by the productivity check
checkIfGuarded :: Name -> Idris ()
checkIfGuarded n
   = do i <- get
        let ctxt = tt_ctxt i
        case lookupDefExact n ctxt of
             Just (CaseOp _ ty _ _ _ cases) ->
                  let gnames = fst (cases_compiletime cases) in
                      if allGuarded gnames i (snd (cases_compiletime cases))
                         then -- trace (show (n, gnames, ty, cases_compiletime cases)) $
                              addFnOpt n AllGuarded
                         else return ()
             _ -> return ()
  where
    guard n ist = isConName n (tt_ctxt ist) || guardFlag n ist
    guardFlag n ist = case lookupCtxtExact n (idris_flags ist) of
                           Nothing -> False
                           Just fs -> AllGuarded `elem` fs

    -- Top level thing always needs to be a constructor application if
    -- the delayed things are going to be definitely guarded by this definition
    allGuarded names i (STerm t)
          | (P _ fn _, args) <- unApply t,
            guard fn i
            = and (map (guardedTerm names i) args)
          | otherwise = False
    allGuarded names i (ProjCase _ alts) = and (map (guardedAlt names i) alts)
    allGuarded names i (Case _ _ alts) = and (map (guardedAlt names i) alts)
    allGuarded names i _ = True

    guardedTerm names i (P _ v _) = v `elem` names || guard v i
    guardedTerm names i (Bind n (Let t v) sc)
          = guardedTerm names i v && guardedTerm names i sc
    guardedTerm names i (Bind n b sc) = False
    guardedTerm names i ap@(App _ _ _)
          | (P _ fn _, args) <- unApply ap,
            guard fn i || fn `elem` names
                = and (map (guardedTerm names i) args)
    guardedTerm names i (App _ f a) = False
    guardedTerm names i tm = True

    guardedAlt names i (ConCase _ _ _ t) = allGuarded names i t
    guardedAlt names i (FnCase _ _ t) = allGuarded names i t
    guardedAlt names i (ConstCase _ t) = allGuarded names i t
    guardedAlt names i (SucCase _ t) = allGuarded names i t
    guardedAlt names i (DefaultCase t) = allGuarded names i t

-- | Check if, in a given group of type declarations mut_ns, the
-- constructor cn : ty is strictly positive, and update the context
-- accordingly
checkPositive :: [Name]       -- ^ the group of type declarations
              -> (Name, Type) -- ^ the constructor
              -> Idris Totality
checkPositive mut_ns (cn, ty')
    = do i <- getIState
         let ty = delazy' True (normalise (tt_ctxt i) [] ty')
         let p = cp i ty
         let tot = if p then Total (args ty) else Partial NotPositive
         let ctxt' = setTotal cn tot (tt_ctxt i)
         putIState (i { tt_ctxt = ctxt' })
         logCoverage 5 $ "Constructor " ++ show cn ++ " is " ++ show tot ++ " with " ++ show mut_ns
         addIBC (IBCTotal cn tot)
         return tot
  where
    args t = [0..length (getArgTys t)-1]

    cp i (Bind n (Pi _ _ aty _) sc)
         = posArg i aty && cp i sc
    cp i t | (P _ n' _ , args) <- unApply t,
             n' `elem` mut_ns = all noRec args
    cp i _ = True

    posArg ist (Bind _ (Pi _ _ nty _) sc) = noRec nty && posArg ist sc
    posArg ist t = posParams ist t

    noRec arg = all (\x -> x `notElem` mut_ns) (allTTNames arg)

    -- If the type appears recursively in a parameter argument, that's
    -- fine, otherwise if it appears in an argument it's not fine.
    posParams ist t | (P _ n _, args) <- unApply t
       = case lookupCtxtExact n (idris_datatypes ist) of
              Just ti -> checkParamsOK (param_pos ti) 0 args
              Nothing -> and (map (posParams ist) args)
    posParams ist t = noRec t

    checkParamsOK ppos i [] = True
    checkParamsOK ppos i (p : ps)
          | i `elem` ppos = checkParamsOK ppos (i + 1) ps
          | otherwise = noRec p && checkParamsOK ppos (i + 1) ps

-- | Calculate the totality of a function from its patterns.  Either
-- follow the size change graph (if inductive) or check for
-- productivity (if coinductive)
calcTotality :: FC -> Name -> [([Name], Term, Term)] -> Idris Totality
calcTotality fc n pats
    = do i <- getIState
         let opts = case lookupCtxt n (idris_flags i) of
                            [fs] -> fs
                            _ -> []
         case mapMaybe (checkLHS i) (map (\ (_, l, r) -> l) pats) of
            (failure : _) -> return failure
            _ -> checkSizeChange n
  where
    checkLHS i (P _ fn _)
        = case lookupTotalExact fn (tt_ctxt i) of
               Just (Partial _) -> return (Partial (Other [fn]))
               _ -> Nothing
    checkLHS i (App _ f a) = mplus (checkLHS i f) (checkLHS i a)
    checkLHS _ _ = Nothing

checkTotality :: [Name] -> FC -> Name -> Idris Totality
checkTotality path fc n
    | n `elem` path = return (Partial (Mutual (n : path)))
    | otherwise = do
        t <- getTotality n
        i <- getIState
        ctxt' <- do ctxt <- getContext
                    tclift $ simplifyCasedef n [] [] (getErasureInfo i) ctxt
        setContext ctxt'
        ctxt <- getContext
        i <- getIState
        let opts = case lookupCtxt n (idris_flags i) of
                            [fs] -> fs
                            _ -> []
        t' <- case t of
                Unchecked ->
                    case lookupDef n ctxt of
                        [CaseOp _ _ _ _ pats _] ->
                            do t' <- if AssertTotal `elem` opts
                                        then return $ Total []
                                        else calcTotality fc n pats
                               logCoverage 2 $ "Set to " ++ show t'
                               setTotality n t'
                               addIBC (IBCTotal n t')
                               return t'
                        [TyDecl (DCon _ _ _) ty] ->
                            case unApply (getRetTy ty) of
                              (P _ tyn _, _) -> do
                                 let ms = case lookupCtxt tyn (idris_datatypes i) of
                                       [TI _ _ _ _ xs@(_:_) _] -> xs
                                       ts -> [tyn]
                                 checkPositive ms (n, ty)
                              _-> return $ Total []
                        _ -> return $ Total []
                x -> return x
        case t' of
            Total _ -> return t'
            Productive -> return t'
            e -> do w <- cmdOptType WarnPartial
                    if TotalFn `elem` opts
                       then do totalityError t'; return t'
                       else do when (w && not (PartialFn `elem` opts)) $
                                   warnPartial n t'
                               return t'
  where
    totalityError t = do i <- getIState
                         let msg = show n ++ " is " ++ show t
                         putIState i { idris_totcheckfail = (fc, msg) : idris_totcheckfail i}
                         addIBC (IBCTotCheckErr fc msg)

    warnPartial n t
       = do i <- getIState
            case lookupDef n (tt_ctxt i) of
               [x] -> do
                  iWarn fc . pprintErr i . Msg $ "Warning - " ++ show n ++ " is " ++ show t
--                                ++ "\n" ++ show x
--                   let cg = lookupCtxtName Nothing n (idris_callgraph i)
--                   iputStrLn (show cg)


checkDeclTotality :: (FC, Name) -> Idris Totality
checkDeclTotality (fc, n)
    = do logCoverage 2 $ "Checking " ++ show n ++ " for totality"
         i <- getIState
         let opts = case lookupCtxtExact n (idris_flags i) of
                              Just fs -> fs
                              _ -> []
         when (CoveringFn `elem` opts) $ checkAllCovering fc [] n n
         t <- checkTotality [] fc n
         return t

-- If the name calls something which is partial, set it as partial
verifyTotality :: (FC, Name) -> Idris ()
verifyTotality (fc, n)
    = do logCoverage 2 $ "Checking " ++ show n ++ "'s descendents are total"
         ist <- getIState
         case lookupTotalExact n (tt_ctxt ist) of
              Just (Total _) -> do
                 let ns = getNames (tt_ctxt ist)

                 case getPartial ist [] ns of
                      Nothing -> return ()
                      Just bad -> do let t' = Partial (Other bad)
                                     logCoverage 2 $ "Set in verify to " ++ show t'
                                     setTotality n t'
                                     addIBC (IBCTotal n t')
              _ -> return ()
  where
    getNames ctxt = case lookupDefExact n ctxt of
                         Just (CaseOp  _ _ _ _ _ defs)
                           -> let (top, def) = cases_compiletime defs in
                                  map fst (findCalls' True def top)
                         _ -> []

    getPartial ist [] [] = Nothing
    getPartial ist bad [] = Just bad
    getPartial ist bad (n : ns)
        = case lookupTotalExact n (tt_ctxt ist) of
               Just (Partial _) -> getPartial ist (n : bad) ns
               _ -> getPartial ist bad ns

-- | Calculate the size change graph for this definition
--
-- SCG for a function f consists of a list of:
--    (g, [(a1, sizechange1), (a2, sizechange2), ..., (an, sizechangen)])
--
-- where g is a function called
-- a1 ... an are the arguments of f in positions 1..n of g
-- sizechange1 ... sizechange2 is how their size has changed wrt the input
-- to f
--    Nothing, if the argument is unrelated to the input
buildSCG :: (FC, Name) -> Idris ()
buildSCG (_, n) = do
   ist <- getIState
   case lookupCtxtExact n (idris_callgraph ist) of
       Just cg -> case lookupDefExact n (tt_ctxt ist) of
           Just (CaseOp _ _ _ pats _ cd) ->
             let (args, sc) = cases_compiletime cd in
               do logCoverage 2 $ "Building SCG for " ++ show n ++ " from\n"
                                ++ show pats ++ "\n" ++ show sc
                  let newscg = buildSCG' ist n (rights pats) args
                  logCoverage 5 $ "SCG is: " ++ show newscg
                  addToCG n ( cg { scg = newscg } )
           _ -> return () -- CG comes from a type declaration only
       _ -> logCoverage 5 $ "Could not build SCG for " ++ show n ++ "\n"

delazy = delazy' False -- not lazy codata
delazy' all t@(App _ f a)
     | (P _ (UN l) _, [_, _, arg]) <- unApply t,
       l == txt "Force" = delazy' all arg
     | (P _ (UN l) _, [P _ (UN lty) _, _, arg]) <- unApply t,
       l == txt "Delay" && (all || lty /= txt "Infinite") = delazy arg
     | (P _ (UN l) _, [P _ (UN lty) _, arg]) <- unApply t,
       l == txt "Delayed" && (all || lty /= txt "Infinite") = delazy' all arg
delazy' all (App s f a) = App s (delazy' all f) (delazy' all a)
delazy' all (Bind n b sc) = Bind n (fmap (delazy' all) b) (delazy' all sc)
delazy' all t = t

data Guardedness = Toplevel | Unguarded | Guarded | Delayed
  deriving Show

buildSCG' :: IState -> Name -> [(Term, Term)] -> [Name] -> [SCGEntry]
buildSCG' ist topfn pats args = nub $ concatMap scgPat pats where
  scgPat (lhs, rhs) = let lhs' = delazy lhs
                          rhs' = delazy rhs
                          (f, pargs) = unApply (dePat lhs') in
                            findCalls [] Toplevel (dePat rhs') (patvars lhs')
                                      (zip pargs [0..])

  -- Under a delay, calls are excluded from the graph - if it's a call to a
  -- non-total function we'll find that in the final totality check
  findCalls cases Delayed ap@(P _ n _) pvs args = []
  findCalls cases guarded ap@(App _ f a) pvs pargs
     -- under a call to "assert_total", don't do any checking, just believe
     -- that it is total.
     | (P _ (UN at) _, [_, _]) <- unApply ap,
       at == txt "assert_total" = []
     -- don't go under calls to functions which are asserted total
     | (P _ n _, _) <- unApply ap,
       Just opts <- lookupCtxtExact n (idris_flags ist),
       AssertTotal `elem` opts = []
     -- under a guarded call to "Delay Infinite", we are 'Delayed', so don't
     -- check under guarded constructors.
     | (P _ (UN del) _, [_,_,arg]) <- unApply ap,
       Guarded <- guarded,
       del == txt "Delay"
           = findCalls cases Delayed arg pvs pargs
     | (P _ n _, args) <- unApply ap,
       Delayed <- guarded,
       isConName n (tt_ctxt ist) || allGuarded n ist
           = -- Still under a 'Delay' and constructor guarded, so check
             -- just the arguments to the constructor, remaining Delayed
             concatMap (\x -> findCalls cases guarded x pvs pargs) args
     | (P _ ifthenelse _, [_, _, t, e]) <- unApply ap,
       ifthenelse == sNS (sUN "ifThenElse") ["Bool", "Prelude"]
       -- Continue look inside if...then...else blocks
       -- TODO: Consider whether we should do this for user defined ifThenElse
       -- rather than just the one in the Prelude as a special case
       = findCalls cases guarded t pvs pargs ++
         findCalls cases guarded e pvs pargs
     | (P _ n _, args) <- unApply ap,
       caseName n && n /= topfn,
       notPartial (lookupTotalExact n (tt_ctxt ist))
       -- case block - look inside the block, as long as it was covering
       -- (i.e. not currently set at Partial) to get a more accurate size
       -- change result from the top level patterns (also to help pass
       -- information through from guarded corecursion accurately)
       = concatMap (\x -> findCalls cases Unguarded x pvs pargs) args ++
             if n `notElem` cases
                then findCallsCase (n : cases) guarded n args pvs pargs
                else []
     | (P _ n _, args) <- unApply ap,
       Delayed <- guarded
       -- Under a delayed recursive call just check the arguments
           = concatMap (\x -> findCalls cases Unguarded x pvs pargs) args
     | (P _ n _, args) <- unApply ap,
       not (n `elem` pvs)
        -- Ordinary call, not under a delay.
        -- If n is a constructor, set 'args' as Guarded
        = let nguarded = case guarded of
                              Unguarded -> Unguarded
                              x -> if isConName n (tt_ctxt ist)
                                       || allGuarded n ist
                                      then Guarded
                                      else Unguarded in
              mkChange n args pargs ++
                 concatMap (\x -> findCalls cases nguarded x pvs pargs) args
    where notPartial (Just (Partial NotCovering)) = False
          notPartial _ = True
  findCalls cases guarded (App _ f a) pvs pargs
        = findCalls cases Unguarded f pvs pargs ++ findCalls cases Unguarded a pvs pargs
  findCalls cases guarded (Bind n (Let t v) e) pvs pargs
        = findCalls cases Unguarded t pvs pargs ++
          findCalls cases Unguarded v pvs pargs ++
          -- Substitute in the scope since this might reveal some useful
          -- structure
          findCalls cases guarded (substV v e) pvs pargs
  findCalls cases guarded (Bind n t e) pvs pargs
        = findCalls cases Unguarded (binderTy t) pvs pargs ++
          findCalls cases guarded e (n : pvs) pargs
  findCalls cases guarded (P _ f _ ) pvs pargs
      | not (f `elem` pvs) = [(f, [])]
  findCalls _ _ _ _ _ = []

  -- Assumption is that names are preserved in the case block (shadowing
  -- dealt with by the elaborator) so we can just assume the top level names
  -- are okay for building the size change
  findCallsCase cases guarded n args pvs pargs
      = case lookupDefExact n (tt_ctxt ist) of
           Just (CaseOp _ _ _ pats _ cd) ->
                concatMap (fccPat cases pvs pargs args guarded) (rights pats)
           Nothing -> []

  fccPat cases pvs pargs args g (lhs, rhs)
      = let lhs' = delazy lhs
            rhs' = delazy rhs
            (f, pargs_case) = unApply (dePat lhs')
            -- pargs is a pair of a term, and the argument position that
            -- term appears in. If any of the arguments to the case block
            -- are also on the lhs, we also want those patterns to appear
            -- in the parg list so that we'll spot patterns which are
            -- smaller than then
            newpargs = newPArg args pargs
            -- Now need to update the rhs of the case with the names in the
            -- outer definition: In rhs', wherever we see what's in pargs_case,
            -- replace it with the corresponding thing in pargs
            csubs = zip pargs_case args
            newrhs = doCaseSubs csubs (dePat rhs')
            pargs' = pargs ++ addPArg newpargs pargs_case in
               findCalls cases g newrhs pvs pargs'
    where
      doCaseSubs [] tm = tm
      doCaseSubs ((x, x') : cs) tm
           = doCaseSubs (subIn x x' cs) (substTerm x x' tm)

      subIn x x' [] = []
      subIn x x' ((l, r) : cs)
          = (substTerm x x' l, substTerm x x' r) : subIn x x' cs

  addPArg (Just (t, i) : ts) (t' : ts') = (t', i) : addPArg ts ts'
  addPArg (Nothing : ts) (t' : ts') = addPArg ts ts'
  addPArg _ _ = []

  newPArg :: [Term] -> [(Term, Int)] -> [Maybe (Term, Int)]
  newPArg (t : ts) pargs = case lookup t pargs of
                                Just i -> Just (t, i) : newPArg ts pargs
                                Nothing -> Nothing : newPArg ts pargs
  newPArg [] pargs = []

  expandToArity n args
     = case lookupTy n (tt_ctxt ist) of
            [ty] -> expand 0 (normalise (tt_ctxt ist) [] ty) args
            _ -> args
     where expand i (Bind n (Pi _ _ _ _) sc) (x : xs) = x : expand (i + 1) sc xs
           expand i (Bind n (Pi _ _ _ _) sc) [] = Just (i, Same) : expand (i + 1) sc []
           expand i _ xs = xs

  mkChange n args pargs = [(n, expandToArity n (sizes args))]
    where
      sizes [] = []
      sizes (a : as) = checkSize a pargs : sizes as

      -- find which argument in pargs <a> is smaller than, if any
      checkSize a ((p, i) : ps)
          | a == p = Just (i, Same)
          | (P _ (UN as) _, [_,_,arg,_]) <- unApply a,
            as == txt "assert_smaller" && arg == p
                  = Just (i, Smaller)
          | smaller Nothing a (p, Nothing) = Just (i, Smaller)
          | otherwise = checkSize a ps
      checkSize a [] = Nothing

      -- Can't be smaller than an erased thing (need to be careful here
      -- because Erased equals everything)
      smaller _ _ (Erased, _) = False -- never smaller than an erased thing
      -- If a == t, and we're under a cosntructor, we've found something
      -- smaller
      smaller (Just tyn) a (t, Just tyt) | a == t = True
      smaller ty a (ap@(App _ f s), _)
          -- Nothing can be smaller than a delayed infinite thing...
          | (P (DCon _ _ _) (UN d) _, [P _ (UN reason) _, _, _]) <- unApply ap,
            d == txt "Delay" && reason == txt "Infinite"
               = False
          | (P (DCon _ _ _) n _, args) <- unApply ap
               = let tyn = getType n in
                     any (smaller (ty `mplus` Just tyn) a)
                         (zip args (map toJust (getArgTys tyn)))
      -- check higher order recursive arguments
      smaller ty (App _ f s) a = smaller ty f a
      smaller _ _ _ = False

      toJust (n, t) = Just t

      getType n = case lookupTyExact n (tt_ctxt ist) of
                       Just ty -> delazy (normalise (tt_ctxt ist) [] ty) -- must exist

  dePat (Bind x (PVar _ ty) sc) = dePat (instantiate (P Bound x ty) sc)
  dePat t = t

  patvars (Bind x (PVar _ _) sc) = x : patvars sc
  patvars _ = []

  allGuarded n ist = case lookupCtxtExact n (idris_flags ist) of
                          Nothing -> False
                          Just fs -> AllGuarded `elem` fs

checkSizeChange :: Name -> Idris Totality
checkSizeChange n = do
   ist <- getIState
   case lookupCtxt n (idris_callgraph ist) of
       [cg] -> do let ms = mkMultiPaths ist [] (scg cg)
                  logCoverage 5 ("Multipath for " ++ show n ++ ":\n" ++
                            "from " ++ show (scg cg) ++ "\n" ++
                            show (length ms) ++ "\n" ++
                            showSep "\n" (map show ms))
                  logCoverage 6 (show cg)
                  -- every multipath must have an infinitely descending
                  -- thread, then the function terminates
                  -- also need to checks functions called are all total
                  -- (Unchecked is okay as we'll spot problems here)
                  let tot = map (checkMP ist n (getArity ist n)) ms
                  logCoverage 4 $ "Generated " ++ show (length tot) ++ " paths"
                  logCoverage 5 $ "Paths for " ++ show n ++ " yield " ++
                       (showSep "\n" (map show (zip ms tot)))
                  return (noPartial tot)
       [] -> do logCoverage 5 $ "No paths for " ++ show n
                return Unchecked
  where getArity ist n
          = case lookupTy n (tt_ctxt ist) of
                 [ty] -> arity (normalise (tt_ctxt ist) [] ty)
                 _ -> error "Can't happen: checkSizeChange.getArity"

type MultiPath = [SCGEntry]

mkMultiPaths :: IState -> MultiPath -> [SCGEntry] -> [MultiPath]
mkMultiPaths ist path [] = [reverse path]
mkMultiPaths ist path cg = concatMap extend cg
  where extend (nextf, args)
           | (nextf, args) `inPath` path = [ reverse ((nextf, args) : path) ]
           | [Unchecked] <- lookupTotal nextf (tt_ctxt ist)
               = case lookupCtxt nextf (idris_callgraph ist) of
                    [ncg] -> mkMultiPaths ist ((nextf, args) : path) (scg ncg)
                    _ -> [ reverse ((nextf, args) : path) ]
           | otherwise = [ reverse ((nextf, args) : path) ]

        inPath :: SCGEntry -> [SCGEntry] -> Bool
        inPath f [] = False
        inPath f (g : gs) = smallerEq f g || f == g || inPath f gs

        smallerEq :: SCGEntry -> SCGEntry -> Bool
        smallerEq (f, args) (g, args')
            = f == g && not (null (filter smallers args))
                     && filter smallers args == filter smallers args'
        smallers (Just (_, Smaller)) = True
        smallers _ = False

-- If any route along the multipath leads to infinite descent, we're fine.
-- Try a route beginning with every argument.
--   If we reach a point we've been to before, but with a smaller value,
--   that means there is an infinitely descending path from that argument.

checkMP :: IState -> Name -> Int -> MultiPath -> Totality
checkMP ist topfn i mp = if i > 0
                     then let paths = (map (tryPath 0 [] mp) [0..i-1]) in
--                               trace ("Paths " ++ show paths) $
                               collapse paths
                     else tryPath 0 [] mp 0
  where
    tryPath' d path mp arg
           = let res = tryPath d path mp arg in
                 trace (show mp ++ "\n" ++ show arg ++ " " ++ show res) res

    mkBig (e, d) = (e, 10000)

    tryPath :: Int -> [((SCGEntry, Int), Int)] -> MultiPath -> Int -> Totality
    tryPath desc path [] _ = Total []
--     tryPath desc path ((UN "believe_me", _) : _) arg
--             = Partial BelieveMe
    -- if we get to a constructor, it's fine as long as it's strictly positive
    tryPath desc path ((f, _) : es) arg
        | [TyDecl (DCon _ _ _) _] <- lookupDef f (tt_ctxt ist)
            = case lookupTotalExact f (tt_ctxt ist) of
                   Just (Total _) -> Unchecked -- okay so far
                   Just (Partial _) -> Partial (Other [f])
                   x -> Unchecked -- An error elsewhere, set as Unchecked to make
                                  -- some progress
        | [TyDecl (TCon _ _) _] <- lookupDef f (tt_ctxt ist)
            = Total []
    tryPath desc path (e@(f, args) : es) arg
        | [Total a] <- lookupTotal f (tt_ctxt ist) = Total a
        | e `elem` es && allNothing args = Partial (Mutual [f])
    tryPath desc path (e@(f, nextargs) : es) arg
        | [Total a] <- lookupTotal f (tt_ctxt ist) = Total a
        | [Partial _] <- lookupTotal f (tt_ctxt ist) = Partial (Other [f])
        | Just d <- lookup (e, arg) path
            = if desc - d > 0 -- Now lower than when we were last here
                   then -- trace ("Descent " ++ show (desc - d) ++ " "
                        --      ++ show (path, e)) $
                        Total []
                   else Partial (Mutual (map (fst . fst . fst) path ++ [f]))
        | e `elem` map (fst . fst) path
           && not (f `elem` map fst es)
              = Partial (Mutual (map (fst . fst . fst) path ++ [f]))
        | [Unchecked] <- lookupTotal f (tt_ctxt ist) =
            let argspos = zip nextargs [0..]
                pathres =
                  do (a, pos) <- argspos
                     case a of
                        Nothing -> -- gone up, but if the
                                   -- rest definitely terminates without any
                                   -- cycles (including the path so far, which
                                   -- we take as inaccessible) the path is fine
                            return $ tryPath 0 (map mkBig (((e, arg), desc) : path)) es pos
                        Just (nextarg, sc) ->
                          if nextarg == arg then
                            case sc of
                              Same -> return $ tryPath desc (((e, arg), desc) : path)
                                                       es pos
                              Smaller -> return $ tryPath (desc+1)
                                                          (((e, arg), desc) : path)
                                                          es
                                                          pos
                              _ -> trace ("Shouldn't happen " ++ show e) $
                                      return (Partial Itself)
                            else return Unchecked in
--                   trace (show (desc, argspos, path, es, pathres)) $
                   collapse pathres

        | otherwise = Unchecked

allNothing :: [Maybe a] -> Bool
allNothing xs = null (collapseNothing (zip xs [0..]))

collapseNothing :: [(Maybe a, b)] -> [(Maybe a, b)]
collapseNothing ((Nothing, t) : xs)
   = (Nothing, t) : filter (\ (x, _) -> case x of
                                             Nothing -> False
                                             _ -> True) xs
collapseNothing (x : xs) = x : collapseNothing xs
collapseNothing [] = []

noPartial :: [Totality] -> Totality
noPartial (Partial p : xs) = Partial p
noPartial (_ : xs)         = noPartial xs
noPartial []               = Total []

collapse :: [Totality] -> Totality
collapse xs = collapse' Unchecked xs
collapse' def (Total r : xs)   = Total r
collapse' def (Unchecked : xs) = collapse' def xs
collapse' def (d : xs)         = collapse' d xs
-- collapse' Unchecked []         = Total []
collapse' def []               = def

-- totalityCheckBlock :: Idris ()
-- totalityCheckBlock = do
--          ist <- getIState
--          -- Do totality checking after entire mutual block
--          mapM_ (\n -> do logElab 5 $ "Simplifying " ++ show n
--                          ctxt' <- do ctxt <- getContext
--                                      tclift $ simplifyCasedef n (getErasureInfo ist) ctxt
--                          setContext ctxt')
--                  (map snd (idris_totcheck ist))
--          mapM_ buildSCG (idris_totcheck ist)
--          mapM_ checkDeclTotality (idris_totcheck ist)
--          clear_totcheck


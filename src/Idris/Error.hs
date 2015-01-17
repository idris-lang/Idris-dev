{-# LANGUAGE CPP, DeriveDataTypeable #-}

module Idris.Error where

import Prelude hiding (catch)
import Idris.AbsSyntax
import Idris.Delaborate
import Idris.Output

import Idris.Core.Evaluate (ctxtAlist)
import Idris.Core.TT
import Idris.Core.Typecheck
import Idris.Core.Constraints
import Idris.Output

import System.Console.Haskeline
import System.Console.Haskeline.MonadException
import Control.Monad (when)
import Control.Monad.State.Strict
#if MIN_VERSION_mtl(2,2,1)
import Control.Monad.Except (throwError, catchError)
#else
import Control.Monad.Error  (throwError, catchError)
#endif
import System.IO.Error(isUserError, ioeGetErrorString)
import Data.Char
import Data.List (intercalate, isPrefixOf)
import qualified Data.Text as T
import Data.Typeable
import qualified Data.Traversable as Traversable
import qualified Data.Foldable as Foldable

iucheck :: Idris ()
iucheck = do tit <- typeInType
             ist <- getIState
             let cs = idris_constraints ist
             logLvl 7 $ "ALL CONSTRAINTS: " ++ show cs
             when (not tit) $
                   (tclift $ ucheck (idris_constraints ist)) `idrisCatch`
                              (\e -> do setErrSpan (getErrSpan e)
                                        iputStrLn (pshow ist e))

showErr :: Err -> Idris String
showErr e = getIState >>= return . flip pshow e


report :: IOError -> String
report e
    | isUserError e = ioeGetErrorString e
    | otherwise     = show e

idrisCatch :: Idris a -> (Err -> Idris a) -> Idris a
idrisCatch = catchError


setAndReport :: Err -> Idris ()
setAndReport e = do ist <- getIState
                    case (unwrap e) of
                      At fc e -> do setErrSpan fc
                                    iWarn fc $ pprintErr ist e
                      _ -> do setErrSpan (getErrSpan e)
                              iWarn emptyFC $ pprintErr ist e
  where unwrap (ProofSearchFail e) = e -- remove bookkeeping constructor
        unwrap e = e

ifail :: String -> Idris a
ifail = throwError . Msg

ierror :: Err -> Idris a
ierror = throwError

tclift :: TC a -> Idris a
tclift (OK v) = return v
tclift (Error err@(At fc e)) = do setErrSpan fc; throwError err
tclift (Error err) = throwError err

tctry :: TC a -> TC a -> Idris a
tctry tc1 tc2
    = case tc1 of
           OK v -> return v
           Error err -> tclift tc2

getErrSpan :: Err -> FC
getErrSpan (At fc _) = fc
getErrSpan _ = emptyFC

--------------------------------------------------------------------
-- Specific warnings not included in elaborator
--------------------------------------------------------------------
-- | Issue a warning on "with"-terms whose namespace is empty or nonexistent
warnDisamb :: IState -> PTerm -> Idris ()
warnDisamb ist (PQuote _) = return ()
warnDisamb ist (PRef _ _) = return ()
warnDisamb ist (PInferRef _ _) = return ()
warnDisamb ist (PPatvar _ _) = return ()
warnDisamb ist (PLam _ _ t b) = warnDisamb ist t >> warnDisamb ist b
warnDisamb ist (PPi _ _ t b) = warnDisamb ist t >> warnDisamb ist b
warnDisamb ist (PLet _ _ x t b) = warnDisamb ist x >> warnDisamb ist t >> warnDisamb ist b
warnDisamb ist (PTyped x t) = warnDisamb ist x >> warnDisamb ist t
warnDisamb ist (PApp _ t args) = warnDisamb ist t >>
                                 mapM_ (warnDisamb ist . getTm) args
warnDisamb ist (PAppBind _ f args) = warnDisamb ist f >>
                                     mapM_ (warnDisamb ist . getTm) args
warnDisamb ist (PMatchApp _ _) = return ()
warnDisamb ist (PCase _ tm cases) = warnDisamb ist tm >>
                                    mapM_ (\(x,y)-> warnDisamb ist x >> warnDisamb ist y) cases
warnDisamb ist (PTrue _ _) = return ()
warnDisamb ist (PRefl _ tm) = warnDisamb ist tm
warnDisamb ist (PResolveTC _) = return ()
warnDisamb ist (PEq _ a b x y) = warnDisamb ist a >> warnDisamb ist b >>
                                 warnDisamb ist x >> warnDisamb ist y
warnDisamb ist (PRewrite _ x y z) = warnDisamb ist x >> warnDisamb ist y >>
                                    Foldable.mapM_ (warnDisamb ist) z
warnDisamb ist (PPair _ _ x y) = warnDisamb ist x >> warnDisamb ist y
warnDisamb ist (PDPair _ _ x y z) = warnDisamb ist x >> warnDisamb ist y >> warnDisamb ist z
warnDisamb ist (PAlternative _ tms) = mapM_ (warnDisamb ist) tms
warnDisamb ist (PHidden tm) = warnDisamb ist tm
warnDisamb ist PType = return ()
warnDisamb ist (PUniverse _) = return ()
warnDisamb ist (PGoal _ x _ y) = warnDisamb ist x >> warnDisamb ist y
warnDisamb ist (PConstant _) = return ()
warnDisamb ist Placeholder = return ()
warnDisamb ist (PDoBlock steps) = mapM_ wStep steps
  where wStep (DoExp _ x) = warnDisamb ist x
        wStep (DoBind _ _ x) = warnDisamb ist x
        wStep (DoBindP _ x y cs) = warnDisamb ist x >> warnDisamb ist y >>
                                   mapM_ (\(x,y)-> warnDisamb ist x >> warnDisamb ist y) cs
        wStep (DoLet _ _ x y) = warnDisamb ist x >> warnDisamb ist y
        wStep (DoLetP _ x y) = warnDisamb ist x >> warnDisamb ist y
warnDisamb ist (PIdiom _ x) = warnDisamb ist x
warnDisamb ist (PReturn _) = return ()
warnDisamb ist (PMetavar _) = return ()
warnDisamb ist (PProof tacs) = mapM_ (Foldable.mapM_ (warnDisamb ist)) tacs
warnDisamb ist (PTactics tacs) = mapM_ (Foldable.mapM_ (warnDisamb ist)) tacs
warnDisamb ist (PElabError _) = return ()
warnDisamb ist PImpossible = return ()
warnDisamb ist (PCoerced tm) = warnDisamb ist tm
warnDisamb ist (PDisamb ds tm) = warnDisamb ist tm >>
                                 mapM_ warnEmpty ds
  where warnEmpty d =
          when (null (filter (isIn d . fst) (ctxtAlist (tt_ctxt ist)))) $
            ierror . Msg $
              "Nothing found in namespace \"" ++
              intercalate "." (map T.unpack d) ++
              "\"."
        isIn d (NS _ ns) = isPrefixOf d ns
        isIn d _ = False

warnDisamb ist (PUnifyLog tm) = warnDisamb ist tm
warnDisamb ist (PNoImplicits tm) = warnDisamb ist tm
warnDisamb ist (PQuasiquote tm goal) = warnDisamb ist tm >>
                                       Foldable.mapM_ (warnDisamb ist) goal
warnDisamb ist (PUnquote tm) = warnDisamb ist tm
warnDisamb ist (PAs _ _ tm) = warnDisamb ist tm

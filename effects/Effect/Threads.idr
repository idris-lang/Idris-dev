module Main

import Eff
import State

mutual
  Thunk : (Type -> Type) -> Type
  Thunk m = (t : Type) -> Threads m ->  
            (Threads m -> () -> m t) -> m t

  data Threads : (Type -> Type) -> Type where
       MkThreads : List (Thunk m) -> List (Thunk m) -> Threads m

initThreads : Monad m => Threads m
initThreads = MkThreads [] []

data Threading : (Type -> Type) -> Effect where
     Yield : Threading m (Threads m) (Threads m) ()
     Fork  : Threading m (Threads m) (Threads m) Bool

instance Monad m => Effective (Threading m) m where
     runEffect (MkThreads ds []) Yield k 
         = k (MkThreads [] (reverse ds)) ()
     runEffect (MkThreads ds (q :: qs)) Yield k 
         = q _ (MkThreads (newThread :: ds) qs) k
        where newThread _ st k' = do k st ()
                                     k' st ()

     runEffect (MkThreads ds qs) Fork k 
         = k (MkThreads ds (newThread :: qs)) False
        where newThread t st k' = do t <- k st True
                                     k' st () 

THREADING : (Type -> Type) -> EFF
THREADING m = MkEff (Threads m) (Threading m)

fork : Monad m => (EffT m [THREADING m] ()) -> EffT m [THREADING m] ()
fork prog = do branch <- effect Fork 
               if branch then prog else return ()

yield : Monad m => EffT m [THREADING m] ()
yield = effect Yield

printA : Int -> Eff [THREADING m, STATE String] ()
printA 0 = return ()
printA n = do s <- lift get
              lift (put (s ++ "A"))
              lift yield
              printA (n - 1)

printB : Int -> Eff [THREADING m, STATE String] ()
printB 0 = return ()
printB n = do s <- lift get
              lift (put (s ++ "B"))
              lift yield
              printB (n - 1)

printAB : Int -> Eff [THREADING m, STATE String] String
printAB n = do branch <- effect Fork
               if branch then printA n
                         else printB n
               lift get
               

main : IO ()
main = print $ runPure [initThreads, ""] (printAB 10)



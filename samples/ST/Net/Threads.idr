module Threads

import Control.ST
import System.Concurrency.Channels
import System

public export
interface Conc (m : Type -> Type) where
  -- 'Fork' sends some resources to the spawned thread, and keeps the rest
  -- for the parent
  -- TODO: Note that there is nothing here yet about how the threads
  -- communicate with each other...
  fork : (thread : STrans m () thread_res (const [])) ->
         {auto tprf : SubRes thread_res all} ->
         STrans m () all (const (kept tprf)) 

export
implementation Conc IO where
  fork thread
      = do threadEnv <- dropSub
           lift $ spawn (do runWith threadEnv thread
                            pure ()) 
           pure ()

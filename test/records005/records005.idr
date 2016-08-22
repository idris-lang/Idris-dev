record Score where
       constructor MkScore
       correct : Nat
       attempted : Nat

record GameState where
       constructor MkGameState
       score : Score
       difficulty : Nat

Show GameState where
    show st = show (correct (score st)) ++ "/" 
              ++ show (attempted (score st)) ++ "\n"
              ++ "Difficulty: " ++ show (difficulty st)

initState : GameState
initState = MkGameState (MkScore 0 0) 12

-- Test record update syntax

correct : GameState -> GameState
correct = record { score->correct $= (+1),
                   score->attempted $= (+1) }

wrong : GameState -> GameState
wrong = record { score->attempted $= (+1) }

restart : GameState -> GameState
restart = record { score->attempted = 0,
                   score->correct = 0 }


main : IO ()
main = do let st = initState
          let st' = correct st
          let st'' = wrong st'
          printLn st''
          printLn (restart st'')


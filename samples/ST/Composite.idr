import Control.ST

splitComp : (comp : Var) -> 
            ST m () [comp ::: Composite [State Int, State String]]
splitComp comp = do [int, str] <- split comp
                    update int (+ 1)
                    update str (++ "\n")
                    combine comp [int, str]

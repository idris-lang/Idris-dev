module Test_show

%default total

data Te = C1 | C2 | C3

Show Te where
    show C1 = "C1"

-- Eq Te where
--     (==) C1 C3 = False

-- foo : Te -> String
-- foo = show


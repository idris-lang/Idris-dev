module main

%default total

data Bad = MkBad (Bad -> Int) Int
         | MkBad' Int

bar : Bad
bar = MkBad (\x => 3) 3

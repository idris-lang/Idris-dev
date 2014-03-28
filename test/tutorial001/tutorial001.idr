foo : Int -> Int
foo x = case isLT of
            Yes => x*2
            No => x*4
   where
      data MyLT = Yes | No
      isLT : MyLT
      isLT = if x < 20 then Yes else No


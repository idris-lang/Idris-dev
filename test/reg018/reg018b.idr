module A 

%default total

codata B = O B | I B

showB : B -> String
showB (I x) = "I" ++ showB x
showB (O x) = "O" ++ showB x

instance Show B where show = showB 

os : B
os = O os

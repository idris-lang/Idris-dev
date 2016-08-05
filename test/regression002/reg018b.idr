module A

%default total

codata B = Z B | I B

showB : B -> String
showB (I x) = "I" ++ showB x
showB (Z x) = "Z" ++ showB x

Show B where show = showB

os : B
os = Z os

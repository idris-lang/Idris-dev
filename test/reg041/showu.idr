module Main

%default total

data U : Type where
  BOOL : U
  NAT : U
  PAIR : U -> U -> U

interpU : U -> Type
interpU BOOL = Bool
interpU NAT = Nat
interpU (PAIR x y) = (interpU x, interpU y)

showU : (u : U) -> interpU u -> String
showU BOOL True            = "Yes"
showU BOOL False           = "No"
showU NAT Z                = "Z"
showU NAT (S x)            = "S of " ++ showU NAT x
showU (PAIR tx ty) (x , y) = "(" ++ showU tx x ++ "," ++ showU ty y ++ ")"

main : IO ()
main = putStrLn $ showU NAT 0

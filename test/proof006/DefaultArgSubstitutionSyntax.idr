module DefaultArgSubstitutionSyntax

DecProofType : {a:Type} -> Dec a -> Type
DecProofType {a} (Yes _)  = a
DecProofType {a} (No _)   = a -> _|_

decProof : {a:Type} -> (dec : Dec a) -> DecProofType dec
decProof (Yes x)  = x
decProof (No x)   = x

DecType : {a:Type} -> Dec a -> Type
DecType {a} _ = a


syntax "{{" [prfname] ":" "accept" [dec] "}}" "->" [ret] 
  = { default (decProof dec) prfname : DecType dec } -> ret


argsAreSame : (n:Nat) -> (m:Nat)
              -> {{ same : accept (decEq n m) }} -> ()
argsAreSame _ _ = ()

data SameNats : Type where
  same : (n:Nat) -> (m:Nat) -> {{ same : accept (decEq m n) }} -> SameNats

zArgsAreSame : ()
zArgsAreSame = argsAreSame Z Z

sameNatZs : SameNats
sameNatZs = same Z Z

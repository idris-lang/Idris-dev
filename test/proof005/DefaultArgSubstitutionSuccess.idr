module DefaultArgSubstitutionSuccess

DecProofType : {a:Type} -> Dec a -> Type
DecProofType {a} (Yes _)  = a
DecProofType {a} (No _)   = a -> Void

decProof : {a:Type} -> (dec : Dec a) -> DecProofType dec
decProof (Yes x)  = x
decProof (No x)   = x

DecType : {a:Type} -> Dec a -> Type
DecType {a} _ = a


argsAreSame : (n:Nat) -> (m:Nat)
              -> { default (decProof (decEq m n)) same : (m=n) } -> ()
argsAreSame _ _ = ()


argsAreDiff : (n:Nat) -> (m:Nat)
              -> { default (decProof (decEq m n)) same : (m=n) -> Void } -> ()
argsAreDiff _ _ = ()


data SameNats : Type where
  Same : (n:Nat) -> (m:Nat) ->
         { default (decProof (decEq m n)) same : (m=n) } -> SameNats

data DiffNats : Type where
  Diff : (n:Nat) -> (m:Nat) ->
         { default (decProof (decEq m n)) same : (m=n) -> Void } -> DiffNats


zArgsAreSame : ()
zArgsAreSame = argsAreSame Z Z

zszArgsAreDiff : ()
zszArgsAreDiff = argsAreDiff Z (S Z)

sameNatZs : SameNats
sameNatZs = Same Z Z

diffNatsZSZ : DiffNats
diffNatsZSZ = Diff Z (S Z)

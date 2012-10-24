module Language.Reflection

TTName : Set
TTName = String

data TT = Var TTName
        | Lam TTName TT TT
        | Pi  TTName TT TT
        | Let TTName TT TT TT
        | App TTName TT TT


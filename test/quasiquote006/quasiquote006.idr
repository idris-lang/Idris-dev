
a : TTName
a = `{Nat}

aOK : a = NS (UN "Nat") ["Nat", "Prelude"]
aOK = Refl

b : TTName
b = `{Nil}

c : TTName
c = `{alsdkjflkj}

d : TTName
d = `{(::)}

d : TTName
d = `{List.(::)}

dOK : d = NS (UN "::") ["List", "Prelude"]
dOK = Refl

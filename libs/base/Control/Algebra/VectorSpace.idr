module Control.Algebra.VectorSpace


infixl 5 <#>
infixr 2 <||>


||| A module over a ring is an additive abelian group of 'vectors' endowed with a
||| scale operation multiplying vectors by ring elements, and distributivity laws
||| relating the scale operation to both ring addition and module addition.
||| Must satisfy the following laws:
|||
||| + Compatibility of scalar multiplication with ring multiplication:
|||     forall a b v,  a <#> (b <#> v) = (a <.> b) <#> v
||| + Ring unity is the identity element of scalar multiplication:
|||     forall v,      unity <#> v = v
||| + Distributivity of `<#>` and `<+>`:
|||     forall a v w,  a <#> (v <+> w) == (a <#> v) <+> (a <#> w)
|||     forall a b v,  (a <+> b) <#> v == (a <#> v) <+> (b <#> v)
class (RingWithUnity a, AbelianGroup b) => Module a b where
  (<#>) : a -> b -> b

class (VerifiedRingWithUnity a, VerifiedAbelianGroup b, Module a b) => VerifiedModule a b where
  total moduleScalarMultiplyComposition : (x,y : a) -> (v : b) -> x <#> (y <#> v) = (x <.> y) <#> v
  total moduleScalarUnityIsUnity : (v : b) -> unity {a} <#> v = v
  total moduleScalarMultDistributiveWRTVectorAddition : (s : a) -> (v, w : b) -> s <#> (v <+> w) = (s <#> v) <+> (s <#> w)
  total moduleScalarMultDistributiveWRTModuleAddition : (s, t : a) -> (v : b) -> (s <+> t) <#> v = (s <#> v) <+> (t <#> v)

||| A vector space is a module over a ring that is also a field
class (Field a, Module a b) => VectorSpace a b where {}

class Module a b => InnerProductSpace a b where
  (<||>) : b -> b -> a

class (VerifiedField a, VerifiedModule a b) => VerifiedVectorSpace a b where {}

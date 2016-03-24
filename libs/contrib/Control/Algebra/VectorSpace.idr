module Control.Algebra.VectorSpace

import Control.Algebra

%access public export

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
interface (RingWithUnity a, AbelianGroup b) => Module a b where
  (<#>) : a -> b -> b

||| A vector space is a module over a ring that is also a field
interface (Field a, Module a b) => VectorSpace a b where {}

||| An inner product space is a module – or vector space – over a ring, with a binary function
||| associating a ring value to each pair of vectors.
interface Module a b => InnerProductSpace a b where
  (<||>) : b -> b -> a

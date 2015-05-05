
module GCD

import Divisibility

||| Proofs of greatests common denominator.
||| @ n one of the input numbers.
||| @ m the other input number.
||| @ k the GCD of the other two.
data GCD : (n,m,k:Nat) -> Type where
  GCDZero : GCD n Z n
  GCDRec  : GCD m n k -> GCD (n+m) m k


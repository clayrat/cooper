module Divisibility

%default total

---------------------------------------------------------------------
-- Properties of Addition
---------------------------------------------------------------------
||| Subtraction is a left inverse of addition.   
plusMinusLeftInverse : (left,right:Nat) -> (left + right) - left = right
plusMinusLeftInverse Z right = rewrite minusZeroRight right in Refl
plusMinusLeftInverse (S left) right = plusMinusLeftInverse left right

||| Subtraction is a right inverse of addition.
plusMinusRightInverse : (left `LTE` right) -> left + (right - left) = right
plusMinusRightInverse {right} LTEZero = rewrite minusZeroRight right in Refl
plusMinusRightInverse (LTESucc gte) = cong $ plusMinusRightInverse gte

||| The sum of two naturals is always greater than the components.
plusNonDecreasing : (left:Nat) -> (right:Nat) -> Not ((right + left) `LT` right)
plusNonDecreasing left Z = succNotLTEzero
plusNonDecreasing left (S right) = (plusNonDecreasing left right) . fromLteSucc


notLTthenGTE : Not (a `LT` b) -> a `GTE` b
notLTthenGTE {a} {b=Z} contra = LTEZero
notLTthenGTE {a=Z} {b=S k} contra = void $ contra $ LTESucc LTEZero
notLTthenGTE {a=S n} {b=S k} contra = LTESucc $ notLTthenGTE $ contra . LTESucc

||| Less than or equal to is an antisymmetric relation.
lteAntisym : a `LTE` b -> b `LTE` a -> a = b
lteAntisym LTEZero LTEZero = Refl
lteAntisym (LTESucc left) (LTESucc right) = cong $ lteAntisym left right
  
||| Less than or equal to is a transitive relation.  
lteTrans : a `LTE` b -> b `LTE` c -> a `LTE` c
lteTrans LTEZero _ = LTEZero
lteTrans (LTESucc left) (LTESucc right) = LTESucc $ lteTrans left right

||| If one number is less than another than there is an additive difference.
lteSum : a `LTE` b -> (x ** b = a + x)
lteSum {b} LTEZero = (b ** Refl)
lteSum (LTESucc {left} lte) = case lteSum lte of (x ** eq) => (x ** cong eq)

---------------------------------------------------------------------
-- Definition of Divisibility
---------------------------------------------------------------------
||| Proofs of divisibility in the natural numbers.
||| @ a the smaller number
||| @ b the larger number
data Div : (a,b:Nat) -> Type where
  DivZero : a `Div` 0
  DivAdd : a `Div` b -> a `Div` (a + b)

||| Every divisor of a number is also a factor of that number.
factors : a `Div` b -> (x ** b = x * a)
factors DivZero = (Z ** Refl)
factors (DivAdd prf) = case factors prf of
  (x ** eq) => (S x ** cong eq)

||| Every factor of a number divides that number.
divides : b = x * a -> a `Div` b
divides {x=Z} eq = rewrite eq in DivZero
divides {a} {b} {x=S k} eq = rewrite eq in
  let prf : (minus b a = mult k a) = 
  trans (cong {f=(flip minus) a} eq) $ plusMinusLeftInverse a (mult k a) in
  rewrite sym prf in
  DivAdd $ divides prf

---------------------------------------------------------------------
-- Properties of Divisibility
---------------------------------------------------------------------
||| Every number divides itself.
divRefl : (n:Nat) -> n `Div` n
divRefl n = divides {x=1} $ sym $ multOneLeftNeutral n

||| A divisor of two numbers is a divisor of their sum.
divAdditive : x `Div` a -> x `Div` b -> x `Div` (a + b)
divAdditive DivZero right = right
divAdditive {x} {b} (DivAdd {b=b1} left) right = 
  rewrite sym $ plusAssociative x b1 b in
    DivAdd $ divAdditive left right

divSubtractive : a `Div` (b + c) -> a `Div` b -> a `Div` c
divSubtractive {a} {b} {c} left right =
case factors left of 
  (x ** eq) => 
  let ex1:((b + c) - b = x*a - b) = cong {f = (flip minus) b} eq in
  let ex2:(c = (b + c) - b) = sym $ plusMinusLeftInverse b c in
  let ex3:(c = x*a - b) = trans ex2 ex1 in
  case factors right of 
    (y ** eq2) => 
    let ex4:(c = x*a - y*a) = (rewrite sym eq2 in ex3) in 
    let ex5:(c = (x-y)*a) = trans ex4 (sym (multDistributesOverMinusLeft x y a)) in
    divides ex5


divMultiplicative : (c:Nat) -> a `Div` b -> a `Div` c * b
divMultiplicative Z _ = DivZero
divMultiplicative (S k) div = divAdditive div $ divMultiplicative k div

divTrans : a `Div` b -> b `Div` c -> a `Div` c
divTrans _ DivZero = DivZero
divTrans left (DivAdd right) = divAdditive left $ divTrans left right

divAntisym : a `Div` b -> b `Div` a -> a = b
divAntisym DivZero DivZero = Refl
divAntisym {a} (DivAdd {b=Z} _) _ = sym $ plusZeroRightNeutral a
divAntisym {b} _ (DivAdd {b=Z} _) = plusZeroRightNeutral b

zeroLeastDivisor : (b `LT` a) -> (a `Div` b) -> (b = 0)
zeroLeastDivisor lt  DivZero = Refl
zeroLeastDivisor {a} lt (DivAdd {b} _) = void $ plusNonDecreasing b a lt


-------------------------------------------------------------------
-- Decidability of Divisibility
-------------------------------------------------------------------

check_div : (a : Nat) -> (b : Nat) -> Maybe (a `Div` b)
check_div _ Z = Just DivZero 
check_div a b = case isLTE (S b) a of 
  Yes prf => Nothing
  No notlt =>
  let (x ** eq) = lteSum (notLTthenGTE notlt) in ?bar
  
--  check_div a x

{-
||| Decision procedure for divisibility.
||| @ left the smaller number.
||| @ right the larger number.
-- TODO: pass the totality checker (currently fails due to non-primitive recursion)
isDiv : (left,right:Nat) -> Dec (left `Div` right)
isDiv _ Z = Yes DivZero
isDiv left (S right) = case isLTE (S (S right)) left of
  (Yes lt) => No $ \div => ZnotS . sym $ zeroLeastDivisor lt div
  (No notlt) => let (x ** eq) = lteSum $ notLTthenGTE notlt in
    case assert_total $ isDiv left x of
      (Yes div) => Yes $ rewrite eq in DivAdd $ div
      (No nodiv) => No $ \prf => 
        nodiv $ divSubtractive (rewrite sym eq in prf) (divRefl left)
-}

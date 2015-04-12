module Division

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
divides {x=Z} (eq) = rewrite eq in DivZero
divides {a} {b} {x=S k} (eq) = rewrite eq in
  let prf : (minus b a = mult k a) = 
  trans (cong {f=(flip minus) a} eq) $ plusMinusLeftInverse a (mult k a) in
  rewrite sym prf in 
  DivAdd $ divides prf

---------------------------------------------------------------------
-- Properties of Divisibility
---------------------------------------------------------------------
||| Every number divides itself.
divReflexive : (n:Nat) -> n `Div` n
divReflexive n = divides {x=1} $ sym $ multOneLeftNeutral n

||| A divisor of two numbers is a divisor of their sum.
divadds : x `Div` a -> x `Div` b -> x `Div` (a + b)
divadds DivZero right = right
divadds {x} {b} (DivAdd {b=b1} left) right = 
  rewrite sym $ plusAssociative x b1 b in
    DivAdd $ divadds left right

divsubs : a `Div` (b + c) -> a `Div` b -> a `Div` c
divsubs {a} {b} {c} left right =
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


prop : (b `LT` a) -> (a `Div` b) -> (b = 0)
prop lt  DivZero = Refl
prop {a} lt (DivAdd {b} _) = void $ plusNonDecreasing b a lt


-------------------------------------------------------------------
-- Decidability of Divisibility
-------------------------------------------------------------------
||| Decision procedure for divisibility.
||| @ left the smaller number.
||| @ right the larger number.
-- TODO: pass the totality checker (currently fails due to cases block)
partial isDiv : (left:Nat) -> (right:Nat) -> Dec (left `Div` right)
isDiv left right = case (isLTE (S right) left) of
  Yes ltprf => case (decEq right Z) of
    Yes eq => Yes $ rewrite eq in DivZero
    No neq => No $ \div => neq $ prop ltprf div
  No gteprf => case (isDiv left (minus right left)) of
    Yes divprf => Yes $ rewrite sym $ plusMinusRightInverse $ notLTthenGTE gteprf in DivAdd $ divprf
    No ndivprf => 
    let beqplusminus = plusMinusRightInverse $ notLTthenGTE gteprf in
    No $ \x : (left `Div` right) => 
      let blah : (left `Div` left + (right - left)) = rewrite beqplusminus in x in
      ndivprf $ divsubs blah $ divReflexive left



{-
--prop : (expr:DivExpr) -> (n `Sat` expr) -> (x ** (x `Sat` expr, LTE x (exprLcm expr)))
--prop {n=Z} (Divisibility a) (SDivides DivZero) = (Z ** (SDivides DivZero, LTEZero))
-}

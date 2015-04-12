module Division

%default total

||| Proofs of divisibility in the natural numbers.
||| @ a the smaller number
||| @ b the larger number
data Div : (a:Nat) -> (b:Nat) -> Type where
  DivZero : n `Div` 0
  DivAdd : a `Div` b -> a `Div` (a + b)
  

||| Factorization distributes over division.
divadds : x `Div` a -> x `Div` b -> x `Div` (a + b)
divadds DivZero right = right
divadds {x} {b} (DivAdd {b=b1} left) right = 
  rewrite sym $ plusAssociative x b1 b in
    DivAdd $ divadds left right

||| Show that every divisor is a factor.
factors : a `Div` b -> (x ** b = x * a)
factors {a} DivZero = (Z ** Refl)
factors {a} (DivAdd {b} prf) = case factors prf of
  (x ** eq) => (S x ** cong eq)
  
minusPlusId : (left:Nat) -> (right:Nat) -> minus (plus left right) left = right
minusPlusId Z right = rewrite minusZeroRight right in Refl
minusPlusId (S left) right = minusPlusId left right

||| Show that every factor is a divisor.
divides : (b = x * a) -> a `Div` b
divides {x=Z} (eq) = rewrite eq in DivZero
divides {a} {b} {x=S k} (eq) = rewrite eq in
  let prf : (minus b a = mult k a) = 
  trans (cong {f=(flip minus) a} eq) $ minusPlusId a (mult k a) in
  rewrite sym prf in 
  DivAdd $ divides prf

divReflexive : (n:Nat) -> n `Div` n
divReflexive n = divides {x=1} $ sym $ multOneLeftNeutral n
  

divsubs : a `Div` (b + c) -> a `Div` b -> a `Div` c
divsubs {a} {b} {c} left right =
case factors left of 
  (x ** eq) => 
  let ex1:((b + c) - b = x*a - b) = cong {f = (flip minus) b} eq in
  let ex2:(c = (b + c) - b) = sym $ minusPlusId b c in
  let ex3:(c = x*a - b) = trans ex2 ex1 in
  case factors right of 
    (y ** eq2) => 
    let ex4:(c = x*a - y*a) = (rewrite sym eq2 in ex3) in 
    let ex5:(c = (x-y)*a) = trans ex4 (sym (multDistributesOverMinusLeft x y a)) in
    divides ex5


plusNonDecreasing : (left:Nat) -> (right:Nat) -> Not ((right + left) `LT` right)
plusNonDecreasing left Z = succNotLTEzero
plusNonDecreasing left (S right) = (plusNonDecreasing left right) . fromLteSucc


prop : (b `LT` a) -> (a `Div` b) -> (b = 0)
prop lt  DivZero = Refl
prop {a} lt (DivAdd {b} _) = void $ plusNonDecreasing b a lt

prop2 : (a `LTE` b) -> a + (b - a) = b
prop2 {b} LTEZero = rewrite minusZeroRight b in Refl
prop2 (LTESucc gte) = cong $ prop2 gte

prop3 : Not (a `LT` b) -> b `LTE` a
prop3 {a} {b=Z} contra = LTEZero
prop3 {a=Z} {b=S k} contra = void $ contra $ LTESucc LTEZero
prop3 {a=S n} {b=S k} contra = LTESucc $ prop3 $ contra . LTESucc


||| Decision procedure for divisibility.
-- TODO: pass the totality checker
partial isDiv : (left:Nat) -> (right:Nat) -> Dec (left `Div` right)
isDiv left right = case (isLTE (S right) left) of
  Yes ltprf => case (decEq right Z) of
    Yes eq => Yes $ rewrite eq in DivZero
    No neq => No $ \div => neq $ prop ltprf div
  No gteprf => case (isDiv left (minus right left)) of
    Yes divprf => Yes $ rewrite sym $ prop2 $ prop3 gteprf in DivAdd $ divprf
    No ndivprf => 
    let beqplusminus = prop2 $ prop3 gteprf in
    No $ \x : (left `Div` right) => 
      let blah : (left `Div` left + (right - left)) = rewrite beqplusminus in x in
      ndivprf $ divsubs blah $ divReflexive left

{-
||| Divisibility propositions in a single variable in negative normal form.
data DivExpr : Type where
  Divisibility : Nat -> DivExpr
  NotDivisibility : Nat -> DivExpr
  And : DivExpr -> DivExpr -> DivExpr
  Or : DivExpr -> DivExpr -> DivExpr

      

data Sat : Nat -> DivExpr -> Type where
  SDivides : a `Div` x -> x `Sat` (Divisibility a)
  SNotDivides : Not (a `Div` x) -> x `Sat` (NotDivisibility a)
  SAnd : x `Sat` left -> x `Sat` right -> x `Sat` (And left right)
  HOr : Either (x `Sat` left) (x `Sat` right) -> x `Sat` (Or left right)
  

exprLcm : DivExpr -> Nat
exprLcm (Divisibility n) = n
exprLcm (NotDivisibility n) = n
exprLcm (And left right) = lcm (exprLcm left) (exprLcm right)
exprLcm (Or left right) = lcm (exprLcm left) (exprLcm right)

--prop : (expr:DivExpr) -> (n `Sat` expr) -> (x ** (x `Sat` expr, LTE x (exprLcm expr)))
--prop {n=Z} (Divisibility a) (SDivides DivZero) = (Z ** (SDivides DivZero, LTEZero))


partial prop : x `Div` (a + b) -> x `Div` a -> x `Div` b
prop DivZero DivZero = DivZero
prop adivab DivZero = adivab
--prop (DivAdd prf) xdiva with 
--  ... | ... =DivAdd $ prop prf xdiva


data Div2 : Nat -> Nat -> Type where
  DivE : (x ** b = x * a) -> Div2 a b

partial div2divE : Div a b -> Div2 a b
div2divE DivZero = DivE (Z ** Refl)
--div2divE {a} (DivAdd prf) with (div2divE prf)
--  | DivE (x ** eq) = DivE (a + x ** eq)
  


  


{--
divsubs : x `Div` (a + b) -> x `Div` a -> x `Div` b
divsubs DivZero DivZero = DivZero
divsubs (DivAdd left) DivZero = DivAdd left
divsubs (DivAdd left) right = ?dontknowagain
--}

-}

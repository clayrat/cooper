module Division

%default total

||| Divisibility propositions in a single variable in negative normal form.
data DivExpr : Type where
  Divisibility : Nat -> DivExpr
  NotDivisibility : Nat -> DivExpr
  And : DivExpr -> DivExpr -> DivExpr
  Or : DivExpr -> DivExpr -> DivExpr

      
data Div : Nat -> Nat -> Type where
  DivZero : n `Div` 0
  DivAdd : a `Div` b -> a `Div` (a + b)

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
  


partial divadds : x `Div` a -> x `Div` b -> x `Div` (a + b)
divadds DivZero right = right
--divadds {a} left DivZero = rewrite plusZeroRightNeutral a in left
divadds {x} {b} (DivAdd left) right = 
  DivAdd $ divadds left right
  


{--
divsubs : x `Div` (a + b) -> x `Div` a -> x `Div` b
divsubs DivZero DivZero = DivZero
divsubs (DivAdd left) DivZero = DivAdd left
divsubs (DivAdd left) right = ?dontknowagain
--}


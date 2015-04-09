
%default total

data Div : Nat -> Nat -> Type where
  DivZero : (n:Nat) -> n `Div` Z
  DivAdd : (a,b:Nat) -> a `Div` b -> a `Div` (a + b)
  

prop : x `Div` a -> x `Div` b -> x `Div` (a + b)
prop (DivZero x) right = right
prop (DivAdd x _ left) right = DivAdd x _ $ prop left right

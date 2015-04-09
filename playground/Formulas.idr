----------------------------------

data Formula : (n:Nat) -> Type where
  True : Formula n
  False : Formula n
  Single : Expr n -> Formula n
  Not : Formula n -> Formula n
  Forall : Fin n -> Expr n -> Formula n
  
  
data Formula : (q:Nat) -> (v:Nat) -> Type where
  Single : Expr n -> Formula Z n
  Forall : Formula k n -> Formula (S k) n
  And : Formula k n -> Formula k n -> Formula k n
  

Sentence : Type
Sentence = Formula k k
    
-- (Forall x P(x)) and (Exists x Q(x,y))

lift : Formula q v -> Formula (q + a) (v + a)

--Forall (Exists (... Var Z ... Var 1 ...)
--Exists (Forall (... Var 1 ... Var Z ...)


--forall x | exists y | ... x ... y ...
--exists x | forall y | ... y ... x ...

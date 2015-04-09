module Step1.Expr

import Data.ZZ
import Data.Fin
import Data.Vect

%default total


||| A Term in presburger arithmetic.
||| @ n the number of variables in the term.
%elim data Expr : (n : Nat) -> Type where
  Val   : ZZ     -> Expr n
  Var   : Fin n  -> Expr n
  Add   : Expr n -> Expr n -> Expr n
  Scale : ZZ     -> Expr n -> Expr n

inc : Expr n -> Expr n
inc x = Add x (Val 1)

||| Evaluate a term in an environment.
evalExpr : Vect n ZZ -> Expr n -> ZZ
evalExpr _  (Val v)     = v
evalExpr xs (Var x)     = index x xs
evalExpr xs (Add v u)   = evalExpr xs v + evalExpr xs u
evalExpr xs (Scale k v) = k * evalExpr xs v

||| Substitute a term for the first variable in a second term.
substExpr : Expr n -> Expr (S n) -> Expr n
substExpr _ (Val v)      = Val v
substExpr x (Var FZ)     = x
substExpr _ (Var (FS k)) = Var k
substExpr x (Add a b)    = Add (substExpr x a) (substExpr x b)
substExpr x (Scale k v)  = Scale k (substExpr x v)

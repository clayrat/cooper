
module Input

import NegationNormalForm
import Data.List

%default total

------------------------------------------------------
-- Data Definition
------------------------------------------------------
data InputTerm : Type where
  Con : Nat -> InputTerm
  Var : Iden -> InputTerm
  Add : InputTerm -> InputTerm -> InputTerm
  Scale : Nat -> InputTerm -> InputTerm
  
  

data Input : Type where
  Eq : InputTerm -> InputTerm -> Input
  Lte : InputTerm -> InputTerm -> Input
  
  Forall : Iden -> Input -> Input
  Exists : Iden -> Input -> Input
  
  And : Input -> Input -> Input
  Or  : Input -> Input -> Input
  Not : Input -> Input

data ValidInputTerm : List Iden -> InputTerm -> Type where
  VCon : (n:Nat) -> ValidInputTerm env (Con n)
  VVar : Elem x env -> ValidInputTerm env (Var x)
  VAdd : ValidInputTerm env x -> ValidInputTerm env y -> 
         ValidInputTerm env (Add x y)
  VScale : (n:Nat) -> ValidInputTerm env x -> ValidInputTerm env (Scale n x)

data ValidInput : List Iden -> Input -> Type where
  VEq : ValidInputTerm env x -> ValidInputTerm env y -> 
        ValidInput env (Eq x y)
  VLte : ValidInputTerm env x -> ValidInputTerm env y ->
         ValidInput env (Lte x y)
  VForall : (x:Iden) -> ValidInput (x::env) body -> 
            ValidInput env (Forall x body)
  VExists : (x:Iden) -> ValidInput (x::env) body ->
            ValidInput env (Exists x body)
  VAnd : ValidInput env x -> ValidInput env y -> ValidInput env (And x y)
  VOr  : ValidInput env x -> ValidInput env y -> ValidInput env (Or x y)
  VNot : ValidInput env x -> ValidInput env (Not x)          
  
denoteInputTerm : (env:Env) -> ValidInputTerm (map fst env) term -> Nat
denoteInputTerm env (VCon n) = n
denoteInputTerm env (VAdd x y) = (denoteInputTerm env x) + 
                                 (denoteInputTerm env y)
denoteInputTerm env (VVar x) = lookup env x
denoteInputTerm env (VScale n x) = n * (denoteInputTerm env x)

denoteInput : (env:Env) -> ValidInput (map fst env) formula -> Type
denoteInput env (VEq x y) = 
  (denoteInputTerm env x) = (denoteInputTerm env y)
denoteInput env (VLte x y) = 
  (denoteInputTerm env x) `LTE` (denoteInputTerm env y)
denoteInput env (VForall x body) =
  (v:Nat) -> denoteInput ((x,v)::env) body


{- Rough outline of future functions
translate : (ValidInput [] formula) -> (ValidNNF [] formula)

if : (ValidInput [] formula) -> (denoteInput formula) -> (denoteNNF (translate formula))
onlyif : (VAlidInput [] formula) -> (denoteNNF (translate formula)) -> (denoteInput formula)

decideInput : ValidInput [] formula -> Dec (denoteInput formula)
decideInput formula = case (decideNNF (translate formula)) of
  Yes prf => Yes $ onlyif prf
  No contra => No $ if contra
  
-}

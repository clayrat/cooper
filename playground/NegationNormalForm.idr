module NegationNormalForm.idr

import QuantifierFree
import Data.List

%default total

-------------------------------------------------------------------
-- Data Definition
-------------------------------------------------------------------
-- Variable identifiers
Iden : Type
Iden = String

-- terms indexed by the type of variables
data Term : Type where
  Var : Iden -> Term
  Con : Nat -> Term
  Add : Term -> Term -> Term

data Formula : Type where
  Lt  : Term -> Term -> Formula
--  Div : Term -> Term -> Formula
  And : Formula -> Formula -> Formula
  Or  : Formula -> Formula -> Formula
  
  Exists  : Iden -> Formula -> Formula
  NExists : Iden -> Formula -> Formula

-- term is valid in the environment
data ValidTerm : List Iden -> Term -> Type where
  VCon : (n:Nat) -> ValidTerm env (Con n)
  VAdd : ValidTerm env x -> ValidTerm env y -> ValidTerm env (Add x y)
  VVar : Elem x env -> ValidTerm env (Var x)

-- formula is valid in the environment
data Valid : List Iden -> Formula -> Type where
  VLt : ValidTerm env x -> ValidTerm env y -> Valid env (Lt x y)
  VAnd : Valid env left -> Valid env right -> Valid env (And left right)
  VOr  : Valid env left -> Valid env right -> Valid env (Or left right)
  VExists  : (x:Iden) -> Valid (x::env) body -> Valid env (Exists x body)
  VNExists : (x:Iden) -> Valid (x::env) body -> Valid env (NExists x body)

-------------------------------------------------------------------
-- Reflection functions
-------------------------------------------------------------------
parse : Type -> Valid [] formula

Env : Type
Env = List (Iden, Nat)

lookup : (env:Env) -> Elem x (map fst env) -> Nat
lookup ((x,v)::xs) Here = v
lookup (_::xs) (There prf) = lookup xs prf

-- what does a valid term denote in an environment
denoteTerm : (env:Env) -> ValidTerm (map fst env) term -> Nat
denoteTerm env (VCon n) = n
denoteTerm env (VAdd left right) = (denoteTerm env left) + (denoteTerm env right)
denoteTerm env (VVar x) = lookup env x


-- what does a valid formula denote in an environment
denote : (env:Env) -> Valid (map fst env) formula -> Type
denote env (VLt left right) = (denoteTerm env left) `LT` (denoteTerm env right)
denote env (VAnd left right) = (denote env left, denote env right)
denote env (VOr left right) = Either (denote env left) (denote env right)
denote env (VExists x body) = Sigma Nat (\v => denote ((x,v)::env) body)
denote env (VNExists x body) = (Sigma Nat (\v => denote ((x,v)::env) body)) -> Void

-------------------------------------------------------------------
-- Decision Procedure
-------------------------------------------------------------------

decideNNF : (env:Env) -> (expr:Valid (map fst env) _) -> Dec (denote env expr)

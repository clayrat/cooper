module QuantifierFree

import Divisibility
import ReflectionTactic

%default total

-------------------------------------------------------------
-- Data Definition
-------------------------------------------------------------
data QFree : Type where
  QFDiv : Nat -> Nat -> QFree
  QFLT  : Nat -> Nat -> QFree
  QFAnd : QFree -> QFree -> QFree
  QFOr  : QFree -> QFree -> QFree
  QFNot : QFree -> QFree

-------------------------------------------------------------
-- Reflection functions
-------------------------------------------------------------
%reflection
parseQF : Type -> QFree
parseQF (a `Div` b) = QFDiv a b
parseQF (a `LT` b) = QFLT a b
parseQF (left, right) = QFAnd (parseQF left) (parseQF right)
parseQF (Either left right) = QFOr (parseQF left) (parseQF right)
-- TODO 'Void' is interpreted here as a variable, it should be 'Builtins.Void'
-- except that Void is a builtin and so it has no prefix
-- e.g. 'parseQF (a -> Unit)' evaluates to 'QFNot (parseQF a)'
parseQF (a -> Void) = QFNot (parseQF a)

denoteQF : QFree -> Type
denoteQF (QFDiv a b) = a `Div` b
denoteQF (QFLT a b) = a `LT` b
denoteQF (QFAnd left right) = (denoteQF left, denoteQF right)
denoteQF (QFOr left right) = Either (denoteQF left) (denoteQF right)
denoteQF (QFNot prop) = (denoteQF prop) -> Void

-- check that we wrote sensible functions
denoteParseLeftInverse : (p:QFree) -> (parseQF (denoteQF p)) = p
denoteParseLeftInverse (QFDiv a b) = Refl
denoteParseLeftInverse (QFLT a b) = Refl
denoteParseLeftInverse (QFAnd left right) = 
  rewrite denoteParseLeftInverse left in 
  rewrite denoteParseLeftInverse right in Refl
denoteParseLeftInverse (QFOr left right) =
  rewrite denoteParseLeftInverse left in 
  rewrite denoteParseLeftInverse right in Refl
denoteParseLeftInverse (QFNot left) = 
  rewrite denoteParseLeftInverse left in Refl

---------------------------------------------------------------
-- Decision Procedure
---------------------------------------------------------------
decideQF : (p:QFree) -> Dec (denoteQF p)
decideQF (QFDiv a b) = decideDiv a b
decideQF (QFLT a b) = isLTE (S a) b
decideQF (QFAnd left right) = case (decideQF left, decideQF right) of
  (Yes prfLeft, Yes prfRight) => Yes (prfLeft, prfRight)
  (No contra, _) => No $ contra . fst
  (_, No contra) => No $ contra . snd
decideQF (QFOr left right) = case (decideQF left, decideQF right) of
  (Yes prf, _) => Yes $ Left prf
  (_, Yes prf) => Yes $ Right prf
  (No contraLeft, No contraRight) => No $ either contraLeft contraRight
decideQF (QFNot prop) = case (decideQF prop) of
  Yes prf => No $ \contra => void $ contra prf
  No contra => Yes contra


----------------------------------------------------------------
-- Reflection Tactic
----------------------------------------------------------------
syntax solveQF = reflectionTactic parseQF decideQF

test : Either (1 `Div` (2 + 3)) (5 `LT` 4, 0 `Div` 0)
test = solveQF

test2 : (2 `Div` 3) -> Void
test2 = solveQF

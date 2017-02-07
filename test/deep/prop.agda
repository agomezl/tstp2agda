
-- tstp2agda proof

module prop where

open import Data.FOL.Deep 1

-- Vars
a : Prop
a = Var (# 0)

-- Axioms
-- Axioms
lm : Prop
lm = a
-- Premises

-- Premises
Γ : Ctxt
Γ = ∅ , lm
-- Conjecture

-- Conjecture
goal : Prop
goal = a

-- Proof

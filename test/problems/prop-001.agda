
-- tstp2agda proof

open import Data.FOL.Deep 1

-- Vars
a : Prop
a = Var (# 0)

-- Axioms
lm : Prop
lm = a

-- Premises
Γ : Ctxt
Γ = ∅ , lm

-- Conjecture
goal : Prop
goal = a

-- Proof

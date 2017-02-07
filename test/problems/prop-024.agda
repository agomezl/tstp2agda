
-- tstp2agda proof

open import Data.FOL.Deep 2

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)


-- Conjecture
goal : Prop
goal = p ↔ q ↔ q ∨ ¬ p ∧ ¬ q ∨ p

-- Proof

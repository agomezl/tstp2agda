
-- tstp2agda proof

open import Data.FOL.Deep 3

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)


-- Conjecture
goal : Prop
goal = ((p → r) ∧ (¬ p → ¬ q) ∧ p ∨ q ⇒ p ∧ r)

-- Proof

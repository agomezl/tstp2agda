
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
goal = ((q → r) ∧ (r → p ∧ q) ∧ (p → q ∧ r) ⇒ p ↔ q)

-- Proof
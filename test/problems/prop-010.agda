
-- tstp2agda proof

open import Data.FOL.Deep 4

-- Vars
a : Prop
a = Var (# 0)

g : Prop
g = Var (# 1)

k : Prop
k = Var (# 2)

q : Prop
q = Var (# 3)


-- Conjecture
goal : Prop
goal = ((a ∨ ¬ k → g) ∧ (g → q) ∧ ¬ q ⇒ k)

-- Proof

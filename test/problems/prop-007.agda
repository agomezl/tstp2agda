
-- tstp2agda proof

open import Data.FOL.Deep 3

-- Vars
x : Prop
x = Var (# 0)

y : Prop
y = Var (# 1)

z : Prop
z = Var (# 2)


-- Conjecture
goal : Prop
goal = ((x → y) ⇒ (¬ y ∨ z → ¬ x ∨ z))

-- Proof


-- tstp2agda proof

open import Data.FOL.Deep 3

-- Vars
s : Prop
s = Var (# 0)

x : Prop
x = Var (# 1)

y : Prop
y = Var (# 2)


-- Conjecture
goal : Prop
goal = ((s → x) ∧ (s → (x → y)) ⇒ (s → y))

-- Proof

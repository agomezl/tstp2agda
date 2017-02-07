
-- tstp2agda proof

open import Data.FOL.Deep 2

-- Vars
x : Prop
x = Var (# 0)

y : Prop
y = Var (# 1)


-- Conjecture
goal : Prop
goal = (x ⇒ (y → x))

-- Proof

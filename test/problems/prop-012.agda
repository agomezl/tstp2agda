
-- tstp2agda proof

open import Data.FOL.Deep 1

-- Vars
p : Prop
p = Var (# 0)


-- Conjecture
goal : Prop
goal = ¬ ¬ p ↔ p

-- Proof

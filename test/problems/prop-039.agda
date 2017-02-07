
-- tstp2agda proof

open import Data.FOL.Deep 2

-- Vars
clause : Prop
clause = Var (# 0)

lit : Prop
lit = Var (# 1)


-- Conjecture
goal : Prop
goal = ((lit → clause) ⇒ lit ∨ clause ↔ clause)

-- Proof


-- tstp2agda proof

open import Data.FOL.Deep 4

-- Vars
a : Prop
a = Var (# 0)

b : Prop
b = Var (# 1)

c : Prop
c = Var (# 2)

d : Prop
d = Var (# 3)

-- Axioms
a1 : Prop
a1 = a

a2 : Prop
a2 = b

a3 : Prop
a3 = ¬ a ∨ ¬ b ∨ c

a4 : Prop
a4 = ¬ c ∨ d

-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2 , a3 , a4

-- Conjecture
a5 : Prop
a5 = d ∧ a ∧ b ∧ c

-- Proof

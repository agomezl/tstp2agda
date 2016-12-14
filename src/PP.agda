
-- tstp2agda proof

open import Data.FOL.Deep 3

-- Vars
a : Prop
a = Var (# 0)

b : Prop
b = Var (# 1)

z : Prop
z = Var (# 2)

-- Axioms
a1 : Prop
a1 = a

a2 : Prop
a2 = b

a3 : Prop
a3 = positive (a ∧ b ⇒ z)

-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2 , a3

-- Conjecture
a4 : Prop
a4 = z

-- Proof

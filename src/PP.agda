
-- tstp2agda proof

-- number of atoms.
n = 5

-- deep embedding.
open import Data.FOL.Deep n

-- ATP of the proof.
open import Data.FOL.Deep.ATP.Metis n

-- Variables.
a : Prop
a = Var (# 0)

b : Prop
b = Var (# 1)

c : Prop
c  = Var (# 2)

d : Prop
d = Var (# 3)

z : Prop
z = Var (# 4)

-- Axioms.
a1 : Prop
a1 = a

a2 : Prop
a2 = b

a3 : Prop
a3 = (a ∧ b ⇒ z)

-- Premises.
Γ : Ctxt
Γ = ∅ , a1 , a2 , a3

-- Conjecture
a4 : Prop
a4 = z

res : Prop
res = clausify (a ∨ (b ∧ (c ∨ d)))

-- Proof

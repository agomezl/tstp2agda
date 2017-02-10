
-- tstp2agda proof

open import Data.FOL.Deep 3
open import Data.FOL.Deep.ATP.Metis3

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
a3 = ((a ∧ b) ⇒ z)

-- Premises
Γ : Ctxt
Γ = ∅ , a1 , a2 , a3

-- Subgoal
subgoal-0 : Prop
subgoal-0 = z

-- Conjecture
a4 : Prop
a4 = z

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet


-- tstp2agda proof

open import Data.FOL.Deep 3

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoal
subgoal-0 : Prop
subgoal-0 = (((((p ∨ q) ⇒ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)

-- Conjecture
goal : Prop
goal = (((p ∨ q) ⇒ (p ∨ r)) ⇒ (p ∨ (q ⇒ r)))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet

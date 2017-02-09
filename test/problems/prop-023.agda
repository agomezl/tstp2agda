
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

-- Subgoals
subgoal-0 : Prop
subgoal-0 = (((p ∨ (q ∧ r)) ∧ ¬ p) ⇒ q)

subgoal-1 : Prop
subgoal-1 = ((((p ∨ (q ∧ r)) ∧ (p ∨ q)) ∧ ¬ p) ⇒ r)

subgoal-2 : Prop
subgoal-2 = ((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ⇒ q)

subgoal-3 : Prop
subgoal-3 = (((((p ∨ q) ∧ (p ∨ r)) ∧ ¬ p) ∧ q) ⇒ r)

-- Conjecture
goal : Prop
goal = ((p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r)))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet

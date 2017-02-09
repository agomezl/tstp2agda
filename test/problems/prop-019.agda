
-- tstp2agda proof

open import Data.FOL.Deep 2

-- Vars
p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoals
subgoal-0 : Prop
subgoal-0 = ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ q)

subgoal-1 : Prop
subgoal-1 = (((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ∧ ¬ ¬ q) ⇒ q)

-- Conjecture
goal : Prop
goal = ((((p ∨ q) ∧ (¬ p ∨ q)) ∧ (p ∨ ¬ q)) ⇒ ¬ (¬ q ∨ ¬ q))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet

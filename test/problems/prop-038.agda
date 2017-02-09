
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
subgoal-0 = ((¬ (p ⇔ q) ∧ p) ⇒ ¬ q)

subgoal-1 : Prop
subgoal-1 = (((¬ (p ⇔ q) ∧ (p ⇒ ¬ q)) ∧ q) ⇒ ¬ p)

subgoal-2 : Prop
subgoal-2 = ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ p) ⇒ ¬ q)

subgoal-3 : Prop
subgoal-3 = ((((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)) ∧ q) ⇒ ¬ p)

-- Conjecture
goal : Prop
goal = (¬ (p ⇔ q) ⇔ ((p ⇒ ¬ q) ∧ (q ⇒ ¬ p)))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet


-- tstp2agda proof

open import Data.FOL.Deep 3
open import Data.FOL.Deep.ATP.Metis3

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
subgoal-0 = (((¬ (¬ (p ⇔ q) ⇔ r) ∧ p) ∧ q) ⇒ r)

subgoal-1 : Prop
subgoal-1 = (((¬ (¬ (p ⇔ q) ⇔ r) ∧ p) ∧ r) ⇒ q)

subgoal-2 : Prop
subgoal-2 = ((¬ (¬ (p ⇔ q) ⇔ r) ∧ ¬ (q ⇔ r)) ⇒ ¬ p)

subgoal-3 : Prop
subgoal-3 = ((¬ (p ⇔ ¬ (q ⇔ r)) ∧ ¬ (p ⇔ q)) ⇒ ¬ r)

subgoal-4 : Prop
subgoal-4 = (((¬ (p ⇔ ¬ (q ⇔ r)) ∧ r) ∧ p) ⇒ q)

subgoal-5 : Prop
subgoal-5 = (((¬ (p ⇔ ¬ (q ⇔ r)) ∧ r) ∧ q) ⇒ p)

-- Conjecture
goal : Prop
goal = (¬ (¬ (p ⇔ q) ⇔ r) ⇔ ¬ (p ⇔ ¬ (q ⇔ r)))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet

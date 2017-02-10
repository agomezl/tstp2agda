
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
subgoal-0 = ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ p)

subgoal-1 : Prop
subgoal-1 = (((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ∧ p) ⇒ r)

-- Conjecture
goal : Prop
goal = ((((p ⇒ r) ∧ (¬ p ⇒ ¬ q)) ∧ (p ∨ q)) ⇒ (p ∧ r))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet

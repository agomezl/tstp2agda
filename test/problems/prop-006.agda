
-- tstp2agda proof

open import Data.FOL.Deep 3

-- Vars
x : Prop
x = Var (# 0)

y : Prop
y = Var (# 1)

z : Prop
z = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoals
subgoal-0 : Prop
subgoal-0 = (((x ∧ (y ∨ z)) ∧ ¬ (x ∧ y)) ⇒ x)

subgoal-1 : Prop
subgoal-1 = ((((x ∧ (y ∨ z)) ∧ ¬ (x ∧ y)) ∧ x) ⇒ z)

-- Conjecture
goal : Prop
goal = ((x ∧ (y ∨ z)) ⇒ ((x ∧ y) ∨ (x ∧ z)))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet

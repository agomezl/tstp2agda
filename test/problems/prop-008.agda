
-- tstp2agda proof

open import Data.FOL.Deep 3

-- Vars
s : Prop
s = Var (# 0)

x : Prop
x = Var (# 1)

y : Prop
y = Var (# 2)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoal
subgoal-0 : Prop
subgoal-0 = ((((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ∧ s) ⇒ y)

-- Conjecture
goal : Prop
goal = (((s ⇒ x) ∧ (s ⇒ (x ⇒ y))) ⇒ (s ⇒ y))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
    atp-canonicalize $
      inference rule no supported yet $
-- no supported yet

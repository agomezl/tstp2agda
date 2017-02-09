
-- tstp2agda proof

open import Data.FOL.Deep 1

-- Vars
p : Prop
p = Var (# 0)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoals
subgoal-0 : Prop
subgoal-0 = (¬ ¬ p ⇒ p)

subgoal-1 : Prop
subgoal-1 = (p ⇒ p)

-- Conjecture
goal : Prop
goal = (¬ ¬ p ⇔ p)

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet

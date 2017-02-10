
-- tstp2agda proof

open import Data.FOL.Deep 2
open import Data.FOL.Deep.ATP.Metis2

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
subgoal-0 = (((¬ p ⇒ q) ∧ ¬ q) ⇒ p)

subgoal-1 : Prop
subgoal-1 = (((¬ q ⇒ p) ∧ ¬ p) ⇒ q)

-- Conjecture
goal : Prop
goal = ((¬ p ⇒ q) ⇔ (¬ q ⇒ p))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet

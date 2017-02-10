
-- tstp2agda proof

open import Data.FOL.Deep 2
open import Data.FOL.Deep.ATP.Metis2

-- Vars
clause : Prop
clause = Var (# 0)

lit : Prop
lit = Var (# 1)

-- Premise
Γ : Ctxt
Γ = ∅

-- Subgoals
subgoal-0 : Prop
subgoal-0 = (((lit ⇒ clause) ∧ (lit ∨ clause)) ⇒ clause)

subgoal-1 : Prop
subgoal-1 = ((((lit ⇒ clause) ∧ clause) ∧ ¬ lit) ⇒ clause)

-- Conjecture
goal : Prop
goal = ((lit ⇒ clause) ⇒ ((lit ∨ clause) ⇔ clause))

-- Proof
proof : Γ ⊢ goal
proof =
  RAA {Γ = Γ , ¬ goal} $
-- no supported yet
